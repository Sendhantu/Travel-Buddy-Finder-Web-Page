from flask import (Flask,render_template,request,redirect,url_for,session,abort,jsonify,Response,send_file,flash)
import pymysql
import os
from functools import wraps
from flask_socketio import SocketIO, emit, join_room, leave_room
from datetime import datetime, timedelta
from werkzeug.security import generate_password_hash, check_password_hash
from werkzeug.utils import secure_filename
from email.message import EmailMessage
import secrets
import threading
import time
import math
import re
import uuid
import json
import csv
import io
import mimetypes
import subprocess
import shutil
import smtplib
from collections import defaultdict

try:
    import redis as redis_module
except Exception:
    redis_module = None

MAX_ATTEMPTS = 5
LOCKOUT_SECONDS = 60
CHAT_PAGE_SIZE = 50
CHAT_RATE_LIMIT_SECONDS = 0.35
CHAT_DUPLICATE_WINDOW_SECONDS = 10
CHAT_SPAM_WINDOW_SECONDS = 30
CHAT_SPAM_MAX_MESSAGES = 12
CHAT_REDIS_WINDOW_SECONDS = 15
CHAT_REDIS_MAX_MESSAGES = 20
CHAT_REDIS_BURST_WINDOW_SECONDS = 6
CHAT_REDIS_BURST_MAX_MESSAGES = 10
CHAT_IP_WINDOW_SECONDS = 20
CHAT_IP_MAX_MESSAGES = 40
CSRF_SESSION_KEY = "_csrf_token"
PASSWORD_POLICY_MIN_LENGTH = 8
PASSWORD_POLICY_RE = re.compile(r"^(?=.*[A-Za-z])(?=.*\d).+$")
MAX_ATTACHMENT_SIZE = 8 * 1024 * 1024
CHAT_UPLOAD_ROOT = os.path.join("uploads", "chat")
ALLOWED_ATTACHMENT_EXTENSIONS = {
    ".jpg", ".jpeg", ".png", ".gif", ".webp", ".pdf", ".txt", ".csv", ".doc", ".docx"
}
SUPPORT_EMAIL_SENDER = os.environ.get("SUPPORT_EMAIL_SENDER", "")
SUPPORT_EMAIL_ENABLED = os.environ.get("SUPPORT_EMAIL_ENABLED", "0").strip() == "1"
NOTIFICATION_EMAIL_ENABLED = os.environ.get("NOTIFICATION_EMAIL_ENABLED", "1").strip() == "1"
NOTIFICATION_SMS_ENABLED = os.environ.get("NOTIFICATION_SMS_ENABLED", "1").strip() == "1"
AUTO_EMAIL_FOR_ALL_NOTIFICATIONS = os.environ.get("AUTO_EMAIL_FOR_ALL_NOTIFICATIONS", "0").strip() == "1"
AUTO_SMS_FOR_ALL_NOTIFICATIONS = os.environ.get("AUTO_SMS_FOR_ALL_NOTIFICATIONS", "0").strip() == "1"
EMAIL_BACKEND = (os.environ.get("EMAIL_BACKEND") or "console").strip().lower()
EMAIL_FROM = (
    os.environ.get("EMAIL_FROM")
    or SUPPORT_EMAIL_SENDER
    or "no-reply@travelbuddy.local"
).strip()
SMTP_HOST = (os.environ.get("SMTP_HOST") or "").strip()
SMTP_PORT = (os.environ.get("SMTP_PORT") or "587").strip()
SMTP_USER = (os.environ.get("SMTP_USER") or "").strip()
SMTP_PASSWORD = os.environ.get("SMTP_PASSWORD") or ""
SMTP_USE_TLS = os.environ.get("SMTP_USE_TLS", "1").strip() == "1"
SMS_BACKEND = (os.environ.get("SMS_BACKEND") or "console").strip().lower()
REDIS_URL = os.environ.get("REDIS_URL", "").strip()
CHAT_RETENTION_DEFAULT_DAYS = 365
CHAT_RETENTION_RESTORE_DAYS = 14
CHAT_ALLOWED_REACTIONS = {"👍", "❤️", "😂", "🙏", "😮"}
CHAT_MAX_SEARCH_LIMIT = 100
DB_HOST = "localhost"
DB_USER = "root"
DB_NAME = "travelbuddyfinder"
DB_PASSWORD = "Sendhan@2005"
app = Flask(__name__)
SOCKETIO_ASYNC_MODE = (os.environ.get("SOCKETIO_ASYNC_MODE") or "threading").strip().lower() or "threading"
socketio = SocketIO(app, cors_allowed_origins="*", async_mode=SOCKETIO_ASYNC_MODE)

app.config["SECRET_KEY"] = os.environ.get("SECRET_KEY") or secrets.token_hex(32)

_IS_PRODUCTION = os.environ.get("FLASK_ENV", "development").lower() == "production"

app.config.update(
    SESSION_COOKIE_HTTPONLY=True,
    SESSION_COOKIE_SAMESITE="Lax",
    SESSION_COOKIE_SECURE=_IS_PRODUCTION
)

app.permanent_session_lifetime = timedelta(days=7)

_chat_schema_ready = False
_chat_schema_lock = threading.Lock()
_chat_throttle_lock = threading.Lock()
_chat_last_sent_at = {}
_redis_lock = threading.Lock()
_redis_client = None
_auth_schema_ready = False
_auth_schema_lock = threading.Lock()
_trip_core_schema_ready = False
_trip_core_schema_lock = threading.Lock()
_trip_feedback_schema_ready = False
_trip_feedback_schema_lock = threading.Lock()

class _CsrfTokenProxy:
    def __call__(self):
        return _get_csrf_token()

    def __str__(self):
        return _get_csrf_token()

    def __html__(self):
        return _get_csrf_token()

def _get_csrf_token():
    token = session.get(CSRF_SESSION_KEY)
    if not token:
        token = secrets.token_urlsafe(32)
        session[CSRF_SESSION_KEY] = token
    return token

@app.context_processor
def inject_csrf_token():
    return {"csrf_token": _CsrfTokenProxy()}

@app.context_processor
def inject_notification_badge():
    user_id = session.get("user_id")
    if not user_id:
        return {"unread_notifications": 0}
    try:
        db = get_db_connection()
        cur = db.cursor()
        cur.execute("""
            SELECT COUNT(*) AS unread
            FROM user_notifications
            WHERE user_id=%s
              AND is_read=0
        """, (user_id,))
        row = cur.fetchone() or {}
        unread = int(row.get("unread") or 0)
        cur.close()
        db.close()
        return {"unread_notifications": unread}
    except Exception:
        return {"unread_notifications": 0}

def _csrf_is_exempt_endpoint():
    endpoint = request.endpoint or ""
    if endpoint in {"home", "login", "register", "forgot_password", "reset_password"}:
        return True
    if endpoint.startswith("static"):
        return True
    return False

@app.before_request
def csrf_protect():
    if request.method not in ("POST", "PUT", "PATCH", "DELETE"):
        return
    if _csrf_is_exempt_endpoint():
        return
    if "user_id" not in session:
        return

    supplied = (
        request.form.get("csrf_token")
        or request.headers.get("X-CSRF-Token")
        or request.headers.get("X-CSRFToken")
    )
    if not supplied:
        abort(400, description="Missing CSRF token")

    expected = _get_csrf_token()
    if not secrets.compare_digest(str(supplied), str(expected)):
        abort(400, description="Invalid CSRF token")

def _dt_to_str(value):
    if isinstance(value, datetime):
        return value.strftime("%Y-%m-%d %H:%M:%S")
    return str(value) if value is not None else ""

def _parse_int(value):
    try:
        return int(value)
    except (TypeError, ValueError):
        return None

def _normalize_message(message):
    if not isinstance(message, str):
        return ""
    text = message.replace("\r\n", "\n").replace("\r", "\n")
    text = text.replace("\u200b", "").replace("\ufeff", "")
    text = re.sub(r"[ \t]{2,}", " ", text)
    return text.strip()

def _is_valid_message(message):
    text = _normalize_message(message)
    if not text:
        return False
    return len(text) <= 2000

def _is_duplicate_message(cur, table_name, channel_col, channel_id, sender_col, sender_id, message):
    cur.execute(f"""
        SELECT 1
        FROM {table_name}
        WHERE {channel_col} = %s
          AND {sender_col} = %s
          AND deleted_at IS NULL
          AND message = %s
          AND created_at >= (NOW() - INTERVAL {CHAT_DUPLICATE_WINDOW_SECONDS} SECOND)
        LIMIT 1
    """, (channel_id, sender_id, message))
    return bool(cur.fetchone())

def _spam_window_ok(cur, table_name, channel_col, channel_id, sender_col, sender_id):
    cur.execute(f"""
        SELECT COUNT(*) AS msg_count
        FROM {table_name}
        WHERE {channel_col} = %s
          AND {sender_col} = %s
          AND deleted_at IS NULL
          AND created_at >= (NOW() - INTERVAL {CHAT_SPAM_WINDOW_SECONDS} SECOND)
    """, (channel_id, sender_id))
    row = cur.fetchone() or {}
    return int(row.get("msg_count") or 0) < CHAT_SPAM_MAX_MESSAGES

def _throttle_ok(user_id, channel_key):
    now = time.monotonic()
    with _chat_throttle_lock:
        key = (int(user_id), channel_key)
        last = _chat_last_sent_at.get(key, 0.0)
        if now - last < CHAT_RATE_LIMIT_SECONDS:
            return False
        _chat_last_sent_at[key] = now
        if len(_chat_last_sent_at) > 2000:
            cutoff = now - 300
            stale = [k for k, ts in _chat_last_sent_at.items() if ts < cutoff]
            for k in stale:
                _chat_last_sent_at.pop(k, None)
    return True

def _get_redis_client():
    global _redis_client
    if _redis_client is not None:
        return _redis_client
    if not REDIS_URL or redis_module is None:
        return None
    with _redis_lock:
        if _redis_client is not None:
            return _redis_client
        try:
            client = redis_module.from_url(REDIS_URL, decode_responses=True)
            client.ping()
            _redis_client = client
        except Exception:
            _redis_client = None
    return _redis_client

def _redis_rate_ok_with_ip(user_id, channel_key, ip_addr=""):
    client = _get_redis_client()
    if client is None:
        return True
    safe_ip = (ip_addr or "").strip() or "unknown"
    user_key = f"tb:rl:user:{int(user_id)}:{channel_key}"
    burst_key = f"tb:rl:burst:{int(user_id)}:{channel_key}"
    ip_key = f"tb:rl:ip:{safe_ip}:{channel_key}"
    try:
        pipe = client.pipeline()
        pipe.incr(user_key, 1)
        pipe.expire(user_key, CHAT_REDIS_WINDOW_SECONDS, nx=True)
        pipe.incr(burst_key, 1)
        pipe.expire(burst_key, CHAT_REDIS_BURST_WINDOW_SECONDS, nx=True)
        pipe.incr(ip_key, 1)
        pipe.expire(ip_key, CHAT_IP_WINDOW_SECONDS, nx=True)
        user_count, _, burst_count, _, ip_count, _ = pipe.execute()
        if int(user_count or 0) > CHAT_REDIS_MAX_MESSAGES:
            return False
        if int(burst_count or 0) > CHAT_REDIS_BURST_MAX_MESSAGES:
            return False
        if int(ip_count or 0) > CHAT_IP_MAX_MESSAGES:
            return False
        return True
    except Exception:
        return True

def _ensure_upload_root():
    abs_root = os.path.join(app.root_path, CHAT_UPLOAD_ROOT)
    os.makedirs(abs_root, exist_ok=True)
    return abs_root

def _is_allowed_attachment(filename, mimetype):
    ext = os.path.splitext(filename or "")[1].lower()
    if ext not in ALLOWED_ATTACHMENT_EXTENSIONS:
        return False
    mt = (mimetype or "").lower()
    if not mt:
        guessed, _ = mimetypes.guess_type(filename or "")
        mt = (guessed or "").lower()
    if not mt:
        return False
    return (
        mt.startswith("image/")
        or mt in {"application/pdf", "text/plain", "text/csv", "application/msword",
                  "application/vnd.openxmlformats-officedocument.wordprocessingml.document"}
    )

def _scan_attachment(path):
    scanner = os.environ.get("CLAMSCAN_PATH", "").strip() or shutil.which("clamscan")
    if not scanner:
        return True, "scanner_unavailable"
    try:
        proc = subprocess.run(
            [scanner, "--no-summary", path],
            capture_output=True,
            text=True,
            timeout=12
        )
    except Exception:
        return True, "scan_skipped"
    if proc.returncode == 0:
        return True, "clean"
    if proc.returncode == 1:
        return False, "infected"
    return True, "scan_error"

def _write_admin_action(cur, admin_user_id, action_type, target_type, target_id=None, details=""):
    cur.execute("""
        INSERT INTO admin_action_logs
            (admin_user_id, action_type, target_type, target_id, details)
        VALUES (%s, %s, %s, %s, %s)
    """, (admin_user_id, action_type, target_type, target_id, details[:2000]))

def _resolve_notification_user_id(job_payload):
    if not isinstance(job_payload, dict):
        return None
    user_id = _parse_int(job_payload.get("user_id"))
    if user_id is None:
        user_id = _parse_int(job_payload.get("to_admin_id"))
    return user_id

def _load_user_notification_contact(user_id):
    ensure_auth_schema()
    db = get_db_connection()
    cur = db.cursor()
    try:
        cur.execute("""
            SELECT
                user_id,
                username,
                email,
                phone,
                notify_email,
                notify_sms,
                is_active
            FROM User_Details
            WHERE user_id=%s
            LIMIT 1
        """, (user_id,))
        return cur.fetchone() or {}
    finally:
        cur.close()
        db.close()

def _mark_notification_email_sent(notification_id):
    nid = _parse_int(notification_id)
    if nid is None:
        return
    db = get_db_connection()
    cur = db.cursor()
    try:
        cur.execute("""
            UPDATE user_notifications
            SET email_sent=1
            WHERE id=%s
        """, (nid,))
        db.commit()
    finally:
        cur.close()
        db.close()

def _send_email_console(recipient_email, subject, body):
    print(
        f"[DEV EMAIL] to={recipient_email} subject={subject} body={body[:400]}",
        flush=True
    )

def _send_email_smtp(recipient_email, subject, body):
    if not SMTP_HOST:
        raise RuntimeError("SMTP_HOST is required for SMTP email backend")
    try:
        smtp_port = int(SMTP_PORT)
    except Exception:
        smtp_port = 587

    msg = EmailMessage()
    msg["Subject"] = subject
    msg["From"] = EMAIL_FROM
    msg["To"] = recipient_email
    msg.set_content(body)

    with smtplib.SMTP(SMTP_HOST, smtp_port, timeout=20) as server:
        if SMTP_USE_TLS:
            server.starttls()
        if SMTP_USER:
            server.login(SMTP_USER, SMTP_PASSWORD)
        server.send_message(msg)

def _send_notification_email_stub(job_payload):
    if not NOTIFICATION_EMAIL_ENABLED:
        return True
    user_id = _resolve_notification_user_id(job_payload)
    if user_id is None:
        return True
    try:
        contact = _load_user_notification_contact(user_id)
        if not contact:
            return True
        if not int(contact.get("is_active") or 0):
            return True
        if not _parse_bool_flag(contact.get("notify_email"), True):
            return True

        recipient_email = (contact.get("email") or "").strip().lower()
        if not _looks_like_email(recipient_email):
            return True

        title = (job_payload.get("title") or "Travel Buddy Update").strip()
        message = (job_payload.get("message") or "").strip()
        if not message and job_payload.get("kind") == "support_opened":
            conv_id = _parse_int(job_payload.get("conversation_id"))
            priority = (job_payload.get("priority") or "normal").strip()
            message = f"Conversation #{conv_id or 0} was marked as support ({priority})."
        if not message:
            message = "You have a new update in your Travel Buddy account."

        recipient_name = (contact.get("username") or "traveler").strip() or "traveler"
        body = (
            f"Hi {recipient_name},\n\n"
            f"{message}\n\n"
            "Open Travel Buddy to see full details.\n\n"
            "This is an automated notification."
        )

        if EMAIL_BACKEND == "smtp":
            _send_email_smtp(recipient_email, title, body)
        else:
            _send_email_console(recipient_email, title, body)

        _mark_notification_email_sent(job_payload.get("notification_id"))
        return True
    except Exception:
        return False

def _send_notification_sms_stub(job_payload):
    if not NOTIFICATION_SMS_ENABLED:
        return True
    user_id = _resolve_notification_user_id(job_payload)
    if user_id is None:
        return True
    try:
        contact = _load_user_notification_contact(user_id)
        if not contact:
            return True
        if not int(contact.get("is_active") or 0):
            return True
        if not _parse_bool_flag(contact.get("notify_sms"), False):
            return True
        recipient_phone = _normalize_phone(contact.get("phone"))
        if not _is_valid_phone(recipient_phone):
            return True

        title = (job_payload.get("title") or "Travel Buddy").strip()
        message = (job_payload.get("message") or "").strip()
        if not message and job_payload.get("kind") == "support_opened":
            conv_id = _parse_int(job_payload.get("conversation_id"))
            priority = (job_payload.get("priority") or "normal").strip()
            message = f"Support update: conversation #{conv_id or 0} ({priority})."
        if not message:
            message = "You have a new update in Travel Buddy."
        sms_text = f"{title}: {message}"[:320]

        if SMS_BACKEND == "console":
            print(f"[DEV SMS] to={recipient_phone} text={sms_text}", flush=True)
            return True
        return False
    except Exception:
        return False

def _create_notification(cur, user_id, title, message, ntype="info", send_email=False, send_sms=False):
    email_requested = bool(send_email or AUTO_EMAIL_FOR_ALL_NOTIFICATIONS)
    sms_requested = bool(send_sms or AUTO_SMS_FOR_ALL_NOTIFICATIONS)
    cur.execute("""
        INSERT INTO user_notifications
            (user_id, title, message, type, send_email, is_read, created_at)
        VALUES (%s, %s, %s, %s, %s, 0, NOW())
    """, (user_id, title[:180], message[:1000], ntype[:30], 1 if email_requested else 0))
    notification_id = int(cur.lastrowid or 0)

    payload = {
        "notification_id": notification_id,
        "user_id": int(user_id),
        "title": title[:180],
        "message": message[:1000],
        "type": ntype[:30]
    }

    if email_requested:
        _enqueue_background_job(
            cur,
            "send_notification_email",
            payload,
            run_at=datetime.utcnow()
        )
    if sms_requested:
        _enqueue_background_job(
            cur,
            "send_notification_sms",
            payload,
            run_at=datetime.utcnow()
        )

def _enqueue_background_job(cur, job_type, payload, run_at=None):
    run_at = run_at or datetime.utcnow()
    if isinstance(payload, dict):
        payload = json.dumps(payload, ensure_ascii=True)
    cur.execute("""
        INSERT INTO background_jobs
            (job_type, payload, status, run_at, attempts, created_at, updated_at)
        VALUES (%s, %s, 'queued', %s, 0, NOW(), NOW())
    """, (job_type[:80], str(payload), run_at))

def _is_user_blocked(cur, user_id, other_user_id):
    cur.execute("""
        SELECT 1
        FROM user_blocks
        WHERE (
              (blocker_id=%s AND blocked_id=%s)
           OR (blocker_id=%s AND blocked_id=%s)
        )
          AND muted=0
        LIMIT 1
    """, (user_id, other_user_id, other_user_id, user_id))
    return bool(cur.fetchone())

def _touch_presence(cur, user_id, is_online=None, room_name=""):
    if is_online is None:
        cur.execute("""
            INSERT INTO user_presence (user_id, is_online, last_seen_at, last_socket_at, current_room)
            VALUES (%s, 1, NOW(), NOW(), %s)
            ON DUPLICATE KEY UPDATE
                last_seen_at=NOW(),
                last_socket_at=NOW(),
                current_room=VALUES(current_room)
        """, (user_id, room_name[:120]))
        return
    cur.execute("""
        INSERT INTO user_presence (user_id, is_online, last_seen_at, last_socket_at, current_room)
        VALUES (%s, %s, NOW(), NOW(), %s)
        ON DUPLICATE KEY UPDATE
            is_online=VALUES(is_online),
            last_seen_at=NOW(),
            last_socket_at=NOW(),
            current_room=VALUES(current_room)
    """, (user_id, 1 if is_online else 0, room_name[:120]))

def _fetch_reaction_map(cur, channel_type, message_ids):
    if not message_ids:
        return {}
    placeholders = ",".join(["%s"] * len(message_ids))
    cur.execute(f"""
        SELECT message_id, reaction, COUNT(*) AS cnt
        FROM chat_reactions
        WHERE channel_type=%s
          AND message_id IN ({placeholders})
        GROUP BY message_id, reaction
    """, (channel_type, *message_ids))
    out = defaultdict(dict)
    for row in cur.fetchall():
        out[int(row["message_id"])][row["reaction"]] = int(row["cnt"] or 0)
    return dict(out)

def _fetch_starred_map(cur, channel_type, message_ids, user_id):
    if not message_ids:
        return {}
    placeholders = ",".join(["%s"] * len(message_ids))
    cur.execute(f"""
        SELECT message_id
        FROM chat_message_stars
        WHERE channel_type=%s
          AND user_id=%s
          AND message_id IN ({placeholders})
    """, (channel_type, user_id, *message_ids))
    return {int(r["message_id"]): 1 for r in cur.fetchall()}

def _fetch_receipt_counts(cur, channel_type, message_ids):
    if not message_ids:
        return {}
    placeholders = ",".join(["%s"] * len(message_ids))
    cur.execute(f"""
        SELECT
            message_id,
            SUM(CASE WHEN delivered_at IS NOT NULL THEN 1 ELSE 0 END) AS delivered_count,
            SUM(CASE WHEN seen_at IS NOT NULL THEN 1 ELSE 0 END) AS seen_count,
            COUNT(*) AS recipient_count
        FROM chat_message_receipts
        WHERE channel_type=%s
          AND message_id IN ({placeholders})
        GROUP BY message_id
    """, (channel_type, *message_ids))
    return {
        int(r["message_id"]): {
            "delivered_count": int(r.get("delivered_count") or 0),
            "seen_count": int(r.get("seen_count") or 0),
            "recipient_count": int(r.get("recipient_count") or 0)
        }
        for r in cur.fetchall()
    }

def _receipt_status(delivered_count, seen_count, recipient_count):
    delivered = int(delivered_count or 0)
    seen = int(seen_count or 0)
    recipients = int(recipient_count or 0)
    if recipients <= 0:
        return "sent"
    if seen >= recipients:
        return "seen"
    if delivered >= recipients:
        return "delivered"
    return "sent"

def _public_attachment_url(rel_path):
    if not rel_path:
        return None
    safe_rel = str(rel_path).replace("\\", "/").lstrip("/")
    if not safe_rel:
        return None
    return url_for("download_chat_attachment", rel_path=safe_rel, _external=False)

def _parse_date_only(value):
    if value is None:
        return None
    if isinstance(value, datetime):
        return value.date()
    if hasattr(value, "year") and hasattr(value, "month") and hasattr(value, "day") and not isinstance(value, str):
        try:
            return datetime(int(value.year), int(value.month), int(value.day)).date()
        except Exception:
            pass
    text = str(value).strip()
    if not text:
        return None
    try:
        return datetime.strptime(text, "%Y-%m-%d").date()
    except ValueError:
        return None

def _safe_json_dumps(payload):
    try:
        return json.dumps(payload or {}, ensure_ascii=True)
    except Exception:
        return "{}"

def _safe_json_loads(text):
    if not text:
        return {}
    try:
        value = json.loads(text)
        return value if isinstance(value, dict) else {}
    except Exception:
        return {}

def _parse_bool_flag(value, default=False):
    if value is None:
        return bool(default)
    text = str(value).strip().lower()
    if text in {"1", "true", "yes", "on"}:
        return True
    if text in {"0", "false", "no", "off"}:
        return False
    return bool(default)

def _looks_like_email(text):
    value = (text or "").strip()
    if not value:
        return False
    return bool(re.fullmatch(r"[^@\s]+@[^@\s]+\.[^@\s]{2,}", value))

def _normalize_phone(text):
    raw = (text or "").strip()
    if not raw:
        return ""
    return raw.replace(" ", "").replace("+", "").replace("-", "").replace("(", "").replace(")", "")

def _is_valid_phone(text):
    clean = _normalize_phone(text)
    if not clean:
        return False
    return clean.isdigit() and 7 <= len(clean) <= 15

def _build_simple_pdf(title, lines):
    safe_title = (title or "Chat Export").replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)")
    clean_lines = []
    for line in lines or []:
        txt = (line or "").replace("\\", "\\\\").replace("(", "\\(").replace(")", "\\)")
        if len(txt) > 110:
            txt = txt[:107] + "..."
        clean_lines.append(txt)
    content_lines = [f"BT /F1 14 Tf 50 790 Td ({safe_title}) Tj ET"]
    y = 768
    for line in clean_lines[:44]:
        content_lines.append(f"BT /F1 10 Tf 50 {y} Td ({line}) Tj ET")
        y -= 16
    content_stream = "\n".join(content_lines).encode("latin-1", errors="replace")
    parts = []
    offsets = []

    def push(obj_bytes):
        offsets.append(sum(len(p) for p in parts))
        parts.append(obj_bytes)

    header = b"%PDF-1.4\n"
    parts.append(header)
    push(b"1 0 obj << /Type /Catalog /Pages 2 0 R >> endobj\n")
    push(b"2 0 obj << /Type /Pages /Kids [3 0 R] /Count 1 >> endobj\n")
    push(b"3 0 obj << /Type /Page /Parent 2 0 R /MediaBox [0 0 595 842] /Resources << /Font << /F1 4 0 R >> >> /Contents 5 0 R >> endobj\n")
    push(b"4 0 obj << /Type /Font /Subtype /Type1 /BaseFont /Helvetica >> endobj\n")
    push(f"5 0 obj << /Length {len(content_stream)} >> stream\n".encode("latin-1") + content_stream + b"\nendstream endobj\n")
    xref_start = sum(len(p) for p in parts)
    xref = [b"xref\n0 6\n0000000000 65535 f \n"]
    for off in offsets:
        xref.append(f"{off:010d} 00000 n \n".encode("latin-1"))
    trailer = b"trailer << /Size 6 /Root 1 0 R >>\nstartxref\n" + str(xref_start).encode("latin-1") + b"\n%%EOF\n"
    return b"".join(parts + xref + [trailer])

def ensure_trip_feedback_schema():
    global _trip_feedback_schema_ready
    if _trip_feedback_schema_ready:
        return
    with _trip_feedback_schema_lock:
        if _trip_feedback_schema_ready:
            return
        db = get_db_connection()
        cur = db.cursor()
        _ensure_column(cur, "travel_posts", "itinerary", """
            ALTER TABLE travel_posts
            ADD COLUMN itinerary TEXT NULL
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS trip_reviews (
                id BIGINT AUTO_INCREMENT PRIMARY KEY,
                post_id INT NOT NULL,
                review_type VARCHAR(20) NOT NULL,
                reviewer_id INT NOT NULL,
                reviewee_user_id INT NOT NULL DEFAULT 0,
                rating TINYINT NOT NULL,
                comment VARCHAR(1000) NOT NULL DEFAULT '',
                created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                updated_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
                UNIQUE KEY uq_trip_review_unique (post_id, review_type, reviewer_id, reviewee_user_id),
                KEY idx_trip_reviews_post_type (post_id, review_type, created_at),
                KEY idx_trip_reviews_reviewee (reviewee_user_id, review_type, created_at)
            )
        """)
        _ensure_column(cur, "trip_reviews", "post_id", """
            ALTER TABLE trip_reviews
            ADD COLUMN post_id INT NOT NULL DEFAULT 0
        """)
        _ensure_column(cur, "trip_reviews", "review_type", """
            ALTER TABLE trip_reviews
            ADD COLUMN review_type VARCHAR(20) NOT NULL DEFAULT 'trip'
        """)
        _ensure_column(cur, "trip_reviews", "reviewer_id", """
            ALTER TABLE trip_reviews
            ADD COLUMN reviewer_id INT NOT NULL DEFAULT 0
        """)
        _ensure_column(cur, "trip_reviews", "reviewee_user_id", """
            ALTER TABLE trip_reviews
            ADD COLUMN reviewee_user_id INT NOT NULL DEFAULT 0
        """)
        _ensure_column(cur, "trip_reviews", "rating", """
            ALTER TABLE trip_reviews
            ADD COLUMN rating TINYINT NOT NULL DEFAULT 5
        """)
        _ensure_column(cur, "trip_reviews", "comment", """
            ALTER TABLE trip_reviews
            ADD COLUMN comment VARCHAR(1000) NOT NULL DEFAULT ''
        """)
        _ensure_column(cur, "trip_reviews", "created_at", """
            ALTER TABLE trip_reviews
            ADD COLUMN created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP
        """)
        _ensure_column(cur, "trip_reviews", "updated_at", """
            ALTER TABLE trip_reviews
            ADD COLUMN updated_at DATETIME NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP
        """)
        _ensure_column(cur, "trip_reviews", "is_flagged", """
            ALTER TABLE trip_reviews
            ADD COLUMN is_flagged TINYINT(1) NOT NULL DEFAULT 0
        """)
        _ensure_column(cur, "trip_reviews", "moderation_status", """
            ALTER TABLE trip_reviews
            ADD COLUMN moderation_status VARCHAR(20) NOT NULL DEFAULT 'clear'
        """)
        _ensure_column(cur, "trip_reviews", "moderated_at", """
            ALTER TABLE trip_reviews
            ADD COLUMN moderated_at DATETIME NULL
        """)
        _ensure_column(cur, "trip_reviews", "moderated_by", """
            ALTER TABLE trip_reviews
            ADD COLUMN moderated_by INT NULL
        """)
        _ensure_index(cur, "trip_reviews", "idx_trip_reviews_flag_status", """
            CREATE INDEX idx_trip_reviews_flag_status
            ON trip_reviews (is_flagged, moderation_status, created_at)
        """)
        _ensure_index(cur, "trip_reviews", "idx_trip_reviews_post_type", """
            CREATE INDEX idx_trip_reviews_post_type
            ON trip_reviews (post_id, review_type, created_at)
        """)
        _ensure_index(cur, "trip_reviews", "idx_trip_reviews_reviewee", """
            CREATE INDEX idx_trip_reviews_reviewee
            ON trip_reviews (reviewee_user_id, review_type, created_at)
        """)
        db.commit()
        cur.close()
        db.close()
        _trip_feedback_schema_ready = True

def _conversation_state_table_key(channel_type, channel_id):
    return channel_type.strip().lower(), int(channel_id)

def _fetch_channel_state(cur, channel_type, channel_id, user_id):
    ctype, cid = _conversation_state_table_key(channel_type, channel_id)
    cur.execute("""
        SELECT pinned, archived, starred, muted_until, draft_text, last_opened_at, last_seen_at
        FROM chat_channel_user_state
        WHERE channel_type=%s
          AND channel_id=%s
          AND user_id=%s
        LIMIT 1
    """, (ctype, cid, user_id))
    return cur.fetchone() or {}

def _save_channel_state(
    cur,
    channel_type,
    channel_id,
    user_id,
    *,
    pinned=None,
    archived=None,
    starred=None,
    muted_until=None,
    draft_text=None,
    touch_open=False,
    touch_seen=False
):
    ctype, cid = _conversation_state_table_key(channel_type, channel_id)
    fields = {
        "pinned": pinned,
        "archived": archived,
        "starred": starred,
        "muted_until": muted_until,
        "draft_text": draft_text
    }
    updates = []
    params = [ctype, cid, user_id]
    for col, value in fields.items():
        if value is None:
            continue
        updates.append(f"{col}=VALUES({col})")
        params.append(value)
    if touch_open:
        updates.append("last_opened_at=NOW()")
    if touch_seen:
        updates.append("last_seen_at=NOW()")
    if not updates:
        return
    columns = ["channel_type", "channel_id", "user_id"]
    values_sql = ["%s", "%s", "%s"]
    for col, value in fields.items():
        if value is None:
            continue
        columns.append(col)
        values_sql.append("%s")
    if "last_opened_at=NOW()" in updates:
        columns.append("last_opened_at")
        values_sql.append("NOW()")
    if "last_seen_at=NOW()" in updates:
        columns.append("last_seen_at")
        values_sql.append("NOW()")
    cur.execute(f"""
        INSERT INTO chat_channel_user_state ({",".join(columns)})
        VALUES ({",".join(values_sql)})
        ON DUPLICATE KEY UPDATE {", ".join(updates)}
    """, params)

def _create_trip_system_message(cur, post_id, actor_user_id, message_text, *, event_type="system"):
    text = _normalize_message(message_text)
    if not text:
        return None
    cur.execute("""
        INSERT INTO trip_messages
            (post_id, user_id, message, message_type, created_at)
        VALUES (%s, %s, %s, %s, NOW())
    """, (post_id, actor_user_id, text, event_type[:24]))
    message_id = int(cur.lastrowid or 0)
    if message_id:
        _create_group_receipts(cur, post_id, message_id, actor_user_id)
    return message_id

def _looks_like_password_hash(value):
    if not isinstance(value, str):
        return False
    return value.startswith(("pbkdf2:", "scrypt:", "argon2:"))

def _normalize_pair(a, b):
    x, y = int(a), int(b)
    return (x, y) if x <= y else (y, x)

def _chat_ack(ok, code, **extra):
    payload = {"ok": bool(ok), "code": code}
    payload.update(extra)
    return payload

def _is_password_policy_valid(password):
    if not password or len(password) < PASSWORD_POLICY_MIN_LENGTH:
        return False
    if not PASSWORD_POLICY_RE.search(password):
        return False
    return True

def _ensure_index(cur, table_name, index_name, ddl):
    cur.execute("""
        SELECT 1
        FROM information_schema.statistics
        WHERE table_schema = DATABASE()
          AND table_name = %s
          AND index_name = %s
        LIMIT 1
    """, (table_name, index_name))
    if not cur.fetchone():
        cur.execute(ddl)

def _ensure_unique_index(cur, table_name, index_name, ddl):
    cur.execute("""
        SELECT 1
        FROM information_schema.statistics
        WHERE table_schema = DATABASE()
          AND table_name = %s
          AND index_name = %s
          AND non_unique = 0
        LIMIT 1
    """, (table_name, index_name))
    if not cur.fetchone():
        cur.execute(ddl)

def _ensure_column(cur, table_name, column_name, ddl):
    cur.execute("""
        SELECT 1
        FROM information_schema.columns
        WHERE table_schema = DATABASE()
          AND table_name = %s
          AND column_name = %s
        LIMIT 1
    """, (table_name, column_name))
    if not cur.fetchone():
        cur.execute(ddl)

def ensure_auth_schema():
    global _auth_schema_ready
    if _auth_schema_ready:
        return
    with _auth_schema_lock:
        if _auth_schema_ready:
            return
        db = get_db_connection()
        cur = db.cursor()
        try:
            _ensure_column(cur, "User_Details", "is_active", """
                ALTER TABLE User_Details
                ADD COLUMN is_active TINYINT(1) NOT NULL DEFAULT 1
            """)
            _ensure_column(cur, "User_Details", "email", """
                ALTER TABLE User_Details
                ADD COLUMN email VARCHAR(255) NULL
            """)
            _ensure_column(cur, "User_Details", "phone", """
                ALTER TABLE User_Details
                ADD COLUMN phone VARCHAR(30) NULL
            """)
            _ensure_column(cur, "User_Details", "notify_email", """
                ALTER TABLE User_Details
                ADD COLUMN notify_email TINYINT(1) NOT NULL DEFAULT 1
            """)
            _ensure_column(cur, "User_Details", "notify_sms", """
                ALTER TABLE User_Details
                ADD COLUMN notify_sms TINYINT(1) NOT NULL DEFAULT 0
            """)
            cur.execute("""
                CREATE TABLE IF NOT EXISTS login_logs (
                    id INT AUTO_INCREMENT PRIMARY KEY,
                    username VARCHAR(255) NOT NULL,
                    ip_address VARCHAR(64) NULL,
                    status VARCHAR(32) NOT NULL,
                    created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                    KEY idx_login_logs_username_created (username, created_at),
                    KEY idx_login_logs_status_created (status, created_at)
                )
            """)
            db.commit()
            _auth_schema_ready = True
        finally:
            cur.close()
            db.close()

def ensure_trip_core_schema():
    global _trip_core_schema_ready
    if _trip_core_schema_ready:
        return
    with _trip_core_schema_lock:
        if _trip_core_schema_ready:
            return
        db = get_db_connection()
        cur = db.cursor()
        try:
            _ensure_column(cur, "travel_posts", "duration", """
                ALTER TABLE travel_posts
                ADD COLUMN duration INT NOT NULL DEFAULT 1
            """)
            _ensure_column(cur, "travel_posts", "start_location", """
                ALTER TABLE travel_posts
                ADD COLUMN start_location VARCHAR(255) NULL
            """)
            _ensure_column(cur, "travel_posts", "description", """
                ALTER TABLE travel_posts
                ADD COLUMN description TEXT NULL
            """)
            _ensure_column(cur, "travel_posts", "trip_status", """
                ALTER TABLE travel_posts
                ADD COLUMN trip_status VARCHAR(20) NOT NULL DEFAULT 'open'
            """)
            _ensure_column(cur, "travel_posts", "created_at", """
                ALTER TABLE travel_posts
                ADD COLUMN created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP
            """)
            _ensure_column(cur, "travel_posts", "cancel_reason", """
                ALTER TABLE travel_posts
                ADD COLUMN cancel_reason VARCHAR(255) NULL
            """)
            _ensure_column(cur, "travel_posts", "cancelled_at", """
                ALTER TABLE travel_posts
                ADD COLUMN cancelled_at DATETIME NULL
            """)
            _ensure_column(cur, "travel_posts", "completed_at", """
                ALTER TABLE travel_posts
                ADD COLUMN completed_at DATETIME NULL
            """)

            _ensure_column(cur, "trip_members", "status", """
                ALTER TABLE trip_members
                ADD COLUMN status VARCHAR(20) NOT NULL DEFAULT 'pending'
            """)
            _ensure_column(cur, "trip_members", "member_name", """
                ALTER TABLE trip_members
                ADD COLUMN member_name VARCHAR(120) NULL
            """)
            _ensure_column(cur, "trip_members", "contact_no", """
                ALTER TABLE trip_members
                ADD COLUMN contact_no VARCHAR(30) NULL
            """)
            _ensure_column(cur, "trip_members", "address", """
                ALTER TABLE trip_members
                ADD COLUMN address VARCHAR(300) NULL
            """)
            _ensure_column(cur, "trip_members", "language", """
                ALTER TABLE trip_members
                ADD COLUMN language VARCHAR(80) NULL
            """)
            _ensure_column(cur, "trip_members", "amount_due", """
                ALTER TABLE trip_members
                ADD COLUMN amount_due DECIMAL(10,2) NOT NULL DEFAULT 0
            """)
            _ensure_column(cur, "trip_members", "amount_paid", """
                ALTER TABLE trip_members
                ADD COLUMN amount_paid DECIMAL(10,2) NOT NULL DEFAULT 0
            """)
            _ensure_column(cur, "trip_members", "payment_status", """
                ALTER TABLE trip_members
                ADD COLUMN payment_status VARCHAR(20) NOT NULL DEFAULT 'unpaid'
            """)
            _ensure_column(cur, "trip_members", "created_at", """
                ALTER TABLE trip_members
                ADD COLUMN created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP
            """)
            _ensure_index(cur, "travel_posts", "idx_travel_posts_user_status_date", """
                CREATE INDEX idx_travel_posts_user_status_date
                ON travel_posts (user_id, trip_status, travel_date)
            """)
            _ensure_index(cur, "trip_members", "idx_trip_members_post_status", """
                CREATE INDEX idx_trip_members_post_status
                ON trip_members (post_id, status)
            """)
            _ensure_index(cur, "trip_members", "idx_trip_members_user_status", """
                CREATE INDEX idx_trip_members_user_status
                ON trip_members (user_id, status, post_id)
            """)
            db.commit()
            _trip_core_schema_ready = True
        finally:
            cur.close()
            db.close()

def _delete_ids_in_chunks(cur, table_name, id_list):
    if not id_list:
        return
    chunk_size = 500
    for i in range(0, len(id_list), chunk_size):
        chunk = id_list[i:i + chunk_size]
        placeholders = ",".join(["%s"] * len(chunk))
        cur.execute(f"DELETE FROM {table_name} WHERE id IN ({placeholders})", chunk)

def _dedupe_trip_members(cur):
    cur.execute("""
        SELECT id, post_id, user_id, status
        FROM trip_members
        ORDER BY post_id, user_id,
                 CASE status
                     WHEN 'approved' THEN 3
                     WHEN 'pending' THEN 2
                     WHEN 'rejected' THEN 1
                     ELSE 0
                 END DESC,
                 id DESC
    """)
    rows = cur.fetchall()
    seen = set()
    remove_ids = []
    for row in rows:
        key = (row["post_id"], row["user_id"])
        if key in seen:
            remove_ids.append(row["id"])
        else:
            seen.add(key)
    _delete_ids_in_chunks(cur, "trip_members", remove_ids)

def _dedupe_private_conversations(cur):
    cur.execute("""
        SELECT id, user1_id, user2_id
        FROM private_conversations
        ORDER BY id
    """)
    rows = cur.fetchall()
    keep_by_pair = {}

    for row in rows:
        convo_id = row["id"]
        u1, u2 = _normalize_pair(row["user1_id"], row["user2_id"])

        if row["user1_id"] != u1 or row["user2_id"] != u2:
            cur.execute("""
                UPDATE private_conversations
                SET user1_id=%s, user2_id=%s
                WHERE id=%s
            """, (u1, u2, convo_id))

        key = (u1, u2)
        keep_id = keep_by_pair.get(key)
        if keep_id is None:
            keep_by_pair[key] = convo_id
            continue

        cur.execute("""
            UPDATE private_messages
            SET conversation_id=%s
            WHERE conversation_id=%s
        """, (keep_id, convo_id))

        cur.execute("""
            INSERT INTO private_chat_reads (conversation_id, user_id, last_read_at)
            SELECT %s, user_id, last_read_at
            FROM private_chat_reads
            WHERE conversation_id=%s
            ON DUPLICATE KEY UPDATE
                last_read_at = GREATEST(private_chat_reads.last_read_at, VALUES(last_read_at))
        """, (keep_id, convo_id))

        cur.execute("DELETE FROM private_chat_reads WHERE conversation_id=%s", (convo_id,))
        cur.execute("DELETE FROM private_conversations WHERE id=%s", (convo_id,))

def ensure_chat_schema():
    global _chat_schema_ready
    if _chat_schema_ready:
        return
    with _chat_schema_lock:
        if _chat_schema_ready:
            return

        db = get_db_connection()
        cur = db.cursor()

        cur.execute("""
            CREATE TABLE IF NOT EXISTS private_chat_reads (
                conversation_id INT NOT NULL,
                user_id INT NOT NULL,
                last_read_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                PRIMARY KEY (conversation_id, user_id)
            )
        """)

        _ensure_column(cur, "private_messages", "edited_at", """
            ALTER TABLE private_messages
            ADD COLUMN edited_at DATETIME NULL
        """)
        _ensure_column(cur, "private_messages", "deleted_at", """
            ALTER TABLE private_messages
            ADD COLUMN deleted_at DATETIME NULL
        """)
        _ensure_column(cur, "private_messages", "is_flagged", """
            ALTER TABLE private_messages
            ADD COLUMN is_flagged TINYINT(1) NOT NULL DEFAULT 0
        """)
        _ensure_column(cur, "private_messages", "reply_to_id", """
            ALTER TABLE private_messages
            ADD COLUMN reply_to_id INT NULL
        """)
        _ensure_column(cur, "private_messages", "attachment_path", """
            ALTER TABLE private_messages
            ADD COLUMN attachment_path VARCHAR(500) NULL
        """)
        _ensure_column(cur, "private_messages", "attachment_name", """
            ALTER TABLE private_messages
            ADD COLUMN attachment_name VARCHAR(255) NULL
        """)
        _ensure_column(cur, "private_messages", "attachment_type", """
            ALTER TABLE private_messages
            ADD COLUMN attachment_type VARCHAR(120) NULL
        """)
        _ensure_column(cur, "private_messages", "attachment_size", """
            ALTER TABLE private_messages
            ADD COLUMN attachment_size INT NULL
        """)
        _ensure_column(cur, "private_messages", "message_type", """
            ALTER TABLE private_messages
            ADD COLUMN message_type VARCHAR(24) NOT NULL DEFAULT 'text'
        """)
        _ensure_column(cur, "private_messages", "moderation_status", """
            ALTER TABLE private_messages
            ADD COLUMN moderation_status VARCHAR(20) NOT NULL DEFAULT 'clear'
        """)
        _ensure_column(cur, "private_messages", "moderated_at", """
            ALTER TABLE private_messages
            ADD COLUMN moderated_at DATETIME NULL
        """)
        _ensure_column(cur, "private_messages", "moderated_by", """
            ALTER TABLE private_messages
            ADD COLUMN moderated_by INT NULL
        """)
        _ensure_column(cur, "trip_messages", "edited_at", """
            ALTER TABLE trip_messages
            ADD COLUMN edited_at DATETIME NULL
        """)
        _ensure_column(cur, "trip_messages", "deleted_at", """
            ALTER TABLE trip_messages
            ADD COLUMN deleted_at DATETIME NULL
        """)
        _ensure_column(cur, "trip_messages", "is_flagged", """
            ALTER TABLE trip_messages
            ADD COLUMN is_flagged TINYINT(1) NOT NULL DEFAULT 0
        """)
        _ensure_column(cur, "trip_messages", "reply_to_id", """
            ALTER TABLE trip_messages
            ADD COLUMN reply_to_id INT NULL
        """)
        _ensure_column(cur, "trip_messages", "attachment_path", """
            ALTER TABLE trip_messages
            ADD COLUMN attachment_path VARCHAR(500) NULL
        """)
        _ensure_column(cur, "trip_messages", "attachment_name", """
            ALTER TABLE trip_messages
            ADD COLUMN attachment_name VARCHAR(255) NULL
        """)
        _ensure_column(cur, "trip_messages", "attachment_type", """
            ALTER TABLE trip_messages
            ADD COLUMN attachment_type VARCHAR(120) NULL
        """)
        _ensure_column(cur, "trip_messages", "attachment_size", """
            ALTER TABLE trip_messages
            ADD COLUMN attachment_size INT NULL
        """)
        _ensure_column(cur, "trip_messages", "message_type", """
            ALTER TABLE trip_messages
            ADD COLUMN message_type VARCHAR(24) NOT NULL DEFAULT 'text'
        """)
        _ensure_column(cur, "trip_messages", "moderation_status", """
            ALTER TABLE trip_messages
            ADD COLUMN moderation_status VARCHAR(20) NOT NULL DEFAULT 'clear'
        """)
        _ensure_column(cur, "trip_messages", "moderated_at", """
            ALTER TABLE trip_messages
            ADD COLUMN moderated_at DATETIME NULL
        """)
        _ensure_column(cur, "trip_messages", "moderated_by", """
            ALTER TABLE trip_messages
            ADD COLUMN moderated_by INT NULL
        """)
        _ensure_column(cur, "private_conversations", "is_support", """
            ALTER TABLE private_conversations
            ADD COLUMN is_support TINYINT(1) NOT NULL DEFAULT 0
        """)
        _ensure_column(cur, "private_conversations", "support_status", """
            ALTER TABLE private_conversations
            ADD COLUMN support_status VARCHAR(20) NOT NULL DEFAULT 'open'
        """)
        _ensure_column(cur, "private_conversations", "support_priority", """
            ALTER TABLE private_conversations
            ADD COLUMN support_priority VARCHAR(20) NOT NULL DEFAULT 'normal'
        """)
        _ensure_column(cur, "private_conversations", "assigned_admin_id", """
            ALTER TABLE private_conversations
            ADD COLUMN assigned_admin_id INT NULL
        """)
        _ensure_column(cur, "private_conversations", "support_opened_by", """
            ALTER TABLE private_conversations
            ADD COLUMN support_opened_by INT NULL
        """)
        _ensure_column(cur, "private_conversations", "is_archived", """
            ALTER TABLE private_conversations
            ADD COLUMN is_archived TINYINT(1) NOT NULL DEFAULT 0
        """)

        _ensure_index(cur, "trip_messages", "idx_trip_messages_post_created", """
            CREATE INDEX idx_trip_messages_post_created
            ON trip_messages (post_id, created_at)
        """)
        _ensure_index(cur, "private_messages", "idx_private_messages_conversation_created", """
            CREATE INDEX idx_private_messages_conversation_created
            ON private_messages (conversation_id, created_at)
        """)
        _ensure_index(cur, "trip_members", "idx_trip_members_post_user_status", """
            CREATE INDEX idx_trip_members_post_user_status
            ON trip_members (post_id, user_id, status)
        """)
        _ensure_index(cur, "private_conversations", "idx_private_conversations_pair", """
            CREATE INDEX idx_private_conversations_pair
            ON private_conversations (user1_id, user2_id)
        """)
        _ensure_index(cur, "private_chat_reads", "idx_private_chat_reads_user_read", """
            CREATE INDEX idx_private_chat_reads_user_read
            ON private_chat_reads (user_id, last_read_at)
        """)
        _ensure_index(cur, "trip_chat_reads", "idx_trip_chat_reads_user_read", """
            CREATE INDEX idx_trip_chat_reads_user_read
            ON trip_chat_reads (user_id, last_read_at)
        """)
        _ensure_index(cur, "private_messages", "idx_private_messages_conversation_deleted_id", """
            CREATE INDEX idx_private_messages_conversation_deleted_id
            ON private_messages (conversation_id, deleted_at, id)
        """)
        _ensure_index(cur, "private_messages", "idx_private_messages_conversation_sender_read", """
            CREATE INDEX idx_private_messages_conversation_sender_read
            ON private_messages (conversation_id, sender_id, deleted_at, created_at)
        """)
        _ensure_index(cur, "trip_messages", "idx_trip_messages_post_deleted_id", """
            CREATE INDEX idx_trip_messages_post_deleted_id
            ON trip_messages (post_id, deleted_at, id)
        """)
        _ensure_index(cur, "trip_messages", "idx_trip_messages_post_sender_read", """
            CREATE INDEX idx_trip_messages_post_sender_read
            ON trip_messages (post_id, user_id, deleted_at, created_at)
        """)
        _ensure_index(cur, "private_conversations", "idx_private_conversations_support", """
            CREATE INDEX idx_private_conversations_support
            ON private_conversations (is_support, support_status, support_priority, assigned_admin_id)
        """)
        _ensure_index(cur, "private_messages", "idx_private_messages_reply", """
            CREATE INDEX idx_private_messages_reply
            ON private_messages (reply_to_id)
        """)
        _ensure_index(cur, "trip_messages", "idx_trip_messages_reply", """
            CREATE INDEX idx_trip_messages_reply
            ON trip_messages (reply_to_id)
        """)
        _ensure_index(cur, "private_messages", "idx_private_messages_flag_status", """
            CREATE INDEX idx_private_messages_flag_status
            ON private_messages (is_flagged, moderation_status, created_at)
        """)
        _ensure_index(cur, "trip_messages", "idx_trip_messages_flag_status", """
            CREATE INDEX idx_trip_messages_flag_status
            ON trip_messages (is_flagged, moderation_status, created_at)
        """)

        cur.execute("""
            CREATE TABLE IF NOT EXISTS chat_message_receipts (
                id BIGINT AUTO_INCREMENT PRIMARY KEY,
                channel_type VARCHAR(16) NOT NULL,
                channel_id INT NOT NULL,
                message_id INT NOT NULL,
                user_id INT NOT NULL,
                delivered_at DATETIME NULL,
                seen_at DATETIME NULL,
                created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                UNIQUE KEY ux_chat_message_receipt (channel_type, message_id, user_id),
                KEY idx_chat_message_receipt_user (user_id, channel_type, channel_id, seen_at),
                KEY idx_chat_message_receipt_msg (channel_type, message_id)
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS chat_reactions (
                id BIGINT AUTO_INCREMENT PRIMARY KEY,
                channel_type VARCHAR(16) NOT NULL,
                message_id INT NOT NULL,
                user_id INT NOT NULL,
                reaction VARCHAR(16) NOT NULL,
                created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                UNIQUE KEY ux_chat_reaction (channel_type, message_id, user_id, reaction),
                KEY idx_chat_reaction_message (channel_type, message_id)
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS chat_message_stars (
                channel_type VARCHAR(16) NOT NULL,
                message_id INT NOT NULL,
                user_id INT NOT NULL,
                created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                PRIMARY KEY (channel_type, message_id, user_id),
                KEY idx_chat_message_stars_user (user_id, created_at)
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS chat_channel_user_state (
                channel_type VARCHAR(16) NOT NULL,
                channel_id INT NOT NULL,
                user_id INT NOT NULL,
                pinned TINYINT(1) NOT NULL DEFAULT 0,
                archived TINYINT(1) NOT NULL DEFAULT 0,
                starred TINYINT(1) NOT NULL DEFAULT 0,
                muted_until DATETIME NULL,
                draft_text TEXT NULL,
                last_opened_at DATETIME NULL,
                last_seen_at DATETIME NULL,
                PRIMARY KEY (channel_type, channel_id, user_id),
                KEY idx_chat_channel_state_user (user_id, channel_type, pinned, archived, starred)
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS conversation_user_state (
                conversation_id INT NOT NULL,
                user_id INT NOT NULL,
                pinned TINYINT(1) NOT NULL DEFAULT 0,
                archived TINYINT(1) NOT NULL DEFAULT 0,
                starred TINYINT(1) NOT NULL DEFAULT 0,
                muted_until DATETIME NULL,
                draft_text TEXT NULL,
                last_opened_at DATETIME NULL,
                last_seen_at DATETIME NULL,
                PRIMARY KEY (conversation_id, user_id),
                KEY idx_conversation_state_user (user_id, pinned, archived, starred)
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS user_blocks (
                blocker_id INT NOT NULL,
                blocked_id INT NOT NULL,
                muted TINYINT(1) NOT NULL DEFAULT 0,
                reason VARCHAR(255) NULL,
                created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                PRIMARY KEY (blocker_id, blocked_id),
                KEY idx_user_blocks_target (blocked_id)
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS user_reports (
                id BIGINT AUTO_INCREMENT PRIMARY KEY,
                reporter_id INT NOT NULL,
                reported_user_id INT NOT NULL,
                reason VARCHAR(255) NULL,
                details TEXT NULL,
                status VARCHAR(20) NOT NULL DEFAULT 'open',
                created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                reviewed_at DATETIME NULL,
                reviewed_by INT NULL,
                KEY idx_user_reports_status (status, created_at)
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS user_notifications (
                id BIGINT AUTO_INCREMENT PRIMARY KEY,
                user_id INT NOT NULL,
                title VARCHAR(180) NOT NULL,
                message VARCHAR(1000) NOT NULL,
                type VARCHAR(30) NOT NULL DEFAULT 'info',
                send_email TINYINT(1) NOT NULL DEFAULT 0,
                email_sent TINYINT(1) NOT NULL DEFAULT 0,
                is_read TINYINT(1) NOT NULL DEFAULT 0,
                created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                KEY idx_user_notifications_user_read (user_id, is_read, created_at)
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS admin_action_logs (
                id BIGINT AUTO_INCREMENT PRIMARY KEY,
                admin_user_id INT NOT NULL,
                action_type VARCHAR(80) NOT NULL,
                target_type VARCHAR(80) NOT NULL,
                target_id BIGINT NULL,
                details TEXT NULL,
                created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                KEY idx_admin_action_logs_admin (admin_user_id, created_at)
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS chat_uploads (
                id BIGINT AUTO_INCREMENT PRIMARY KEY,
                owner_id INT NOT NULL,
                channel_type VARCHAR(16) NOT NULL,
                channel_id INT NOT NULL,
                rel_path VARCHAR(500) NOT NULL,
                original_name VARCHAR(255) NULL,
                mime_type VARCHAR(120) NULL,
                file_size INT NULL,
                is_scanned TINYINT(1) NOT NULL DEFAULT 0,
                is_malicious TINYINT(1) NOT NULL DEFAULT 0,
                used_at DATETIME NULL,
                created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                KEY idx_chat_uploads_owner (owner_id, channel_type, channel_id, used_at)
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS user_presence (
                user_id INT PRIMARY KEY,
                is_online TINYINT(1) NOT NULL DEFAULT 0,
                last_seen_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                last_socket_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                current_room VARCHAR(120) NULL
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS scheduled_messages (
                id BIGINT AUTO_INCREMENT PRIMARY KEY,
                channel_type VARCHAR(16) NOT NULL,
                channel_id INT NOT NULL,
                sender_id INT NOT NULL,
                message TEXT NOT NULL,
                run_at DATETIME NOT NULL,
                status VARCHAR(20) NOT NULL DEFAULT 'scheduled',
                attachment_path VARCHAR(500) NULL,
                created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                sent_at DATETIME NULL,
                KEY idx_scheduled_messages_run (status, run_at)
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS background_jobs (
                id BIGINT AUTO_INCREMENT PRIMARY KEY,
                job_type VARCHAR(80) NOT NULL,
                payload LONGTEXT NULL,
                status VARCHAR(20) NOT NULL DEFAULT 'queued',
                run_at DATETIME NOT NULL,
                attempts INT NOT NULL DEFAULT 0,
                last_error TEXT NULL,
                created_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP,
                updated_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP,
                KEY idx_background_jobs_queue (status, run_at)
            )
        """)
        cur.execute("""
            CREATE TABLE IF NOT EXISTS system_settings (
                setting_key VARCHAR(80) PRIMARY KEY,
                setting_value VARCHAR(255) NOT NULL,
                updated_at DATETIME NOT NULL DEFAULT CURRENT_TIMESTAMP ON UPDATE CURRENT_TIMESTAMP
            )
        """)
        cur.execute("""
            INSERT INTO system_settings (setting_key, setting_value)
            VALUES ('chat_retention_days', %s)
            ON DUPLICATE KEY UPDATE setting_value=setting_value
        """, (str(CHAT_RETENTION_DEFAULT_DAYS),))

        _dedupe_private_conversations(cur)
        _dedupe_trip_members(cur)

        _ensure_unique_index(cur, "private_conversations", "ux_private_conversations_pair", """
            CREATE UNIQUE INDEX ux_private_conversations_pair
            ON private_conversations (user1_id, user2_id)
        """)
        _ensure_unique_index(cur, "trip_members", "ux_trip_members_post_user", """
            CREATE UNIQUE INDEX ux_trip_members_post_user
            ON trip_members (post_id, user_id)
        """)

        db.commit()
        cur.close()
        db.close()

        _chat_schema_ready = True

def _is_user_in_trip_chat(cur, post_id, user_id):
    cur.execute("""
        SELECT 1
        FROM travel_posts
        WHERE post_id=%s AND user_id=%s
        UNION
        SELECT 1
        FROM trip_members
        WHERE post_id=%s AND user_id=%s AND status='approved'
    """, (post_id, user_id, post_id, user_id))
    return bool(cur.fetchone())

def _has_relationship_policy(cur, user_id, other_user_id):
    if int(user_id) == int(other_user_id):
        return False

    cur.execute("""
        SELECT user_id, role
        FROM User_Details
        WHERE user_id IN (%s, %s)
    """, (user_id, other_user_id))
    role_map = {
        int(row["user_id"]): (row.get("role") or "").lower()
        for row in cur.fetchall()
    }
    if len(role_map) < 2:
        return False
    if _is_user_blocked(cur, user_id, other_user_id):
        return False
    if role_map.get(int(user_id)) == "admin" or role_map.get(int(other_user_id)) == "admin":
        return True

    cur.execute("""
        SELECT 1
        FROM travel_posts tp
        WHERE tp.trip_status != 'cancelled'
          AND (
              (tp.user_id = %s AND EXISTS (
                  SELECT 1
                  FROM trip_members host_peer
                  WHERE host_peer.post_id = tp.post_id
                    AND host_peer.user_id = %s
                    AND host_peer.status IN ('pending', 'approved')
              ))
              OR
              (tp.user_id = %s AND EXISTS (
                  SELECT 1
                  FROM trip_members host_peer
                  WHERE host_peer.post_id = tp.post_id
                    AND host_peer.user_id = %s
                    AND host_peer.status IN ('pending', 'approved')
              ))
              OR
              (
                  EXISTS (
                      SELECT 1
                      FROM trip_members tm1
                      WHERE tm1.post_id = tp.post_id
                        AND tm1.user_id = %s
                        AND tm1.status = 'approved'
                  )
                  AND EXISTS (
                      SELECT 1
                      FROM trip_members tm2
                      WHERE tm2.post_id = tp.post_id
                        AND tm2.user_id = %s
                        AND tm2.status = 'approved'
                  )
              )
          )
        LIMIT 1
    """, (
        user_id,
        other_user_id,
        other_user_id,
        user_id,
        user_id,
        other_user_id
    ))
    return bool(cur.fetchone())

def _has_message_relationship(cur, user_id, other_user_id):
    return _has_relationship_policy(cur, user_id, other_user_id)

def _conversation_other_user(cur, conversation_id, user_id):
    cur.execute("""
        SELECT user1_id, user2_id
        FROM private_conversations
        WHERE id=%s
        LIMIT 1
    """, (conversation_id,))
    row = cur.fetchone()
    if not row:
        return None
    if int(row["user1_id"]) == int(user_id):
        return int(row["user2_id"])
    if int(row["user2_id"]) == int(user_id):
        return int(row["user1_id"])
    return None

def _can_access_private_conversation(cur, conversation_id, user_id):
    other_user_id = _conversation_other_user(cur, conversation_id, user_id)
    if other_user_id is None:
        return False, None
    return _has_relationship_policy(cur, user_id, other_user_id), other_user_id

def _message_is_from_sender(cur, table_name, message_id, sender_col, sender_id):
    cur.execute(f"""
        SELECT 1
        FROM {table_name}
        WHERE id=%s
          AND {sender_col}=%s
          AND deleted_at IS NULL
        LIMIT 1
    """, (message_id, sender_id))
    return bool(cur.fetchone())

def _is_admin_user(cur, user_id):
    cur.execute("""
        SELECT 1
        FROM User_Details
        WHERE user_id=%s
          AND role='admin'
        LIMIT 1
    """, (user_id,))
    return bool(cur.fetchone())

def _create_private_receipts(cur, conversation_id, message_id, sender_id):
    cur.execute("""
        SELECT user1_id, user2_id
        FROM private_conversations
        WHERE id=%s
        LIMIT 1
    """, (conversation_id,))
    convo = cur.fetchone()
    if not convo:
        return
    recipients = [convo["user1_id"], convo["user2_id"]]
    for uid in recipients:
        if int(uid) == int(sender_id):
            continue
        cur.execute("""
            INSERT INTO chat_message_receipts
                (channel_type, channel_id, message_id, user_id, delivered_at, seen_at)
            VALUES ('private', %s, %s, %s, NULL, NULL)
            ON DUPLICATE KEY UPDATE channel_id=VALUES(channel_id)
        """, (conversation_id, message_id, uid))

def _create_group_receipts(cur, post_id, message_id, sender_id):
    cur.execute("""
        SELECT user_id
        FROM travel_posts
        WHERE post_id=%s
        UNION
        SELECT user_id
        FROM trip_members
        WHERE post_id=%s
          AND status='approved'
    """, (post_id, post_id))
    for row in cur.fetchall():
        uid = int(row["user_id"])
        if uid == int(sender_id):
            continue
        cur.execute("""
            INSERT INTO chat_message_receipts
                (channel_type, channel_id, message_id, user_id, delivered_at, seen_at)
            VALUES ('group', %s, %s, %s, NULL, NULL)
            ON DUPLICATE KEY UPDATE channel_id=VALUES(channel_id)
        """, (post_id, message_id, uid))

def _mark_private_delivered(cur, conversation_id, user_id):
    cur.execute("""
        UPDATE chat_message_receipts
        SET delivered_at = COALESCE(delivered_at, NOW())
        WHERE channel_type='private'
          AND channel_id=%s
          AND user_id=%s
    """, (conversation_id, user_id))

def _mark_group_delivered(cur, post_id, user_id):
    cur.execute("""
        UPDATE chat_message_receipts
        SET delivered_at = COALESCE(delivered_at, NOW())
        WHERE channel_type='group'
          AND channel_id=%s
          AND user_id=%s
    """, (post_id, user_id))

def mark_private_chat_read(cur, conversation_id, user_id):
    cur.execute("""
        INSERT INTO private_chat_reads (conversation_id, user_id, last_read_at)
        VALUES (%s, %s, NOW())
        ON DUPLICATE KEY UPDATE last_read_at = NOW()
    """, (conversation_id, user_id))
    cur.execute("""
        UPDATE chat_message_receipts
        SET delivered_at = COALESCE(delivered_at, NOW()),
            seen_at = COALESCE(seen_at, NOW())
        WHERE channel_type='private'
          AND channel_id=%s
          AND user_id=%s
    """, (conversation_id, user_id))

def mark_trip_chat_read(cur, post_id, user_id):
    cur.execute("""
        INSERT INTO trip_chat_reads (post_id, user_id, last_read_at)
        VALUES (%s, %s, NOW())
        ON DUPLICATE KEY UPDATE last_read_at = NOW()
    """, (post_id, user_id))
    cur.execute("""
        UPDATE chat_message_receipts
        SET delivered_at = COALESCE(delivered_at, NOW()),
            seen_at = COALESCE(seen_at, NOW())
        WHERE channel_type='group'
          AND channel_id=%s
          AND user_id=%s
    """, (post_id, user_id))

def _emit_receipt_snapshot(cur, channel_type, channel_id, room_name, event_name):
    cur.execute("""
        SELECT
            message_id,
            SUM(CASE WHEN delivered_at IS NOT NULL THEN 1 ELSE 0 END) AS delivered_count,
            SUM(CASE WHEN seen_at IS NOT NULL THEN 1 ELSE 0 END) AS seen_count,
            COUNT(*) AS recipient_count
        FROM chat_message_receipts
        WHERE channel_type=%s
          AND channel_id=%s
        GROUP BY message_id
        ORDER BY message_id DESC
        LIMIT 400
    """, (channel_type, channel_id))
    rows = cur.fetchall()
    if not rows:
        return
    payload_rows = []
    for row in rows:
        delivered = int(row.get("delivered_count") or 0)
        seen = int(row.get("seen_count") or 0)
        recipients = int(row.get("recipient_count") or 0)
        payload_rows.append({
            "message_id": int(row["message_id"]),
            "delivered_count": delivered,
            "seen_count": seen,
            "recipient_count": recipients,
            "status": _receipt_status(delivered, seen, recipients)
        })
    socketio.emit(event_name, {
        "channel_type": channel_type,
        "channel_id": int(channel_id),
        "rows": payload_rows
    }, room=room_name)

def _run_retention_cleanup(cur, retention_days):
    retention_days = max(30, int(retention_days or CHAT_RETENTION_DEFAULT_DAYS))
    summary = {"private_archived": 0, "group_archived": 0}
    cur.execute("""
        UPDATE private_messages
        SET deleted_at = NOW(),
            moderation_status='archived',
            moderated_at=NOW()
        WHERE deleted_at IS NULL
          AND is_flagged=0
          AND created_at < (NOW() - INTERVAL %s DAY)
    """, (retention_days,))
    summary["private_archived"] = int(cur.rowcount or 0)
    cur.execute("""
        UPDATE trip_messages
        SET deleted_at = NOW(),
            moderation_status='archived',
            moderated_at=NOW()
        WHERE deleted_at IS NULL
          AND is_flagged=0
          AND created_at < (NOW() - INTERVAL %s DAY)
    """, (retention_days,))
    summary["group_archived"] = int(cur.rowcount or 0)
    return summary

def _restore_archived_messages(cur, restore_days):
    days = max(1, min(120, int(restore_days or CHAT_RETENTION_RESTORE_DAYS)))
    summary = {"private_restored": 0, "group_restored": 0}
    cur.execute("""
        UPDATE private_messages
        SET deleted_at=NULL
        WHERE moderation_status='archived'
          AND deleted_at IS NOT NULL
          AND deleted_at >= (NOW() - INTERVAL %s DAY)
    """, (days,))
    summary["private_restored"] = int(cur.rowcount or 0)
    cur.execute("""
        UPDATE trip_messages
        SET deleted_at=NULL
        WHERE moderation_status='archived'
          AND deleted_at IS NOT NULL
          AND deleted_at >= (NOW() - INTERVAL %s DAY)
    """, (days,))
    summary["group_restored"] = int(cur.rowcount or 0)
    return summary

def _dispatch_scheduled_private(cur, row):
    channel_id = int(row["channel_id"])
    sender_id = int(row["sender_id"])
    cur.execute("""
        SELECT user1_id, user2_id
        FROM private_conversations
        WHERE id=%s
        LIMIT 1
    """, (channel_id,))
    convo = cur.fetchone()
    if not convo:
        return False
    if sender_id not in {int(convo["user1_id"]), int(convo["user2_id"])}:
        return False
    cur.execute("""
        INSERT INTO private_messages
            (conversation_id, sender_id, message, message_type, created_at)
        VALUES (%s, %s, %s, 'scheduled', NOW())
    """, (channel_id, sender_id, row["message"]))
    message_id = int(cur.lastrowid or 0)
    _create_private_receipts(cur, channel_id, message_id, sender_id)
    cur.execute("""
        SELECT username
        FROM User_Details
        WHERE user_id=%s
        LIMIT 1
    """, (sender_id,))
    user_row = cur.fetchone() or {}
    socketio.emit("private_message", {
        "conversation_id": channel_id,
        "id": message_id,
        "sender_id": sender_id,
        "username": user_row.get("username") or "User",
        "message": row["message"],
        "reply_to_id": None,
        "created_at": _dt_to_str(datetime.now()),
        "edited_at": None,
        "is_flagged": 0,
        "message_type": "scheduled"
    }, room=f"private_{channel_id}")
    return True

def _dispatch_scheduled_group(cur, row):
    post_id = int(row["channel_id"])
    sender_id = int(row["sender_id"])
    if not _is_user_in_trip_chat(cur, post_id, sender_id):
        return False
    cur.execute("""
        INSERT INTO trip_messages
            (post_id, user_id, message, message_type, created_at)
        VALUES (%s, %s, %s, 'scheduled', NOW())
    """, (post_id, sender_id, row["message"]))
    message_id = int(cur.lastrowid or 0)
    _create_group_receipts(cur, post_id, message_id, sender_id)
    cur.execute("""
        SELECT username
        FROM User_Details
        WHERE user_id=%s
        LIMIT 1
    """, (sender_id,))
    user_row = cur.fetchone() or {}
    socketio.emit("message", {
        "trip_id": post_id,
        "id": message_id,
        "user_id": sender_id,
        "username": user_row.get("username") or "User",
        "message": row["message"],
        "reply_to_id": None,
        "created_at": _dt_to_str(datetime.now()),
        "edited_at": None,
        "is_flagged": 0,
        "message_type": "scheduled"
    }, room=str(post_id))
    return True

def _process_due_scheduled_messages(cur, limit=80):
    limit = max(1, min(250, int(limit or 80)))
    cur.execute("""
        SELECT id, channel_type, channel_id, sender_id, message
        FROM scheduled_messages
        WHERE status='scheduled'
          AND run_at <= NOW()
        ORDER BY run_at ASC
        LIMIT %s
    """, (limit,))
    rows = cur.fetchall()
    sent = 0
    failed = 0
    for row in rows:
        ok = False
        ctype = (row.get("channel_type") or "").strip().lower()
        try:
            if ctype == "private":
                ok = _dispatch_scheduled_private(cur, row)
            elif ctype == "group":
                ok = _dispatch_scheduled_group(cur, row)
        except Exception:
            ok = False
        if ok:
            sent += 1
            cur.execute("""
                UPDATE scheduled_messages
                SET status='sent',
                    sent_at=NOW()
                WHERE id=%s
            """, (row["id"],))
        else:
            failed += 1
            cur.execute("""
                UPDATE scheduled_messages
                SET status='failed'
                WHERE id=%s
            """, (row["id"],))
    return {"total": len(rows), "sent": sent, "failed": failed}

def _run_background_jobs(cur, limit=80):
    limit = max(1, min(300, int(limit or 80)))
    cur.execute("""
        SELECT id, job_type, payload, attempts
        FROM background_jobs
        WHERE status='queued'
          AND run_at <= NOW()
        ORDER BY run_at ASC
        LIMIT %s
    """, (limit,))
    rows = cur.fetchall()
    processed = 0
    failed = 0
    for row in rows:
        payload = _safe_json_loads(row.get("payload"))
        ok = False
        error_text = ""
        try:
            if row["job_type"] == "send_notification_email":
                ok = _send_notification_email_stub(payload)
            elif row["job_type"] == "send_notification_sms":
                ok = _send_notification_sms_stub(payload)
            elif row["job_type"] == "run_retention":
                days = int(payload.get("days") or CHAT_RETENTION_DEFAULT_DAYS)
                _run_retention_cleanup(cur, days)
                ok = True
            elif row["job_type"] == "dispatch_scheduled":
                _process_due_scheduled_messages(cur, limit=120)
                ok = True
            else:
                ok = True
        except Exception as exc:
            ok = False
            error_text = str(exc)[:1600]
        if ok:
            processed += 1
            cur.execute("""
                UPDATE background_jobs
                SET status='done',
                    attempts=attempts+1,
                    last_error=NULL
                WHERE id=%s
            """, (row["id"],))
        else:
            failed += 1
            cur.execute("""
                UPDATE background_jobs
                SET status='failed',
                    attempts=attempts+1,
                    last_error=%s
                WHERE id=%s
            """, (error_text or "unknown error", row["id"]))
    return {"total": len(rows), "processed": processed, "failed": failed}

@socketio.on("join_private")
def join_private(data):
    ensure_chat_schema()
    convo_id = _parse_int(data.get("conversation_id"))
    user_id = session.get("user_id")

    if not convo_id or not user_id:
        return _chat_ack(False, "invalid", error="Invalid conversation")

    db = get_db_connection()
    cur = db.cursor()

    allowed, _ = _can_access_private_conversation(cur, convo_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        return _chat_ack(False, "forbidden", error="Not allowed")

    _mark_private_delivered(cur, convo_id, user_id)
    _touch_presence(cur, user_id, True, f"private_{convo_id}")
    _save_channel_state(cur, "private", convo_id, user_id, touch_open=True, touch_seen=True)
    _emit_receipt_snapshot(cur, "private", convo_id, f"private_{convo_id}", "private_receipts_updated")
    db.commit()

    cur.close()
    db.close()

    join_room(f"private_{convo_id}")
    return _chat_ack(True, "joined")

@socketio.on("send_private_message")
def send_private_message(data):
    ensure_chat_schema()
    convo_id = _parse_int(data.get("conversation_id"))
    message = _normalize_message(data.get("message") or "")
    client_id = str(data.get("client_id") or "").strip()[:64]
    reply_to_id = _parse_int(data.get("reply_to_id"))
    upload_id = _parse_int(data.get("upload_id"))
    user_id = session.get("user_id")

    if not convo_id or not user_id:
        return _chat_ack(False, "invalid", error="Message is invalid")
    if not message and not upload_id:
        return _chat_ack(False, "invalid", error="Message is invalid")
    if message and not _is_valid_message(message):
        return _chat_ack(False, "invalid", error="Message is invalid")

    if not _throttle_ok(user_id, f"private:{convo_id}"):
        return _chat_ack(False, "rate_limited", error="Please slow down")
    if not _redis_rate_ok_with_ip(user_id, f"private:{convo_id}", request.remote_addr):
        return _chat_ack(False, "rate_limited", error="Please slow down")

    db = get_db_connection()
    cur = db.cursor()

    allowed, other_user_id = _can_access_private_conversation(cur, convo_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        return _chat_ack(False, "forbidden", error="Not allowed")

    if not _spam_window_ok(cur, "private_messages", "conversation_id", convo_id, "sender_id", user_id):
        cur.close()
        db.close()
        return _chat_ack(False, "spam_limited", error="Too many messages, slow down")

    if message and _is_duplicate_message(cur, "private_messages", "conversation_id", convo_id, "sender_id", user_id, message):
        cur.close()
        db.close()
        return _chat_ack(False, "duplicate", error="Duplicate message blocked")

    attachment_path = None
    attachment_name = None
    attachment_type = None
    attachment_size = None
    if upload_id:
        cur.execute("""
            SELECT id, rel_path, original_name, mime_type, file_size, is_malicious
            FROM chat_uploads
            WHERE id=%s
              AND owner_id=%s
              AND channel_type='private'
              AND channel_id=%s
              AND used_at IS NULL
            LIMIT 1
        """, (upload_id, user_id, convo_id))
        upload_row = cur.fetchone()
        if not upload_row:
            cur.close()
            db.close()
            return _chat_ack(False, "invalid_attachment", error="Attachment not found")
        if int(upload_row.get("is_malicious") or 0) == 1:
            cur.close()
            db.close()
            return _chat_ack(False, "invalid_attachment", error="Attachment blocked")
        attachment_path = upload_row.get("rel_path")
        attachment_name = upload_row.get("original_name")
        attachment_type = upload_row.get("mime_type")
        attachment_size = upload_row.get("file_size")
        cur.execute("UPDATE chat_uploads SET used_at=NOW() WHERE id=%s", (upload_id,))

    if reply_to_id:
        cur.execute("""
            SELECT id
            FROM private_messages
            WHERE id=%s
              AND conversation_id=%s
              AND deleted_at IS NULL
            LIMIT 1
        """, (reply_to_id, convo_id))
        if not cur.fetchone():
            cur.close()
            db.close()
            return _chat_ack(False, "invalid_reply", error="Reply target not found")

    cur.execute("""
        INSERT INTO private_messages (
            conversation_id, sender_id, message, reply_to_id,
            attachment_path, attachment_name, attachment_type, attachment_size, message_type
        )
        VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
    """, (
        convo_id, user_id, message, reply_to_id,
        attachment_path, attachment_name, attachment_type, attachment_size,
        "attachment" if attachment_path else "text"
    ))

    message_id = cur.lastrowid
    cur.execute("SELECT created_at FROM private_messages WHERE id = %s", (message_id,))
    created_row = cur.fetchone()
    cur.execute("SELECT username FROM User_Details WHERE user_id=%s", (user_id,))
    username_row = cur.fetchone()
    username = username_row["username"] if username_row else "User"
    _create_private_receipts(cur, convo_id, message_id, user_id)
    _mark_private_delivered(cur, convo_id, user_id)

    if other_user_id:
        preview = message or (attachment_name and f"Attachment: {attachment_name}") or "New message"
        _create_notification(
            cur,
            other_user_id,
            "New private message",
            f"{username}: {preview}",
            ntype="chat",
            send_email=False
        )

    db.commit()

    cur.close()
    db.close()

    emit("private_message", {
        "conversation_id": convo_id,
        "id": message_id,
        "sender_id": user_id,
        "username": username,
        "message": message,
        "reply_to_id": reply_to_id,
        "created_at": _dt_to_str(created_row["created_at"] if created_row else datetime.now()),
        "edited_at": None,
        "is_flagged": 0,
        "attachment_path": attachment_path,
        "attachment_name": attachment_name,
        "attachment_type": attachment_type,
        "attachment_size": attachment_size,
        "attachment_url": (
            _public_attachment_url(attachment_path)
            if attachment_path else None
        ),
        "message_type": "attachment" if attachment_path else "text",
        "delivered_count": 0,
        "seen_count": 0,
        "recipient_count": 1,
        "receipt_status": "sent",
        "client_id": client_id
    }, room=f"private_{convo_id}")
    return _chat_ack(
        True,
        "sent",
        message_id=message_id,
        created_at=_dt_to_str(created_row["created_at"] if created_row else datetime.now()),
        client_id=client_id
    )

@socketio.on("connect")
def socket_connect():
    user_id = session.get("user_id")
    if not user_id:
        return
    db = get_db_connection()
    cur = db.cursor()
    _touch_presence(cur, user_id, True, "online")
    db.commit()
    cur.close()
    db.close()

@socketio.on("disconnect")
def socket_disconnect():
    user_id = session.get("user_id")
    if not user_id:
        return
    db = get_db_connection()
    cur = db.cursor()
    _touch_presence(cur, user_id, False, "")
    db.commit()
    cur.close()
    db.close()

def get_db_connection():
    return pymysql.connect(
        host=DB_HOST,
        user=DB_USER,
        password=DB_PASSWORD,
        database=DB_NAME,
        cursorclass=pymysql.cursors.DictCursor,
        autocommit=True
    )

def login_required(f):
    @wraps(f)
    def wrap(*args, **kwargs):
        if "user_id" not in session:
            return redirect(url_for("home"))
        try:
            ensure_auth_schema()
        except Exception:
            pass
        try:
            ensure_trip_core_schema()
        except Exception:
            pass
        return f(*args, **kwargs)
    return wrap

def generate_reset_token():
    return secrets.token_urlsafe(32)

@app.route("/forgot_password", methods=["GET", "POST"])
def forgot_password():

    if request.method == "GET":
        return render_template("forgot_password.html")

    username = request.form.get("username", "").strip()

    if not username:
        return render_template(
            "forgot_password.html",
            error="Enter your username."
        )

    db = get_db_connection()
    cur = db.cursor()

    cur.execute("SELECT user_id FROM User_Details WHERE username=%s", (username,))
    user = cur.fetchone()

    if not user:
        cur.close()
        db.close()
        return render_template(
            "forgot_password.html",
            error="Username not found."
        )

    token = generate_reset_token()
    expires = datetime.utcnow() + timedelta(minutes=10)

    cur.execute("""
        INSERT INTO password_resets (username, token, expires_at, used)
        VALUES (%s, %s, %s, FALSE)
    """, (username, token, expires))

    db.commit()
    cur.close()
    db.close()

    reset_link = url_for("reset_password", token=token, _external=True)

    return render_template(
        "forgot_password.html",
        success=f"Reset link: {reset_link}"
    )

@app.route("/reset_password/<token>", methods=["GET", "POST"])
def reset_password(token):

    db = get_db_connection()
    cur = db.cursor()

    cur.execute("""
        SELECT username, expires_at, used
        FROM password_resets
        WHERE token=%s
    """, (token,))

    record = cur.fetchone()

    if not record:
        cur.close()
        db.close()
        return "Invalid reset token."

    expires_at = record["expires_at"]

    if isinstance(expires_at, str):
        expires_at = datetime.fromisoformat(expires_at)

    if record["used"]:
        cur.close()
        db.close()
        return "This reset link has already been used."

    if datetime.utcnow() > expires_at:
        cur.close()
        db.close()
        return "Reset link expired."

    if request.method == "GET":
        cur.close()
        db.close()
        return render_template("reset_password.html", token=token)

    new_password = request.form.get("password", "").strip()

    if not new_password:
        cur.close()
        db.close()
        return render_template(
            "reset_password.html",
            token=token,
            error="Enter new password."
        )

    password_hash = generate_password_hash(new_password)
    cur.execute("""
        UPDATE User_Details
        SET password=%s
        WHERE username=%s
    """, (password_hash, record["username"]))

    cur.execute("""
        UPDATE password_resets
        SET used=TRUE
        WHERE token=%s
    """, (token,))

    db.commit()
    cur.close()
    db.close()

    return redirect(url_for("login"))

def admin_required(f):
    @wraps(f)
    def wrap(*args, **kwargs):
        if session.get("role") != "admin":
            abort(403)
        try:
            ensure_auth_schema()
        except Exception:
            pass
        return f(*args, **kwargs)
    return wrap


def non_admin_required(f):
    @wraps(f)
    def wrap(*args, **kwargs):
        if session.get("role") == "admin":
            return redirect(url_for("admin_dashboard"))
        return f(*args, **kwargs)
    return wrap

def get_host_status(user_id):
    if user_id == 0:
        return None

    db = get_db_connection()
    cur = db.cursor()

    cur.execute(
        "SELECT verification_status FROM host_profiles WHERE user_id=%s",
        (user_id,)
    )
    row = cur.fetchone()

    cur.close()
    db.close()

    return row["verification_status"] if row else None

def get_traveler_status(user_id):
    if user_id == 0:
        return None

    db = get_db_connection()
    cur = db.cursor()
    cur.execute(
        "SELECT verification_status FROM traveler_profiles WHERE user_id=%s",
        (user_id,)
    )
    row = cur.fetchone()
    cur.close()
    db.close()

    return row["verification_status"] if row else None

def is_host_verified(user_id):
    return get_host_status(user_id) == "approved"


def is_traveler_verified(user_id):
    return get_traveler_status(user_id) == "approved"

@app.route("/edit/<int:post_id>", methods=["GET", "POST"])
@login_required
def edit_trip(post_id):
    ensure_trip_feedback_schema()
    db = get_db_connection()
    cur = db.cursor()

    cur.execute("""
        SELECT destination, travel_date, duration, start_location,
               max_people, price, description, itinerary, trip_status
        FROM travel_posts
        WHERE post_id=%s AND user_id=%s
    """, (post_id, session["user_id"]))

    trip = cur.fetchone()

    if not trip:
        cur.close()
        db.close()
        abort(403)

    if trip["trip_status"] in ("completed", "cancelled"):
        cur.close()
        db.close()
        abort(403)

    if request.method == "POST":
        cur.execute("""
            UPDATE travel_posts
            SET destination=%s,
                travel_date=%s,
                duration=%s,
                start_location=%s,
                max_people=%s,
                price=%s,
                description=%s,
                itinerary=%s
            WHERE post_id=%s AND user_id=%s
        """, (
            request.form["destination"],
            request.form["travel_date"],
            request.form.get("duration"),
            request.form.get("start_location"),
            request.form["max_people"],
            request.form["price"],
            request.form.get("description"),
            request.form.get("itinerary"),
            post_id,
            session["user_id"]
        ))

        db.commit()

        cur.close()
        db.close()
        return redirect(url_for("mainpage", view="mine"))

    cur.close()
    db.close()

    return render_template(
        "edit_trip.html",
        trip=trip,
        post_id=post_id
    )

@app.route("/")
def home():
    return redirect(url_for("login"))

@app.route("/register", methods=["GET", "POST"])
def register():
    if request.method == "GET":
        return render_template("register.html")

    try:
        ensure_auth_schema()
    except Exception:
        return render_template(
            "register.html",
            error="Registration is temporarily unavailable. Please try again."
        )

    username = request.form.get("username", "").strip()
    password = request.form.get("password", "").strip()
    email = (request.form.get("email") or "").strip().lower()
    phone = (request.form.get("phone") or "").strip()
    phone_clean = _normalize_phone(phone)

    if not username or not password or not email:
        return render_template("register.html",
                               error="Please fill all required fields.")

    if not re.fullmatch(r"[A-Za-z0-9_]{3,30}", username):
        return render_template(
            "register.html",
            error="Username must be 3-30 characters and use letters, numbers, or underscore."
        )

    if not _is_password_policy_valid(password):
        return render_template(
            "register.html",
            error="Password must be at least 8 characters and include letters and numbers."
        )

    if not _looks_like_email(email):
        return render_template(
            "register.html",
            error="Enter a valid email address."
        )

    if phone_clean and not _is_valid_phone(phone_clean):
        return render_template(
            "register.html",
            error="Enter a valid phone number (7-15 digits)."
        )

    db = get_db_connection()
    cur = db.cursor()

    # Check duplicate username
    cur.execute(
        "SELECT user_id FROM User_Details WHERE username=%s",
        (username,)
    )

    if cur.fetchone():
        cur.close()
        db.close()
        return render_template("register.html",
                               error="Username already taken. Please choose another.")

    cur.execute(
        "SELECT user_id FROM User_Details WHERE email=%s LIMIT 1",
        (email,)
    )
    if cur.fetchone():
        cur.close()
        db.close()
        return render_template("register.html",
                               error="Email is already registered. Please use another email.")

    password_hash = generate_password_hash(password)
    cur.execute("""
        INSERT INTO User_Details
            (username, password, role, email, phone, notify_email, notify_sms)
        VALUES (%s, %s, 'user', %s, %s, 1, 0)
    """, (username, password_hash, email, phone_clean or None))

    db.commit()
    cur.close()
    db.close()

    flash("Account created! Please log in.", "success")
    return redirect(url_for("login"))

def is_account_locked():
    if "lockout_until" not in session:
        return False

    lock_time = datetime.fromisoformat(session["lockout_until"])
    return datetime.utcnow() < lock_time


def increment_login_attempts():
    session["login_attempts"] = session.get("login_attempts", 0) + 1

    if session["login_attempts"] >= MAX_ATTEMPTS:
        session["lockout_until"] = (
            datetime.utcnow() + timedelta(seconds=LOCKOUT_SECONDS)
        ).isoformat()
        return True

    return False


def reset_login_attempts():
    session.pop("login_attempts", None)
    session.pop("lockout_until", None)

@app.route("/admin/login_logs")
@admin_required
def admin_login_logs():

    db = get_db_connection()
    cur = db.cursor()

    cur.execute("""
        SELECT * FROM login_logs
        ORDER BY created_at DESC
        LIMIT 200
    """)

    logs = cur.fetchall()

    cur.close()
    db.close()

    return render_template("admin_login_logs.html", logs=logs)

def log_login_attempt(username, status):
    db = None
    cur = None
    try:
        ensure_auth_schema()
        db = get_db_connection()
        cur = db.cursor()
        cur.execute("""
            INSERT INTO login_logs (username, ip_address, status)
            VALUES (%s, %s, %s)
        """, (
            username,
            request.remote_addr,
            status
        ))
        db.commit()
    except Exception:
        return
    finally:
        if cur:
            cur.close()
        if db:
            db.close()

@app.route("/login", methods=["GET", "POST"])
def login():

    if request.method == "GET":
        return render_template("loginpage.html")

    try:
        ensure_auth_schema()
    except Exception:
        return render_template(
            "loginpage.html",
            error="Login is temporarily unavailable. Please try again."
        )

    username = request.form.get("username", "").strip()
    password = request.form.get("password", "").strip()

    remember = request.form.get("remember")

    if not username or not password:
        return render_template(
            "loginpage.html",
            error="Please enter username and password."
        )

    if is_account_locked():
        log_login_attempt(username, "locked")
        return render_template(
            "loginpage.html",
            error="Too many failed attempts. Try again later."
        )

    db = None
    cur = None
    try:
        db = get_db_connection()
        cur = db.cursor()
        cur.execute("""
            SELECT user_id, password, role, is_active
            FROM User_Details
            WHERE username=%s
        """, (username,))
        user = cur.fetchone()
    except Exception:
        return render_template(
            "loginpage.html",
            error="Unable to process login right now. Please try again."
        )
    finally:
        if cur:
            cur.close()
        if db:
            db.close()

    if user:

        if not user["is_active"]:
            log_login_attempt(username, "blocked")
            return render_template(
                "loginpage.html",
                error="Your account has been disabled. Contact admin."
            )

        stored_password = user.get("password") or ""
        password_ok = False

        if _looks_like_password_hash(stored_password):
            password_ok = check_password_hash(stored_password, password)
        else:
            password_ok = (stored_password == password)

        if password_ok:
            if not _looks_like_password_hash(stored_password):
                db_m = None
                cur_m = None
                try:
                    db_m = get_db_connection()
                    cur_m = db_m.cursor()
                    cur_m.execute("""
                        UPDATE User_Details
                        SET password=%s
                        WHERE user_id=%s
                    """, (generate_password_hash(password), user["user_id"]))
                    db_m.commit()
                except Exception:
                    pass
                finally:
                    if cur_m:
                        cur_m.close()
                    if db_m:
                        db_m.close()

            log_login_attempt(username, "success")

            session.clear()
            session["user_id"] = user["user_id"]
            session["username"] = username
            session["role"] = user["role"]

            reset_login_attempts()

            if remember:
                session.permanent = True

            if user["role"] == "admin":
                return redirect(url_for("admin_dashboard"))

            return redirect(url_for("mainpage"))

    log_login_attempt(username, "failed")

    if increment_login_attempts():
        return render_template(
            "loginpage.html",
            error="Too many failed attempts. Login disabled temporarily."
        )

    return render_template(
        "loginpage.html",
        error="Invalid credentials"
    )

def _dedupe_private_contacts(raw_rows, id_key, name_key, context_key):
    deduped = {}
    for row in raw_rows:
        other_id = row[id_key]
        travel_date = row.get("travel_date")
        if other_id not in deduped:
            deduped[other_id] = {
                "other_user_id": other_id,
                "display_name": row[name_key],
                "context_label": row.get(context_key, ""),
                "travel_date": travel_date,
                "conversation_id": None,
                "last_message": None,
                "last_message_at": None,
                "unread_count": 0,
                "pinned": 0,
                "archived": 0,
                "starred": 0,
                "muted_until": None,
                "online": 0,
                "last_seen_at": None
            }
            continue

        current = deduped[other_id]
        if travel_date and (
            current["travel_date"] is None
            or str(travel_date) > str(current["travel_date"])
        ):
            current["travel_date"] = travel_date
            current["context_label"] = row.get(context_key, current["context_label"])
    return list(deduped.values())

def _enrich_private_contacts(cur, user_id, contacts):
    if not contacts:
        return contacts

    ensure_chat_schema()

    user_ids = [c["other_user_id"] for c in contacts]
    placeholders = ",".join(["%s"] * len(user_ids))
    cur.execute(f"""
        SELECT id, user1_id, user2_id
        FROM private_conversations
        WHERE (user1_id=%s AND user2_id IN ({placeholders}))
           OR (user2_id=%s AND user1_id IN ({placeholders}))
    """, (user_id, *user_ids, user_id, *user_ids))

    convo_by_other = {}
    for row in cur.fetchall():
        other_id = row["user2_id"] if row["user1_id"] == user_id else row["user1_id"]
        convo_by_other[other_id] = row["id"]

    for c in contacts:
        c["conversation_id"] = convo_by_other.get(c["other_user_id"])

    convo_ids = [c["conversation_id"] for c in contacts if c["conversation_id"]]
    convo_stats = {}
    if convo_ids:
        convo_placeholders = ",".join(["%s"] * len(convo_ids))
        cur.execute(f"""
            SELECT
                pm.conversation_id,
                pm.message AS last_message,
                pm.created_at AS last_message_at,
                COALESCE(unread.unread_count, 0) AS unread_count
            FROM private_messages pm
            JOIN (
                SELECT conversation_id, MAX(id) AS max_id
                FROM private_messages
                WHERE conversation_id IN ({convo_placeholders})
                  AND deleted_at IS NULL
                GROUP BY conversation_id
            ) latest
              ON latest.conversation_id = pm.conversation_id
             AND latest.max_id = pm.id
            LEFT JOIN (
                SELECT pmu.conversation_id, COUNT(*) AS unread_count
                FROM private_messages pmu
                LEFT JOIN private_chat_reads pcr
                  ON pcr.conversation_id = pmu.conversation_id
                 AND pcr.user_id = %s
                WHERE pmu.conversation_id IN ({convo_placeholders})
                  AND pmu.sender_id != %s
                  AND pmu.deleted_at IS NULL
                  AND (
                      pcr.last_read_at IS NULL
                      OR pmu.created_at > pcr.last_read_at
                  )
                GROUP BY pmu.conversation_id
            ) unread
              ON unread.conversation_id = pm.conversation_id
            WHERE pm.conversation_id IN ({convo_placeholders})
              AND pm.deleted_at IS NULL
        """, (*convo_ids, user_id, *convo_ids, user_id, *convo_ids))
        convo_stats = {
            row["conversation_id"]: row
            for row in cur.fetchall()
        }

    for c in contacts:
        stats = convo_stats.get(c["conversation_id"])
        if not stats:
            continue
        c["last_message"] = stats["last_message"]
        c["last_message_at"] = stats["last_message_at"]
        c["unread_count"] = int(stats["unread_count"] or 0)

    if convo_ids:
        convo_placeholders = ",".join(["%s"] * len(convo_ids))
        cur.execute(f"""
            SELECT channel_id AS conversation_id, pinned, archived, starred, muted_until
            FROM chat_channel_user_state
            WHERE user_id=%s
              AND channel_type='private'
              AND channel_id IN ({convo_placeholders})
        """, (user_id, *convo_ids))
        state_by_convo = {int(r["conversation_id"]): r for r in cur.fetchall()}
        for c in contacts:
            convo_id = c.get("conversation_id")
            state = state_by_convo.get(int(convo_id)) if convo_id else None
            if not state:
                continue
            c["pinned"] = int(state.get("pinned") or 0)
            c["archived"] = int(state.get("archived") or 0)
            c["starred"] = int(state.get("starred") or 0)
            c["muted_until"] = state.get("muted_until")

    if user_ids:
        placeholders_presence = ",".join(["%s"] * len(user_ids))
        cur.execute(f"""
            SELECT user_id, is_online, last_seen_at
            FROM user_presence
            WHERE user_id IN ({placeholders_presence})
        """, user_ids)
        presence_by_user = {int(r["user_id"]): r for r in cur.fetchall()}
        for c in contacts:
            p = presence_by_user.get(int(c["other_user_id"]))
            if not p:
                continue
            c["online"] = int(p.get("is_online") or 0)
            c["last_seen_at"] = p.get("last_seen_at")

    contacts.sort(
        key=lambda c: (
            int(c.get("pinned") or 0),
            c["last_message_at"] or datetime.min
        ),
        reverse=True
    )
    return contacts

def fetch_chat_overview(cur, user_id):
    ensure_chat_schema()

    cur.execute("""
        SELECT
            tp.post_id,
            tp.destination,
            tp.travel_date,
            lm.message AS last_message,
            lm.created_at AS last_message_at,
            COALESCE(unread.unread_count, 0) AS unread_count
        FROM travel_posts tp
        LEFT JOIN trip_members my_tm
          ON my_tm.post_id = tp.post_id
         AND my_tm.user_id = %s
         AND my_tm.status = 'approved'
        LEFT JOIN (
            SELECT tm.post_id, tm.message, tm.created_at
            FROM trip_messages tm
            JOIN (
                SELECT post_id, MAX(id) AS max_id
                FROM trip_messages
                WHERE deleted_at IS NULL
                GROUP BY post_id
            ) latest
              ON latest.post_id = tm.post_id
             AND latest.max_id = tm.id
        ) lm
          ON lm.post_id = tp.post_id
        LEFT JOIN (
            SELECT tm.post_id, COUNT(*) AS unread_count
            FROM trip_messages tm
            LEFT JOIN trip_chat_reads tcr
              ON tcr.post_id = tm.post_id
             AND tcr.user_id = %s
            WHERE tm.user_id != %s
              AND tm.deleted_at IS NULL
              AND (
                  tcr.last_read_at IS NULL
                  OR tm.created_at > tcr.last_read_at
              )
            GROUP BY tm.post_id
        ) unread
          ON unread.post_id = tp.post_id
        WHERE tp.trip_status != 'cancelled'
          AND (
              tp.user_id = %s
              OR my_tm.id IS NOT NULL
          )
        ORDER BY COALESCE(lm.created_at, tp.travel_date) DESC
    """, (user_id, user_id, user_id, user_id))
    group_chat_trips = cur.fetchall()
    for row in group_chat_trips:
        row["unread_count"] = int(row.get("unread_count") or 0)

    cur.execute("""
        SELECT
            tp.post_id,
            tp.destination,
            tp.travel_date,
            tp.user_id AS host_id,
            u.username AS host_name
        FROM trip_members tm
        JOIN travel_posts tp ON tp.post_id = tm.post_id
        JOIN User_Details u ON u.user_id = tp.user_id
        WHERE tm.user_id = %s
          AND tm.status = 'approved'
          AND tp.trip_status != 'cancelled'
          AND tp.user_id != %s
        ORDER BY tp.travel_date DESC
    """, (user_id, user_id))
    host_chat_contacts = _dedupe_private_contacts(
        cur.fetchall(),
        id_key="host_id",
        name_key="host_name",
        context_key="destination"
    )

    cur.execute("""
        SELECT
            tp.post_id,
            tp.destination,
            tp.travel_date,
            tm.user_id AS traveler_id,
            u.username AS traveler_name
        FROM travel_posts tp
        JOIN trip_members tm
          ON tm.post_id = tp.post_id
         AND tm.status IN ('pending', 'approved')
        JOIN User_Details u ON u.user_id = tm.user_id
        WHERE tp.user_id = %s
          AND tp.trip_status != 'cancelled'
        ORDER BY tp.travel_date DESC, u.username
    """, (user_id,))
    traveler_to_host_contacts = _dedupe_private_contacts(
        cur.fetchall(),
        id_key="traveler_id",
        name_key="traveler_name",
        context_key="destination"
    )

    cur.execute("""
        SELECT
            tp.post_id,
            tp.destination,
            tp.travel_date,
            peer.user_id AS traveler_id,
            u.username AS traveler_name
        FROM trip_members me
        JOIN trip_members peer
          ON peer.post_id = me.post_id
         AND peer.status = 'approved'
         AND peer.user_id != me.user_id
        JOIN travel_posts tp ON tp.post_id = me.post_id
        JOIN User_Details u ON u.user_id = peer.user_id
        WHERE me.user_id = %s
          AND me.status = 'approved'
          AND tp.trip_status != 'cancelled'
        ORDER BY tp.travel_date DESC, u.username
    """, (user_id,))
    traveler_chat_contacts = _dedupe_private_contacts(
        cur.fetchall(),
        id_key="traveler_id",
        name_key="traveler_name",
        context_key="destination"
    )

    host_chat_contacts = _enrich_private_contacts(cur, user_id, host_chat_contacts)
    traveler_to_host_contacts = _enrich_private_contacts(cur, user_id, traveler_to_host_contacts)
    traveler_chat_contacts = _enrich_private_contacts(cur, user_id, traveler_chat_contacts)

    cur.execute("""
        SELECT
            u.user_id AS admin_id,
            u.username AS admin_name,
            'Support' AS context_label
        FROM User_Details u
        WHERE u.role = 'admin'
          AND u.is_active = 1
          AND u.user_id != %s
        ORDER BY u.username
    """, (user_id,))
    admin_chat_contacts = _dedupe_private_contacts(
        cur.fetchall(),
        id_key="admin_id",
        name_key="admin_name",
        context_key="context_label"
    )
    admin_chat_contacts = _enrich_private_contacts(cur, user_id, admin_chat_contacts)

    return {
        "group_chat_trips": group_chat_trips,
        "host_chat_contacts": host_chat_contacts,
        "traveler_to_host_contacts": traveler_to_host_contacts,
        "traveler_chat_contacts": traveler_chat_contacts,
        "admin_chat_contacts": admin_chat_contacts,
    }

def _build_message_widget(chat_data):
    group_rows = chat_data.get("group_chat_trips") or []
    host_rows = chat_data.get("host_chat_contacts") or []
    traveler_host_rows = chat_data.get("traveler_to_host_contacts") or []
    traveler_rows = chat_data.get("traveler_chat_contacts") or []
    admin_rows = chat_data.get("admin_chat_contacts") or []

    dm_rows = host_rows + traveler_host_rows + traveler_rows + admin_rows
    total_group_unread = sum(int(r.get("unread_count") or 0) for r in group_rows)
    total_dm_unread = sum(int(r.get("unread_count") or 0) for r in dm_rows)
    total_unread = total_group_unread + total_dm_unread

    latest = None
    latest_label = "No recent messages"
    latest_text = "Open inbox to start chatting."
    latest_at = None

    for row in group_rows:
        ts = row.get("last_message_at")
        if not ts:
            continue
        if latest is None or ts > latest:
            latest = ts
            latest_at = ts
            latest_label = f"Group: {row.get('destination') or 'Trip chat'}"
            latest_text = row.get("last_message") or "New group activity"

    for row in dm_rows:
        ts = row.get("last_message_at")
        if not ts:
            continue
        if latest is None or ts > latest:
            latest = ts
            latest_at = ts
            latest_label = f"DM: {row.get('display_name') or 'Contact'}"
            latest_text = row.get("last_message") or "New direct message"

    latest_text = (latest_text or "").strip()
    if len(latest_text) > 86:
        latest_text = latest_text[:83].rstrip() + "..."

    return {
        "total_unread": int(total_unread),
        "group_unread": int(total_group_unread),
        "dm_unread": int(total_dm_unread),
        "latest_label": latest_label,
        "latest_text": latest_text,
        "latest_at": latest_at
    }

def fetch_admin_chat_contacts(cur, admin_user_id, q="", role="all", page=1, per_page=25):
    ensure_chat_schema()

    q = (q or "").strip()
    role = (role or "all").lower()
    if role not in {"all", "host", "traveler", "user", "admin"}:
        role = "all"
    page = max(1, _parse_int(page) or 1)
    per_page = max(1, min(100, _parse_int(per_page) or 25))
    offset = (page - 1) * per_page

    role_clause = ""
    role_args = []
    if role != "all":
        role_clause = "AND u.role = %s"
        role_args.append(role)

    search_clause = ""
    search_args = []
    if q:
        like = f"%{q.lower()}%"
        search_clause = """
          AND (
              LOWER(u.username) LIKE %s
              OR LOWER(COALESCE(u.role, '')) LIKE %s
          )
        """
        search_args.extend([like, like])

    count_sql = f"""
        SELECT COUNT(*) AS total
        FROM User_Details u
        WHERE u.user_id != %s
          AND u.is_active = 1
          {role_clause}
          {search_clause}
    """
    cur.execute(count_sql, (admin_user_id, *role_args, *search_args))
    total = int((cur.fetchone() or {}).get("total") or 0)

    cur.execute("""
        SELECT
            u.user_id,
            u.username,
            u.role,
            pc.id AS conversation_id,
            pc.is_support,
            pc.support_status,
            pc.support_priority,
            pc.assigned_admin_id,
            pc.support_opened_by,
            assign_u.username AS assigned_admin_name,
            lm.message AS last_message,
            lm.created_at AS last_message_at,
            fm.sender_id AS first_sender_id,
            COALESCE(unread.unread_count, 0) AS unread_count,
            ll.last_login_at,
            COALESCE(lm.created_at, ll.last_login_at) AS last_active_at
        FROM User_Details u
        LEFT JOIN private_conversations pc
          ON pc.user1_id = LEAST(u.user_id, %s)
         AND pc.user2_id = GREATEST(u.user_id, %s)
        LEFT JOIN (
            SELECT pm.conversation_id, pm.message, pm.created_at
            FROM private_messages pm
            JOIN (
                SELECT conversation_id, MAX(id) AS max_id
                FROM private_messages
                WHERE deleted_at IS NULL
                GROUP BY conversation_id
            ) latest
              ON latest.conversation_id = pm.conversation_id
             AND latest.max_id = pm.id
        ) lm
          ON lm.conversation_id = pc.id
        LEFT JOIN (
            SELECT firsts.conversation_id, pm.sender_id
            FROM (
                SELECT conversation_id, MIN(id) AS first_id
                FROM private_messages
                WHERE deleted_at IS NULL
                GROUP BY conversation_id
            ) firsts
            JOIN private_messages pm ON pm.id = firsts.first_id
        ) fm
          ON fm.conversation_id = pc.id
        LEFT JOIN (
            SELECT
                pmu.conversation_id,
                COUNT(*) AS unread_count
            FROM private_messages pmu
            LEFT JOIN private_chat_reads pcr
              ON pcr.conversation_id = pmu.conversation_id
             AND pcr.user_id = %s
            WHERE pmu.sender_id != %s
              AND pmu.deleted_at IS NULL
              AND (
                  pcr.last_read_at IS NULL
                  OR pmu.created_at > pcr.last_read_at
              )
            GROUP BY pmu.conversation_id
        ) unread
          ON unread.conversation_id = pc.id
        LEFT JOIN (
            SELECT
                ll.username,
                MAX(ll.created_at) AS last_login_at
            FROM login_logs ll
            WHERE ll.status = 'success'
            GROUP BY ll.username
        ) ll
          ON ll.username = u.username
        LEFT JOIN User_Details assign_u
          ON assign_u.user_id = pc.assigned_admin_id
        WHERE u.user_id != %s
          AND u.is_active = 1
          {role_clause}
          {search_clause}
        ORDER BY
            COALESCE(lm.created_at, ll.last_login_at, '1970-01-01') DESC,
            CASE u.role
                WHEN 'host' THEN 1
                WHEN 'traveler' THEN 2
                WHEN 'user' THEN 3
                WHEN 'admin' THEN 4
                ELSE 5
            END,
            u.username
        LIMIT %s OFFSET %s
    """.format(role_clause=role_clause, search_clause=search_clause), (
        admin_user_id,
        admin_user_id,
        admin_user_id,
        admin_user_id,
        admin_user_id,
        *role_args,
        *search_args,
        per_page,
        offset
    ))

    contacts = []
    for row in cur.fetchall():
        user_role = (row.get("role") or "user").lower()
        label = {
            "host": "Host",
            "traveler": "Traveler",
            "admin": "Admin",
            "user": "User"
        }.get(user_role, "User")

        origin = "No messages yet"
        if row.get("conversation_id"):
            first_sender = row.get("first_sender_id")
            if first_sender is None:
                origin = "No messages yet"
            elif int(first_sender) == int(admin_user_id):
                origin = "Admin started"
            else:
                origin = "User started"

        contacts.append({
            "other_user_id": row["user_id"],
            "display_name": row["username"],
            "context_label": label,
            "travel_date": None,
            "conversation_id": row.get("conversation_id"),
            "last_message": row.get("last_message"),
            "last_message_at": row.get("last_message_at"),
            "unread_count": int(row.get("unread_count") or 0),
            "role": user_role,
            "last_login_at": row.get("last_login_at"),
            "last_active_at": row.get("last_active_at"),
            "conversation_origin": origin,
            "is_support": bool(row.get("is_support")),
            "support_status": row.get("support_status") or "open",
            "support_priority": row.get("support_priority") or "normal",
            "assigned_admin_id": row.get("assigned_admin_id"),
            "assigned_admin_name": row.get("assigned_admin_name"),
            "support_opened_by": row.get("support_opened_by")
        })

    return contacts, total, page, per_page

def get_admin_unread_private_count(cur, admin_user_id):
    ensure_chat_schema()
    cur.execute("""
        SELECT COUNT(*) AS unread_total
        FROM private_messages pm
        JOIN private_conversations pc
          ON pc.id = pm.conversation_id
        LEFT JOIN private_chat_reads pcr
          ON pcr.conversation_id = pm.conversation_id
         AND pcr.user_id = %s
        WHERE (pc.user1_id = %s OR pc.user2_id = %s)
          AND pm.sender_id != %s
          AND pm.deleted_at IS NULL
          AND (
              pcr.last_read_at IS NULL
              OR pm.created_at > pcr.last_read_at
          )
    """, (admin_user_id, admin_user_id, admin_user_id, admin_user_id))
    row = cur.fetchone() or {}
    return int(row.get("unread_total") or 0)

@app.route("/main")
@login_required
def mainpage():

    if session.get("role") == "admin":
        return redirect(url_for("admin_dashboard"))

    feedback_ready = True
    try:
        ensure_trip_feedback_schema()
    except Exception:
        feedback_ready = False

    if feedback_ready:
        host_avg_expr = """
                (
                    SELECT AVG(r.rating)
                    FROM trip_reviews r
                    WHERE r.review_type='host'
                      AND r.reviewee_user_id=tp.user_id
                      AND COALESCE(r.moderation_status, 'clear') != 'removed'
                )
        """
        host_count_expr = """
                (
                    SELECT COUNT(*)
                    FROM trip_reviews r
                    WHERE r.review_type='host'
                      AND r.reviewee_user_id=tp.user_id
                      AND COALESCE(r.moderation_status, 'clear') != 'removed'
                )
        """
    else:
        host_avg_expr = "NULL"
        host_count_expr = "0"

    view = request.args.get("view", "explore")

    db = get_db_connection()
    cur = db.cursor()

    host_status = get_host_status(session["user_id"])
    traveler_status = get_traveler_status(session["user_id"])

    joined_trips = set()
    approved_joined_trips = set()
    group_chat_trips = []
    host_chat_contacts = []
    traveler_to_host_contacts = []
    traveler_chat_contacts = []
    admin_chat_contacts = []

    if view == "explore":

        cur.execute(f"""
            SELECT
                tp.post_id,
                tp.user_id AS host_id,
                tp.destination,
                tp.travel_date,
                tp.max_people,
                tp.price,
                {host_avg_expr} AS host_avg_rating,
                {host_count_expr} AS host_reviews_count,
                COUNT(tm.id) AS joined,
                tp.trip_status
            FROM travel_posts tp
            LEFT JOIN trip_members tm
                ON tm.post_id = tp.post_id
                AND tm.status='approved'
            WHERE tp.user_id != %s
              AND tp.trip_status='open'
            GROUP BY tp.post_id
            ORDER BY tp.travel_date
        """, (session["user_id"],))

        trips = cur.fetchall()

    elif view == "mine":

        cur.execute(f"""
            SELECT
                tp.post_id,
                tp.user_id AS host_id,
                tp.destination,
                tp.travel_date,
                tp.max_people,
                tp.price,
                {host_avg_expr} AS host_avg_rating,
                {host_count_expr} AS host_reviews_count,
                COUNT(tm.id) AS joined,
                tp.trip_status
            FROM travel_posts tp
            LEFT JOIN trip_members tm
                ON tm.post_id = tp.post_id
                AND tm.status='approved'
            WHERE tp.user_id = %s
              AND tp.trip_status!='cancelled'
            GROUP BY tp.post_id
            ORDER BY tp.created_at DESC
        """, (session["user_id"],))

        trips = cur.fetchall()

    else:
        cur.execute(f"""
                    SELECT tp.post_id,
                        tp.user_id AS host_id,
                           tp.destination,
                           tp.travel_date,
                           tp.max_people,
                           tp.price,
                           {host_avg_expr} AS host_avg_rating,
                           {host_count_expr} AS host_reviews_count,
                           COUNT(tm2.id)                    AS joined,
                           tp.trip_status,
                           tm.amount_due,
                           tm.amount_paid,
                           (tm.amount_due - tm.amount_paid) AS remaining,
                           tm.payment_status, tm.status
                    FROM travel_posts tp
                             JOIN trip_members tm
                                  ON tm.post_id = tp.post_id
                                      AND tm.user_id = %s
                             LEFT JOIN trip_members tm2
                                       ON tm2.post_id = tp.post_id
                                           AND tm2.status = 'approved'
                    WHERE tp.trip_status!='cancelled'
                    GROUP BY tp.post_id
                    """, (session["user_id"],))

        trips = cur.fetchall()

    cur.execute("""
        SELECT post_id, status
        FROM trip_members
        WHERE user_id=%s
    """, (session["user_id"],))
    membership_rows = cur.fetchall()

    joined_trips = {row["post_id"] for row in membership_rows}
    approved_joined_trips = {
        row["post_id"] for row in membership_rows
        if row.get("status") == "approved"
    }

    chat_data = {
        "group_chat_trips": [],
        "host_chat_contacts": [],
        "traveler_to_host_contacts": [],
        "traveler_chat_contacts": [],
        "admin_chat_contacts": []
    }
    try:
        chat_data = fetch_chat_overview(cur, session["user_id"])
    except Exception:
        pass
    group_chat_trips = chat_data["group_chat_trips"]
    host_chat_contacts = chat_data["host_chat_contacts"]
    traveler_to_host_contacts = chat_data["traveler_to_host_contacts"]
    traveler_chat_contacts = chat_data["traveler_chat_contacts"]
    admin_chat_contacts = chat_data["admin_chat_contacts"]
    message_widget = _build_message_widget(chat_data)

    cur.close()
    db.close()

    return render_template(
        "mainpage.html",
        trips=trips,
        view=view,
        host_status=host_status,
        traveler_status=traveler_status,
        joined_trips=joined_trips,
        approved_joined_trips=approved_joined_trips,
        group_chat_trips=group_chat_trips,
        host_chat_contacts=host_chat_contacts,
        traveler_to_host_contacts=traveler_to_host_contacts,
        traveler_chat_contacts=traveler_chat_contacts,
        admin_chat_contacts=admin_chat_contacts,
        message_widget=message_widget
    )

@app.route("/messages")
@login_required
def messages_page():
    if session.get("role") == "admin":
        return redirect(url_for("admin_messages"))

    db = get_db_connection()
    cur = db.cursor()

    chat_data = {
        "group_chat_trips": [],
        "host_chat_contacts": [],
        "traveler_to_host_contacts": [],
        "traveler_chat_contacts": [],
        "admin_chat_contacts": []
    }
    try:
        chat_data = fetch_chat_overview(cur, session["user_id"])
    except Exception:
        pass

    cur.close()
    db.close()

    return render_template(
        "messages_page.html",
        group_chat_trips=chat_data["group_chat_trips"],
        host_chat_contacts=chat_data["host_chat_contacts"],
        traveler_to_host_contacts=chat_data["traveler_to_host_contacts"],
        traveler_chat_contacts=chat_data["traveler_chat_contacts"],
        admin_chat_contacts=chat_data["admin_chat_contacts"]
    )

@app.route("/admin/messages")
@admin_required
def admin_messages():
    q = request.args.get("q", "").strip()
    role = request.args.get("role", "all").strip().lower()
    page = _parse_int(request.args.get("page")) or 1
    per_page = _parse_int(request.args.get("per_page")) or 25

    db = get_db_connection()
    cur = db.cursor()

    contacts, total_contacts, page, per_page = fetch_admin_chat_contacts(
        cur,
        session["user_id"],
        q=q,
        role=role,
        page=page,
        per_page=per_page
    )
    total_unread = get_admin_unread_private_count(cur, session["user_id"])
    total_pages = max(1, math.ceil(total_contacts / per_page)) if total_contacts else 1
    if page > total_pages:
        page = total_pages
        contacts, total_contacts, page, per_page = fetch_admin_chat_contacts(
            cur,
            session["user_id"],
            q=q,
            role=role,
            page=page,
            per_page=per_page
        )

    cur.execute("""
        SELECT
            COALESCE(SUM(CASE WHEN pc.is_support=1 AND pc.support_status='open' THEN 1 ELSE 0 END), 0) AS open_count,
            COALESCE(SUM(CASE WHEN pc.is_support=1 AND pc.support_status='in_progress' THEN 1 ELSE 0 END), 0) AS in_progress_count,
            COALESCE(SUM(CASE WHEN pc.is_support=1 AND pc.support_status='resolved' THEN 1 ELSE 0 END), 0) AS resolved_count
        FROM private_conversations pc
        JOIN User_Details a ON a.user_id = pc.user1_id
        JOIN User_Details b ON b.user_id = pc.user2_id
        WHERE a.role='admin' OR b.role='admin'
    """)
    support_summary = cur.fetchone() or {}
    support_summary = {
        "open_count": int(support_summary.get("open_count") or 0),
        "in_progress_count": int(support_summary.get("in_progress_count") or 0),
        "resolved_count": int(support_summary.get("resolved_count") or 0)
    }

    cur.execute("""
        SELECT COUNT(*) AS flagged_private
        FROM private_messages
        WHERE is_flagged=1
          AND deleted_at IS NULL
    """)
    flagged_private = int((cur.fetchone() or {}).get("flagged_private") or 0)

    cur.execute("""
        SELECT COUNT(*) AS flagged_group
        FROM trip_messages
        WHERE is_flagged=1
          AND deleted_at IS NULL
    """)
    flagged_group = int((cur.fetchone() or {}).get("flagged_group") or 0)

    cur.execute("""
        SELECT user_id, username
        FROM User_Details
        WHERE role='admin'
          AND is_active=1
        ORDER BY username
    """)
    admin_assignees = cur.fetchall()

    cur.close()
    db.close()

    return render_template(
        "admin_messages.html",
        contacts=contacts,
        total_unread=total_unread,
        search_q=q,
        role_filter=role if role in {"all", "host", "traveler", "user", "admin"} else "all",
        page=page,
        per_page=per_page,
        total_contacts=total_contacts,
        total_pages=total_pages,
        support_summary=support_summary,
        flagged_private=flagged_private,
        flagged_group=flagged_group,
        admin_assignees=admin_assignees,
        current_admin_id=session["user_id"]
    )

@app.route("/chat")
@login_required
def chat_landing():
    return redirect(url_for("messages_page"))

@app.route("/host_profile", methods=["GET", "POST"])
@login_required
@non_admin_required
def host_profile():

    db = get_db_connection()
    cur = db.cursor()

    if request.method == "POST":
        full_name = (request.form.get("full_name") or "").strip()
        phone = (request.form.get("phone") or "").strip()
        phone_clean = _normalize_phone(phone)
        email = (request.form.get("email") or "").strip().lower()
        id_proof = (request.form.get("id_proof") or "").strip()
        experience = (request.form.get("experience") or "").strip()
        if email and not _looks_like_email(email):
            if request.headers.get("X-Requested-With") != "XMLHttpRequest":
                flash("Enter a valid email address.", "error")
                cur.close()
                db.close()
                return redirect(url_for("host_profile"))
            cur.close()
            db.close()
            return jsonify(success=False, error="Enter a valid email address."), 400
        if phone_clean and not _is_valid_phone(phone_clean):
            if request.headers.get("X-Requested-With") != "XMLHttpRequest":
                flash("Enter a valid phone number (7-15 digits).", "error")
                cur.close()
                db.close()
                return redirect(url_for("host_profile"))
            cur.close()
            db.close()
            return jsonify(success=False, error="Enter a valid phone number (7-15 digits)."), 400
        cur.execute("""
                    INSERT INTO host_profiles
                        (user_id, full_name, phone, id_proof, bio, verification_status)
                    VALUES (%s, %s, %s, %s, %s, 'pending') ON DUPLICATE KEY
                    UPDATE
                        full_name =
                    VALUES (full_name), phone =
                    VALUES (phone), id_proof =
                    VALUES (id_proof), bio =
                    VALUES (bio), verification_status = 'pending'
                    """, (
                        session["user_id"],
                        full_name,
                        phone_clean or phone,
                        id_proof,
                        experience
                    ))
        cur.execute("""
            UPDATE User_Details
            SET email = %s,
                phone = %s
            WHERE user_id = %s
        """, (
            email or None,
            phone_clean or None,
            session["user_id"]
        ))

        db.commit()
        cur.close()
        db.close()

        if request.headers.get("X-Requested-With") == "XMLHttpRequest":
            return jsonify(success=True, redirect=url_for("mainpage"))

        return redirect(url_for("mainpage"))

    cur.execute(
        "SELECT * FROM host_profiles WHERE user_id=%s",
        (session["user_id"],)
    )
    profile = cur.fetchone()
    if profile:
        cur.execute("""
            SELECT email, phone
            FROM User_Details
            WHERE user_id=%s
            LIMIT 1
        """, (session["user_id"],))
        contact_row = cur.fetchone() or {}
        profile["email"] = contact_row.get("email")
        if not profile.get("phone"):
            profile["phone"] = contact_row.get("phone")

    cur.close()
    db.close()

    return render_template("host_profile.html", profile=profile)

@app.route("/traveler_profile", methods=["GET", "POST"])
@login_required
@non_admin_required
def traveler_profile():
    db = get_db_connection()
    cur = db.cursor()

    if request.method == "POST":
        full_name = (request.form.get("full_name") or "").strip()
        phone     = (request.form.get("phone") or "").strip().replace(" ", "").replace("+", "")
        id_proof  = (request.form.get("id_proof") or "").strip()

        errors = []
        if not full_name or len(full_name) < 2:
            errors.append("Full name is required (at least 2 characters).")
        if not phone.isdigit() or not (7 <= len(phone) <= 15):
            errors.append("Enter a valid phone number (7–15 digits).")
        if not id_proof:
            errors.append("ID proof type is required.")

        if errors:
            cur.execute("SELECT * FROM traveler_profiles WHERE user_id=%s", (session["user_id"],))
            profile = cur.fetchone()
            cur.close()
            db.close()
            for err in errors:
                flash(err, "error")
            return render_template("traveler_profile.html", profile=profile)

        cur.execute("""
            INSERT INTO traveler_profiles
                (user_id, full_name, phone, id_proof, verification_status)
            VALUES (%s, %s, %s, %s, 'pending')
            ON DUPLICATE KEY UPDATE
                full_name = VALUES(full_name),
                phone = VALUES(phone),
                id_proof = VALUES(id_proof),
                verification_status = 'pending'
        """, (
            session["user_id"],
            full_name,
            phone,
            id_proof
        ))

        db.commit()
        cur.close()
        db.close()

        flash("Profile saved and submitted for verification!", "success")
        return redirect(url_for("traveler_profile"))

    cur.execute(
        "SELECT * FROM traveler_profiles WHERE user_id=%s",
        (session["user_id"],)
    )
    profile = cur.fetchone()

    cur.close()
    db.close()

    return render_template("traveler_profile.html", profile=profile)
@app.route("/create_post", methods=["GET", "POST"])
@login_required
def create_post():
    ensure_trip_feedback_schema()

    if not is_host_verified(session["user_id"]):
        return redirect(url_for("host_profile"))

    if request.method == "GET":
        return render_template("create_post.html")

    dest = (request.form.get("destination") or "").strip()
    travel_date = request.form.get("travel_date") or ""
    duration = int(request.form.get("duration") or 1)
    start_location = (request.form.get("start_location") or "").strip()
    max_people = int(request.form.get("max_people") or 1)
    price = float(request.form.get("price") or 0)
    description = (request.form.get("description") or "").strip()
    itinerary = (request.form.get("itinerary") or "").strip()

    db = get_db_connection()
    cur = db.cursor()

    cur.execute("""
        INSERT INTO travel_posts (
            user_id,
            destination,
            travel_date,
            duration,
            start_location,
            max_people,
            price,
            description,
            itinerary,
            trip_status,
            created_at
        ) VALUES (
            %s, %s, %s, %s, %s, %s, %s, %s, %s, 'open', NOW()
        )
    """, (
        session["user_id"],
        dest,
        travel_date,
        duration,
        start_location,
        max_people,
        price,
        description,
        itinerary
    ))

    db.commit()
    cur.close()
    db.close()

    return redirect(url_for("mainpage", view="explore"))

@app.route("/join/<int:post_id>", methods=["GET", "POST"])
@login_required
def join_trip(post_id):

    try:
        ensure_trip_core_schema()
    except Exception:
        abort(503)

    if not is_traveler_verified(session["user_id"]):
        return redirect(url_for("traveler_profile"))

    db = get_db_connection()
    cur = db.cursor()

    cur.execute("""
        SELECT
            tp.destination,
            tp.travel_date,
            tp.duration,
            tp.start_location,
            tp.max_people,
            tp.price,
            tp.trip_status,
            tp.user_id AS host_id,
            u.username AS host_name,
            (
                SELECT COUNT(*)
                FROM trip_members tm
                WHERE tm.post_id = tp.post_id
                  AND tm.status = 'approved'
            ) AS joined_count
        FROM travel_posts tp
        JOIN User_Details u ON tp.user_id = u.user_id
        WHERE tp.post_id = %s
    """, (post_id,))

    trip = cur.fetchone()

    if not trip or trip["trip_status"] != "open":
        cur.close()
        db.close()
        abort(403)

    spots_left = trip["max_people"] - trip["joined_count"]

    host_avg_rating = None
    host_reviews_count = 0
    host_review_samples = []
    try:
        ensure_trip_feedback_schema()
        cur.execute("""
            SELECT COUNT(*) AS review_count, AVG(rating) AS avg_rating
            FROM trip_reviews
            WHERE review_type='host'
              AND reviewee_user_id=%s
              AND COALESCE(moderation_status, 'clear') != 'removed'
        """, (trip["host_id"],))
        rate_row = cur.fetchone() or {}
        host_reviews_count = int(rate_row.get("review_count") or 0)
        if rate_row.get("avg_rating") is not None:
            host_avg_rating = round(float(rate_row["avg_rating"]), 2)

        cur.execute("""
            SELECT
                r.rating,
                r.comment,
                r.created_at,
                u.username AS reviewer_name
            FROM trip_reviews r
            JOIN User_Details u ON u.user_id = r.reviewer_id
            WHERE r.review_type='host'
              AND r.reviewee_user_id=%s
              AND COALESCE(r.moderation_status, 'clear') != 'removed'
            ORDER BY r.created_at DESC
            LIMIT 3
        """, (trip["host_id"],))
        host_review_samples = cur.fetchall()
    except Exception:
        host_avg_rating = None
        host_reviews_count = 0
        host_review_samples = []

    if request.method == "GET":
        cur.close()
        db.close()
        return render_template(
            "join_form.html",
            post_id=post_id,
            price=trip["price"],
            destination=trip["destination"],
            host_name=trip["host_name"],
            host_id=trip["host_id"],
            travel_date=trip["travel_date"],
            duration=trip["duration"],
            start_location=trip["start_location"],
            spots_left=spots_left,
            host_avg_rating=host_avg_rating,
            host_reviews_count=host_reviews_count,
            host_review_samples=host_review_samples
        )

    phone = request.form.get("contact_no", "").replace(" ", "").replace("+", "")

    if not phone.isdigit() or len(phone) < 7 or len(phone) > 15:
        cur.close()
        db.close()
        abort(400)

    cur.execute("""
        SELECT id
        FROM trip_members
        WHERE post_id = %s
          AND user_id = %s
    """, (post_id, session["user_id"]))

    if cur.fetchone():
        cur.close()
        db.close()
        return redirect(url_for("mainpage", view="joined"))

    try:
        cur.execute("""
            INSERT INTO trip_members
            (post_id,
             user_id,
             member_name,
             contact_no,
             address,
             language,
             amount_due,
             status)
            VALUES (%s,%s,%s,%s,%s,%s,%s,'pending')
        """, (
            post_id,
            session["user_id"],
            request.form.get("member_name"),
            request.form.get("contact_no"),
            request.form.get("address"),
            request.form.get("language"),
            trip["price"]
        ))
    except pymysql.err.IntegrityError:
        cur.close()
        db.close()
        return redirect(url_for("mainpage", view="joined"))

    db.commit()
    cur.close()
    db.close()

    return redirect(url_for("mainpage", view="joined"))

def get_or_create_conversation(user1, user2):
    db = get_db_connection()
    cur = db.cursor()

    # Always store smaller ID first (avoids duplicates)
    u1, u2 = _normalize_pair(user1, user2)

    cur.execute("""
        SELECT id FROM private_conversations
        WHERE user1_id=%s AND user2_id=%s
    """, (u1, u2))

    convo = cur.fetchone()

    if convo:
        cur.close()
        db.close()
        return convo["id"]

    try:
        cur.execute("""
            INSERT INTO private_conversations (user1_id, user2_id)
            VALUES (%s, %s)
        """, (u1, u2))
    except pymysql.err.IntegrityError:
        cur.execute("""
            SELECT id FROM private_conversations
            WHERE user1_id=%s AND user2_id=%s
        """, (u1, u2))
        existing = cur.fetchone()
        cur.close()
        db.close()
        if existing:
            return existing["id"]
        raise

    db.commit()
    convo_id = cur.lastrowid
    cur.close()
    db.close()
    return convo_id

@app.route("/chat/private/<int:user_id>")
@login_required
def private_chat(user_id):

    if user_id == session["user_id"]:
        abort(400)

    ensure_chat_schema()

    db = get_db_connection()
    cur = db.cursor()

    if not _has_message_relationship(cur, session["user_id"], user_id):
        cur.close()
        db.close()
        abort(403)

    convo_id = get_or_create_conversation(session["user_id"], user_id)

    cur.execute("""
        SELECT pm.id,
               pm.message,
               pm.message_type,
               pm.created_at,
               pm.edited_at,
               pm.is_flagged,
               pm.reply_to_id,
               rp.message AS reply_to_text,
               pm.attachment_path,
               pm.attachment_name,
               pm.attachment_type,
               pm.attachment_size,
               u.username,
               pm.sender_id,
               COALESCE(rc.delivered_count, 0) AS delivered_count,
               COALESCE(rc.seen_count, 0) AS seen_count,
               COALESCE(rc.recipient_count, 0) AS recipient_count
        FROM private_messages pm
        JOIN User_Details u ON u.user_id = pm.sender_id
        LEFT JOIN private_messages rp
          ON rp.id = pm.reply_to_id
        LEFT JOIN (
            SELECT
                message_id,
                SUM(CASE WHEN delivered_at IS NOT NULL THEN 1 ELSE 0 END) AS delivered_count,
                SUM(CASE WHEN seen_at IS NOT NULL THEN 1 ELSE 0 END) AS seen_count,
                COUNT(*) AS recipient_count
            FROM chat_message_receipts
            WHERE channel_type='private'
            GROUP BY message_id
        ) rc ON rc.message_id = pm.id
        WHERE pm.conversation_id = %s
          AND pm.deleted_at IS NULL
        ORDER BY pm.id DESC
        LIMIT %s
    """, (convo_id, CHAT_PAGE_SIZE))
    latest = cur.fetchall()
    messages = list(reversed(latest))
    message_ids = [int(m["id"]) for m in messages if m.get("id")]
    reaction_map = _fetch_reaction_map(cur, "private", message_ids)
    starred_map = _fetch_starred_map(cur, "private", message_ids, session["user_id"])
    for m in messages:
        m["reactions"] = reaction_map.get(int(m["id"]), {})
        m["starred"] = int(starred_map.get(int(m["id"]), 0))
        m["attachment_url"] = _public_attachment_url(m.get("attachment_path"))
        m["receipt_status"] = _receipt_status(
            m.get("delivered_count"),
            m.get("seen_count"),
            m.get("recipient_count")
        )

    cur.execute("""
        SELECT COUNT(*) AS total_count
        FROM private_messages
        WHERE conversation_id = %s
          AND deleted_at IS NULL
    """, (convo_id,))
    count_row = cur.fetchone()
    total_count = int(count_row["total_count"] if count_row else 0)
    has_older = total_count > len(messages)

    cur.execute("""
        SELECT username, role
        FROM User_Details
        WHERE user_id = %s
    """, (user_id,))
    other_user = cur.fetchone()
    other_username = other_user["username"] if other_user else "User"
    other_user_role = (other_user.get("role") or "").lower() if other_user else "user"

    cur.execute("""
        SELECT is_support,
               support_status,
               support_priority,
               assigned_admin_id,
               support_opened_by
        FROM private_conversations
        WHERE id=%s
    """, (convo_id,))
    support_row = cur.fetchone() or {}

    cur.execute("""
        SELECT last_read_at
        FROM private_chat_reads
        WHERE conversation_id=%s
          AND user_id=%s
        LIMIT 1
    """, (convo_id, session["user_id"]))
    read_row = cur.fetchone() or {}

    cur.execute("""
        SELECT pinned, archived, starred, muted_until, draft_text
        FROM chat_channel_user_state
        WHERE channel_type='private'
          AND channel_id=%s
          AND user_id=%s
        LIMIT 1
    """, (convo_id, session["user_id"]))
    convo_state = cur.fetchone() or {}
    if not convo_state:
        cur.execute("""
            SELECT pinned, archived, starred, muted_until, draft_text
            FROM conversation_user_state
            WHERE conversation_id=%s
              AND user_id=%s
            LIMIT 1
        """, (convo_id, session["user_id"]))
        convo_state = cur.fetchone() or {}

    cur.execute("""
        SELECT is_online, last_seen_at
        FROM user_presence
        WHERE user_id=%s
        LIMIT 1
    """, (user_id,))
    presence_row = cur.fetchone() or {}

    cur.close()
    db.close()

    return render_template(
        "private_chat.html",
        conversation_id=convo_id,
        messages=messages,
        has_older=has_older,
        other_user_id=user_id,
        other_username=other_username,
        other_user_role=other_user_role,
        is_support=bool(support_row.get("is_support")),
        support_status=support_row.get("support_status") or "open",
        support_priority=support_row.get("support_priority") or "normal",
        support_assigned_admin_id=support_row.get("assigned_admin_id"),
        support_opened_by=support_row.get("support_opened_by"),
        last_read_at=read_row.get("last_read_at"),
        conversation_pinned=int(convo_state.get("pinned") or 0),
        conversation_archived=int(convo_state.get("archived") or 0),
        conversation_starred=int(convo_state.get("starred") or 0),
        conversation_muted_until=convo_state.get("muted_until"),
        conversation_draft=convo_state.get("draft_text") or "",
        other_online=int(presence_row.get("is_online") or 0),
        other_last_seen_at=presence_row.get("last_seen_at")
    )

@app.route("/api/chat/private/<int:conversation_id>/messages")
@login_required
def private_messages_page(conversation_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    before_id = _parse_int(request.args.get("before_id"))
    if before_id is None:
        before_id = _parse_int(request.args.get("before"))
    limit = _parse_int(request.args.get("limit")) or CHAT_PAGE_SIZE
    limit = max(1, min(limit, 100))

    db = get_db_connection()
    cur = db.cursor()

    allowed, _ = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)

    q = (request.args.get("q") or "").strip().lower()
    sender_id = _parse_int(request.args.get("sender_id"))
    date_from = _parse_date_only(request.args.get("date_from"))
    date_to = _parse_date_only(request.args.get("date_to"))

    conditions = ["pm.conversation_id=%s", "pm.deleted_at IS NULL"]
    args = [conversation_id]
    if before_id:
        conditions.append("pm.id < %s")
        args.append(before_id)
    if q:
        conditions.append("(LOWER(pm.message) LIKE %s OR LOWER(COALESCE(pm.attachment_name,'')) LIKE %s)")
        like_q = f"%{q}%"
        args.extend([like_q, like_q])
    if sender_id:
        conditions.append("pm.sender_id=%s")
        args.append(sender_id)
    if date_from:
        conditions.append("DATE(pm.created_at) >= %s")
        args.append(date_from.strftime("%Y-%m-%d"))
    if date_to:
        conditions.append("DATE(pm.created_at) <= %s")
        args.append(date_to.strftime("%Y-%m-%d"))

    where_sql = " AND ".join(conditions)
    cur.execute(f"""
        SELECT pm.id,
               pm.message,
               pm.message_type,
               pm.created_at,
               pm.edited_at,
               pm.is_flagged,
               pm.moderation_status,
               pm.sender_id,
               pm.reply_to_id,
               rp.message AS reply_to_text,
               pm.attachment_path,
               pm.attachment_name,
               pm.attachment_type,
               pm.attachment_size,
               u.username
        FROM private_messages pm
        JOIN User_Details u ON u.user_id = pm.sender_id
        LEFT JOIN private_messages rp
          ON rp.id = pm.reply_to_id
        WHERE {where_sql}
        ORDER BY pm.id DESC
        LIMIT %s
    """, (*args, limit))

    rows = list(reversed(cur.fetchall()))
    message_ids = [int(r["id"]) for r in rows if r.get("id")]
    reaction_map = _fetch_reaction_map(cur, "private", message_ids)
    receipt_map = _fetch_receipt_counts(cur, "private", message_ids)
    star_map = _fetch_starred_map(cur, "private", message_ids, user_id)

    has_more = False
    next_before_id = None
    if rows:
        oldest_id = int(rows[0]["id"])
        next_before_id = oldest_id
        more_conditions = [c for c in conditions if not c.startswith("pm.id <")]
        more_args = [a for a in args[:]]
        if before_id:
            # remove original before_id arg for "more" check
            more_args = [conversation_id]
            if q:
                like_q = f"%{q}%"
                more_args.extend([like_q, like_q])
            if sender_id:
                more_args.append(sender_id)
            if date_from:
                more_args.append(date_from.strftime("%Y-%m-%d"))
            if date_to:
                more_args.append(date_to.strftime("%Y-%m-%d"))
        more_conditions.append("pm.id < %s")
        more_args.append(oldest_id)
        cur.execute(f"""
            SELECT 1
            FROM private_messages pm
            WHERE {" AND ".join(more_conditions)}
            LIMIT 1
        """, tuple(more_args))
        has_more = bool(cur.fetchone())

    cur.close()
    db.close()

    return jsonify({
        "messages": [
            {
                "message": row["message"],
                "message_type": row.get("message_type") or "text",
                "created_at": _dt_to_str(row["created_at"]),
                "edited_at": _dt_to_str(row["edited_at"]),
                "is_flagged": int(row.get("is_flagged") or 0),
                "moderation_status": row.get("moderation_status") or "clear",
                "id": row["id"],
                "sender_id": row["sender_id"],
                "username": row["username"],
                "reply_to_id": row.get("reply_to_id"),
                "reply_to_text": row.get("reply_to_text"),
                "attachment_path": row.get("attachment_path"),
                "attachment_name": row.get("attachment_name"),
                "attachment_type": row.get("attachment_type"),
                "attachment_size": row.get("attachment_size"),
                "attachment_url": _public_attachment_url(row.get("attachment_path")),
                "reactions": reaction_map.get(int(row["id"]), {}),
                "starred": int(star_map.get(int(row["id"]), 0)),
                "delivered_count": receipt_map.get(int(row["id"]), {}).get("delivered_count", 0),
                "seen_count": receipt_map.get(int(row["id"]), {}).get("seen_count", 0),
                "recipient_count": receipt_map.get(int(row["id"]), {}).get("recipient_count", 0),
                "receipt_status": _receipt_status(
                    receipt_map.get(int(row["id"]), {}).get("delivered_count", 0),
                    receipt_map.get(int(row["id"]), {}).get("seen_count", 0),
                    receipt_map.get(int(row["id"]), {}).get("recipient_count", 0)
                )
            }
            for row in rows
        ],
        "has_more": has_more,
        "next_before_id": next_before_id
    })

@app.route("/api/chat/group/<int:post_id>/messages")
@login_required
def group_messages_page(post_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    before_id = _parse_int(request.args.get("before_id"))
    if before_id is None:
        before_id = _parse_int(request.args.get("before"))
    limit = _parse_int(request.args.get("limit")) or CHAT_PAGE_SIZE
    limit = max(1, min(limit, 100))

    db = get_db_connection()
    cur = db.cursor()

    if not _is_user_in_trip_chat(cur, post_id, user_id):
        cur.close()
        db.close()
        abort(403)

    q = (request.args.get("q") or "").strip().lower()
    sender_id = _parse_int(request.args.get("sender_id"))
    date_from = _parse_date_only(request.args.get("date_from"))
    date_to = _parse_date_only(request.args.get("date_to"))

    conditions = ["tm.post_id=%s", "tm.deleted_at IS NULL"]
    args = [post_id]
    if before_id:
        conditions.append("tm.id < %s")
        args.append(before_id)
    if q:
        conditions.append("(LOWER(tm.message) LIKE %s OR LOWER(COALESCE(tm.attachment_name,'')) LIKE %s)")
        like_q = f"%{q}%"
        args.extend([like_q, like_q])
    if sender_id:
        conditions.append("tm.user_id=%s")
        args.append(sender_id)
    if date_from:
        conditions.append("DATE(tm.created_at) >= %s")
        args.append(date_from.strftime("%Y-%m-%d"))
    if date_to:
        conditions.append("DATE(tm.created_at) <= %s")
        args.append(date_to.strftime("%Y-%m-%d"))

    where_sql = " AND ".join(conditions)
    cur.execute(f"""
        SELECT tm.id,
               tm.message,
               tm.message_type,
               tm.created_at,
               tm.edited_at,
               tm.is_flagged,
               tm.moderation_status,
               tm.user_id,
               tm.reply_to_id,
               rp.message AS reply_to_text,
               tm.attachment_path,
               tm.attachment_name,
               tm.attachment_type,
               tm.attachment_size,
               u.username
        FROM trip_messages tm
        JOIN User_Details u ON u.user_id = tm.user_id
        LEFT JOIN trip_messages rp
          ON rp.id = tm.reply_to_id
        WHERE {where_sql}
        ORDER BY tm.id DESC
        LIMIT %s
    """, (*args, limit))

    rows = list(reversed(cur.fetchall()))
    message_ids = [int(r["id"]) for r in rows if r.get("id")]
    reaction_map = _fetch_reaction_map(cur, "group", message_ids)
    receipt_map = _fetch_receipt_counts(cur, "group", message_ids)
    star_map = _fetch_starred_map(cur, "group", message_ids, user_id)

    has_more = False
    next_before_id = None
    if rows:
        oldest_id = int(rows[0]["id"])
        next_before_id = oldest_id
        more_conditions = [c for c in conditions if not c.startswith("tm.id <")]
        more_args = [post_id]
        if q:
            like_q = f"%{q}%"
            more_args.extend([like_q, like_q])
        if sender_id:
            more_args.append(sender_id)
        if date_from:
            more_args.append(date_from.strftime("%Y-%m-%d"))
        if date_to:
            more_args.append(date_to.strftime("%Y-%m-%d"))
        more_conditions.append("tm.id < %s")
        more_args.append(oldest_id)
        cur.execute(f"""
            SELECT 1
            FROM trip_messages tm
            WHERE {" AND ".join(more_conditions)}
            LIMIT 1
        """, tuple(more_args))
        has_more = bool(cur.fetchone())

    cur.close()
    db.close()

    return jsonify({
        "messages": [
            {
                "message": row["message"],
                "message_type": row.get("message_type") or "text",
                "created_at": _dt_to_str(row["created_at"]),
                "edited_at": _dt_to_str(row["edited_at"]),
                "is_flagged": int(row.get("is_flagged") or 0),
                "moderation_status": row.get("moderation_status") or "clear",
                "id": row["id"],
                "user_id": row["user_id"],
                "username": row["username"],
                "reply_to_id": row.get("reply_to_id"),
                "reply_to_text": row.get("reply_to_text"),
                "attachment_path": row.get("attachment_path"),
                "attachment_name": row.get("attachment_name"),
                "attachment_type": row.get("attachment_type"),
                "attachment_size": row.get("attachment_size"),
                "attachment_url": _public_attachment_url(row.get("attachment_path")),
                "reactions": reaction_map.get(int(row["id"]), {}),
                "starred": int(star_map.get(int(row["id"]), 0)),
                "delivered_count": receipt_map.get(int(row["id"]), {}).get("delivered_count", 0),
                "seen_count": receipt_map.get(int(row["id"]), {}).get("seen_count", 0),
                "recipient_count": receipt_map.get(int(row["id"]), {}).get("recipient_count", 0),
                "receipt_status": _receipt_status(
                    receipt_map.get(int(row["id"]), {}).get("delivered_count", 0),
                    receipt_map.get(int(row["id"]), {}).get("seen_count", 0),
                    receipt_map.get(int(row["id"]), {}).get("recipient_count", 0)
                )
            }
            for row in rows
        ],
        "has_more": has_more,
        "next_before_id": next_before_id
    })

def _save_chat_upload(cur, owner_id, channel_type, channel_id, file_storage):
    if not file_storage:
        return None, "No file selected"
    original_name = secure_filename(file_storage.filename or "")
    if not original_name:
        return None, "Invalid filename"
    if not _is_allowed_attachment(original_name, file_storage.mimetype):
        return None, "File type not allowed"

    file_storage.stream.seek(0, os.SEEK_END)
    file_size = int(file_storage.stream.tell() or 0)
    file_storage.stream.seek(0)
    if file_size <= 0:
        return None, "Empty file"
    if file_size > MAX_ATTACHMENT_SIZE:
        return None, "Attachment is too large"

    folder = os.path.join(_ensure_upload_root(), channel_type, str(channel_id))
    os.makedirs(folder, exist_ok=True)
    ext = os.path.splitext(original_name)[1].lower()
    safe_name = f"{uuid.uuid4().hex}{ext}"
    abs_path = os.path.join(folder, safe_name)
    file_storage.save(abs_path)
    is_clean, _scan_reason = _scan_attachment(abs_path)
    rel_path = os.path.relpath(abs_path, app.root_path).replace("\\", "/")
    cur.execute("""
        INSERT INTO chat_uploads
            (owner_id, channel_type, channel_id, rel_path, original_name, mime_type, file_size, is_scanned, is_malicious, created_at)
        VALUES (%s, %s, %s, %s, %s, %s, %s, 1, %s, NOW())
    """, (
        owner_id,
        channel_type,
        channel_id,
        rel_path,
        original_name[:255],
        (file_storage.mimetype or "")[:120],
        file_size,
        0 if is_clean else 1
    ))
    upload_id = int(cur.lastrowid or 0)
    return {
        "upload_id": upload_id,
        "name": original_name,
        "size": file_size,
        "mime_type": file_storage.mimetype or "",
        "is_malicious": 0 if is_clean else 1,
        "attachment_url": _public_attachment_url(rel_path)
    }, None

@app.route("/chat/attachment/<path:rel_path>")
@login_required
def download_chat_attachment(rel_path):
    ensure_chat_schema()
    safe_rel = os.path.normpath((rel_path or "").strip()).replace("\\", "/")
    if not safe_rel or safe_rel in {".", ".."}:
        abort(404)
    if safe_rel.startswith("../") or safe_rel.startswith("/"):
        abort(404)
    root_prefix = CHAT_UPLOAD_ROOT.replace("\\", "/").strip("/")
    allowed_prefixes = (root_prefix + "/", f"static/{root_prefix}/")
    if not safe_rel.startswith(allowed_prefixes):
        abort(404)

    abs_path = os.path.join(app.root_path, safe_rel)
    if not os.path.isfile(abs_path):
        abort(404)

    user_id = session["user_id"]
    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
        SELECT channel_type, channel_id, original_name, mime_type, is_malicious
        FROM chat_uploads
        WHERE rel_path=%s
        ORDER BY id DESC
        LIMIT 1
    """, (safe_rel,))
    row = cur.fetchone()
    if not row or int(row.get("is_malicious") or 0) == 1:
        cur.close()
        db.close()
        abort(404)

    channel_type = (row.get("channel_type") or "").strip().lower()
    channel_id = int(row.get("channel_id") or 0)
    allowed = False
    if channel_type == "private":
        allowed, _ = _can_access_private_conversation(cur, channel_id, user_id)
    elif channel_type == "group":
        allowed = _is_user_in_trip_chat(cur, channel_id, user_id)

    filename = row.get("original_name") or os.path.basename(abs_path)
    mime_type = row.get("mime_type") or "application/octet-stream"
    cur.close()
    db.close()

    if not allowed:
        abort(403)

    return send_file(
        abs_path,
        mimetype=mime_type,
        as_attachment=True,
        download_name=filename,
        conditional=True,
        max_age=0
    )

@app.route("/api/chat/private/<int:conversation_id>/upload", methods=["POST"])
@login_required
def upload_private_attachment(conversation_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    if not _redis_rate_ok_with_ip(user_id, f"upload:private:{conversation_id}", request.remote_addr):
        return jsonify({"ok": False, "error": "Upload rate limit exceeded"}), 429

    db = get_db_connection()
    cur = db.cursor()
    allowed, _ = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)
    payload, err = _save_chat_upload(cur, user_id, "private", conversation_id, request.files.get("file"))
    if err:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": err}), 400
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True, **payload})

@app.route("/api/chat/group/<int:post_id>/upload", methods=["POST"])
@login_required
def upload_group_attachment(post_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    if not _redis_rate_ok_with_ip(user_id, f"upload:group:{post_id}", request.remote_addr):
        return jsonify({"ok": False, "error": "Upload rate limit exceeded"}), 429

    db = get_db_connection()
    cur = db.cursor()
    if not _is_user_in_trip_chat(cur, post_id, user_id):
        cur.close()
        db.close()
        abort(403)
    payload, err = _save_chat_upload(cur, user_id, "group", post_id, request.files.get("file"))
    if err:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": err}), 400
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True, **payload})

def _toggle_message_reaction(cur, channel_type, channel_id, message_id, user_id, reaction):
    if reaction not in CHAT_ALLOWED_REACTIONS:
        return None, "Reaction not allowed"
    if channel_type == "private":
        cur.execute("""
            SELECT 1
            FROM private_messages
            WHERE id=%s
              AND conversation_id=%s
              AND deleted_at IS NULL
            LIMIT 1
        """, (message_id, channel_id))
    else:
        cur.execute("""
            SELECT 1
            FROM trip_messages
            WHERE id=%s
              AND post_id=%s
              AND deleted_at IS NULL
            LIMIT 1
        """, (message_id, channel_id))
    if not cur.fetchone():
        return None, "Message not found"

    cur.execute("""
        SELECT 1
        FROM chat_reactions
        WHERE channel_type=%s
          AND message_id=%s
          AND user_id=%s
          AND reaction=%s
        LIMIT 1
    """, (channel_type, message_id, user_id, reaction))
    exists = bool(cur.fetchone())
    if exists:
        cur.execute("""
            DELETE FROM chat_reactions
            WHERE channel_type=%s
              AND message_id=%s
              AND user_id=%s
              AND reaction=%s
        """, (channel_type, message_id, user_id, reaction))
    else:
        cur.execute("""
            INSERT INTO chat_reactions (channel_type, message_id, user_id, reaction, created_at)
            VALUES (%s, %s, %s, %s, NOW())
        """, (channel_type, message_id, user_id, reaction))
    reaction_map = _fetch_reaction_map(cur, channel_type, [message_id]).get(int(message_id), {})
    return {"added": not exists, "reactions": reaction_map}, None

@app.route("/api/chat/private/<int:conversation_id>/messages/<int:message_id>/reaction", methods=["POST"])
@login_required
def private_reaction(conversation_id, message_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    reaction = (request.form.get("reaction") or "").strip()
    db = get_db_connection()
    cur = db.cursor()
    allowed, _ = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)
    payload, err = _toggle_message_reaction(cur, "private", conversation_id, message_id, user_id, reaction)
    if err:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": err}), 400
    db.commit()
    cur.close()
    db.close()
    socketio.emit("private_reaction_updated", {
        "conversation_id": conversation_id,
        "message_id": message_id,
        "reactions": payload["reactions"]
    }, room=f"private_{conversation_id}")
    return jsonify({"ok": True, **payload})

@app.route("/api/chat/group/<int:post_id>/messages/<int:message_id>/reaction", methods=["POST"])
@login_required
def group_reaction(post_id, message_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    reaction = (request.form.get("reaction") or "").strip()
    db = get_db_connection()
    cur = db.cursor()
    if not _is_user_in_trip_chat(cur, post_id, user_id):
        cur.close()
        db.close()
        abort(403)
    payload, err = _toggle_message_reaction(cur, "group", post_id, message_id, user_id, reaction)
    if err:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": err}), 400
    db.commit()
    cur.close()
    db.close()
    socketio.emit("group_reaction_updated", {
        "trip_id": post_id,
        "message_id": message_id,
        "reactions": payload["reactions"]
    }, room=str(post_id))
    return jsonify({"ok": True, **payload})

def _toggle_star(cur, channel_type, channel_id, message_id, user_id):
    if channel_type == "private":
        cur.execute("""
            SELECT 1
            FROM private_messages
            WHERE id=%s
              AND conversation_id=%s
              AND deleted_at IS NULL
            LIMIT 1
        """, (message_id, channel_id))
    else:
        cur.execute("""
            SELECT 1
            FROM trip_messages
            WHERE id=%s
              AND post_id=%s
              AND deleted_at IS NULL
            LIMIT 1
        """, (message_id, channel_id))
    if not cur.fetchone():
        return None, "Message not found"
    cur.execute("""
        SELECT 1
        FROM chat_message_stars
        WHERE channel_type=%s
          AND message_id=%s
          AND user_id=%s
        LIMIT 1
    """, (channel_type, message_id, user_id))
    exists = bool(cur.fetchone())
    if exists:
        cur.execute("""
            DELETE FROM chat_message_stars
            WHERE channel_type=%s
              AND message_id=%s
              AND user_id=%s
        """, (channel_type, message_id, user_id))
    else:
        cur.execute("""
            INSERT INTO chat_message_stars (channel_type, message_id, user_id, created_at)
            VALUES (%s, %s, %s, NOW())
        """, (channel_type, message_id, user_id))
    return {"starred": 0 if exists else 1}, None

@app.route("/api/chat/private/<int:conversation_id>/messages/<int:message_id>/star", methods=["POST"])
@login_required
def star_private_message(conversation_id, message_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    db = get_db_connection()
    cur = db.cursor()
    allowed, _ = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)
    payload, err = _toggle_star(cur, "private", conversation_id, message_id, user_id)
    if err:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": err}), 400
    db.commit()
    cur.close()
    db.close()
    socketio.emit("private_star_updated", {
        "conversation_id": conversation_id,
        "message_id": message_id,
        "starred": payload["starred"],
        "user_id": user_id
    }, room=f"private_{conversation_id}")
    return jsonify({"ok": True, **payload})

@app.route("/api/chat/group/<int:post_id>/messages/<int:message_id>/star", methods=["POST"])
@login_required
def star_group_message(post_id, message_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    db = get_db_connection()
    cur = db.cursor()
    if not _is_user_in_trip_chat(cur, post_id, user_id):
        cur.close()
        db.close()
        abort(403)
    payload, err = _toggle_star(cur, "group", post_id, message_id, user_id)
    if err:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": err}), 400
    db.commit()
    cur.close()
    db.close()
    socketio.emit("group_star_updated", {
        "trip_id": post_id,
        "message_id": message_id,
        "starred": payload["starred"],
        "user_id": user_id
    }, room=str(post_id))
    return jsonify({"ok": True, **payload})

@app.route("/api/chat/private/<int:conversation_id>/state", methods=["GET", "POST"])
@login_required
def private_chat_state(conversation_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    db = get_db_connection()
    cur = db.cursor()
    allowed, _ = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)
    if request.method == "POST":
        pinned = _parse_int(request.form.get("pinned"))
        archived = _parse_int(request.form.get("archived"))
        starred = _parse_int(request.form.get("starred"))
        mute_minutes = _parse_int(request.form.get("mute_minutes"))
        muted_until = None
        if mute_minutes and mute_minutes > 0:
            muted_until = datetime.utcnow() + timedelta(minutes=min(10080, mute_minutes))
        _save_channel_state(
            cur,
            "private",
            conversation_id,
            user_id,
            pinned=None if pinned is None else int(bool(pinned)),
            archived=None if archived is None else int(bool(archived)),
            starred=None if starred is None else int(bool(starred)),
            muted_until=muted_until
        )
        db.commit()
    state = _fetch_channel_state(cur, "private", conversation_id, user_id)
    cur.close()
    db.close()
    return jsonify({
        "ok": True,
        "pinned": int(state.get("pinned") or 0),
        "archived": int(state.get("archived") or 0),
        "starred": int(state.get("starred") or 0),
        "muted_until": _dt_to_str(state.get("muted_until")),
        "draft_text": state.get("draft_text") or ""
    })

@app.route("/api/chat/group/<int:post_id>/state", methods=["GET", "POST"])
@login_required
def group_chat_state(post_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    db = get_db_connection()
    cur = db.cursor()
    if not _is_user_in_trip_chat(cur, post_id, user_id):
        cur.close()
        db.close()
        abort(403)
    if request.method == "POST":
        pinned = _parse_int(request.form.get("pinned"))
        archived = _parse_int(request.form.get("archived"))
        starred = _parse_int(request.form.get("starred"))
        mute_minutes = _parse_int(request.form.get("mute_minutes"))
        muted_until = None
        if mute_minutes and mute_minutes > 0:
            muted_until = datetime.utcnow() + timedelta(minutes=min(10080, mute_minutes))
        _save_channel_state(
            cur,
            "group",
            post_id,
            user_id,
            pinned=None if pinned is None else int(bool(pinned)),
            archived=None if archived is None else int(bool(archived)),
            starred=None if starred is None else int(bool(starred)),
            muted_until=muted_until
        )
        db.commit()
    state = _fetch_channel_state(cur, "group", post_id, user_id)
    cur.close()
    db.close()
    return jsonify({
        "ok": True,
        "pinned": int(state.get("pinned") or 0),
        "archived": int(state.get("archived") or 0),
        "starred": int(state.get("starred") or 0),
        "muted_until": _dt_to_str(state.get("muted_until")),
        "draft_text": state.get("draft_text") or ""
    })

@app.route("/api/chat/private/<int:conversation_id>/draft", methods=["POST"])
@login_required
def save_private_draft(conversation_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    draft_text = (request.form.get("draft_text") or "")[:2000]
    db = get_db_connection()
    cur = db.cursor()
    allowed, _ = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)
    _save_channel_state(cur, "private", conversation_id, user_id, draft_text=draft_text)
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True})

@app.route("/api/chat/group/<int:post_id>/draft", methods=["POST"])
@login_required
def save_group_draft(post_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    draft_text = (request.form.get("draft_text") or "")[:2000]
    db = get_db_connection()
    cur = db.cursor()
    if not _is_user_in_trip_chat(cur, post_id, user_id):
        cur.close()
        db.close()
        abort(403)
    _save_channel_state(cur, "group", post_id, user_id, draft_text=draft_text)
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True})

@app.route("/api/chat/users/<int:target_user_id>/block", methods=["POST"])
@login_required
def block_or_mute_user(target_user_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    if int(target_user_id) == int(user_id):
        return jsonify({"ok": False, "error": "Cannot block yourself"}), 400
    action = (request.form.get("action") or "block").strip().lower()
    reason = (request.form.get("reason") or "").strip()[:255]
    db = get_db_connection()
    cur = db.cursor()
    if action in {"block", "mute"}:
        cur.execute("""
            INSERT INTO user_blocks (blocker_id, blocked_id, muted, reason, created_at)
            VALUES (%s, %s, %s, %s, NOW())
            ON DUPLICATE KEY UPDATE
                muted=VALUES(muted),
                reason=VALUES(reason),
                created_at=NOW()
        """, (user_id, target_user_id, 1 if action == "mute" else 0, reason))
    elif action in {"unblock", "unmute"}:
        cur.execute("""
            DELETE FROM user_blocks
            WHERE blocker_id=%s
              AND blocked_id=%s
        """, (user_id, target_user_id))
    else:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Invalid action"}), 400
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True, "action": action})

@app.route("/api/chat/users/<int:target_user_id>/report", methods=["POST"])
@login_required
def report_user_profile(target_user_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    if int(target_user_id) == int(user_id):
        return jsonify({"ok": False, "error": "Cannot report yourself"}), 400
    reason = (request.form.get("reason") or "abuse").strip()[:255]
    details = (request.form.get("details") or "").strip()[:2000]
    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
        INSERT INTO user_reports
            (reporter_id, reported_user_id, reason, details, status, created_at)
        VALUES (%s, %s, %s, %s, 'open', NOW())
    """, (user_id, target_user_id, reason, details))
    report_id = int(cur.lastrowid or 0)
    cur.execute("""
        SELECT user_id
        FROM User_Details
        WHERE role='admin'
          AND is_active=1
    """)
    for admin_row in cur.fetchall():
        _create_notification(
            cur,
            int(admin_row["user_id"]),
            "User profile reported",
            f"Report #{report_id} submitted for user #{target_user_id}.",
            ntype="moderation",
            send_email=False
        )
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True, "report_id": report_id})

@app.route("/api/chat/private/<int:conversation_id>/read", methods=["POST"])
@login_required
def mark_private_read(conversation_id):
    ensure_chat_schema()
    user_id = session["user_id"]

    db = get_db_connection()
    cur = db.cursor()

    allowed, _ = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)

    mark_private_chat_read(cur, conversation_id, user_id)
    _save_channel_state(cur, "private", conversation_id, user_id, touch_seen=True)
    _emit_receipt_snapshot(cur, "private", conversation_id, f"private_{conversation_id}", "private_receipts_updated")
    db.commit()
    cur.close()
    db.close()

    return jsonify({"ok": True})

@app.route("/api/chat/group/<int:post_id>/read", methods=["POST"])
@login_required
def mark_group_read(post_id):
    ensure_chat_schema()
    user_id = session["user_id"]

    db = get_db_connection()
    cur = db.cursor()

    if not _is_user_in_trip_chat(cur, post_id, user_id):
        cur.close()
        db.close()
        abort(403)

    mark_trip_chat_read(cur, post_id, user_id)
    _save_channel_state(cur, "group", post_id, user_id, touch_seen=True)
    _emit_receipt_snapshot(cur, "group", post_id, str(post_id), "group_receipts_updated")
    db.commit()
    cur.close()
    db.close()

    return jsonify({"ok": True})

@app.route("/api/chat/private/<int:conversation_id>/messages/<int:message_id>/edit", methods=["POST"])
@login_required
def edit_private_message(conversation_id, message_id):
    ensure_chat_schema()
    new_message = _normalize_message(request.form.get("message", ""))
    if not _is_valid_message(new_message):
        return jsonify({"ok": False, "error": "Invalid message"}), 400

    user_id = session["user_id"]
    db = get_db_connection()
    cur = db.cursor()

    allowed, _ = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)

    if not _message_is_from_sender(cur, "private_messages", message_id, "sender_id", user_id):
        cur.close()
        db.close()
        abort(403)

    cur.execute("""
        UPDATE private_messages
        SET message=%s,
            edited_at=NOW()
        WHERE id=%s
          AND conversation_id=%s
          AND deleted_at IS NULL
    """, (new_message, message_id, conversation_id))
    if not cur.rowcount:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Message not found"}), 404

    cur.execute("""
        SELECT created_at, edited_at
        FROM private_messages
        WHERE id=%s
    """, (message_id,))
    row = cur.fetchone() or {}

    db.commit()
    cur.close()
    db.close()

    payload = {
        "conversation_id": conversation_id,
        "id": message_id,
        "message": new_message,
        "created_at": _dt_to_str(row.get("created_at")),
        "edited_at": _dt_to_str(row.get("edited_at"))
    }
    socketio.emit("private_message_updated", payload, room=f"private_{conversation_id}")
    return jsonify({"ok": True, **payload})

@app.route("/api/chat/private/<int:conversation_id>/messages/<int:message_id>/delete", methods=["POST"])
@login_required
def delete_private_message(conversation_id, message_id):
    ensure_chat_schema()
    user_id = session["user_id"]

    db = get_db_connection()
    cur = db.cursor()

    allowed, _ = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)

    if not _message_is_from_sender(cur, "private_messages", message_id, "sender_id", user_id):
        cur.close()
        db.close()
        abort(403)

    cur.execute("""
        UPDATE private_messages
        SET deleted_at=NOW()
        WHERE id=%s
          AND conversation_id=%s
          AND deleted_at IS NULL
    """, (message_id, conversation_id))
    if not cur.rowcount:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Message not found"}), 404

    db.commit()
    cur.close()
    db.close()

    payload = {"conversation_id": conversation_id, "id": message_id}
    socketio.emit("private_message_deleted", payload, room=f"private_{conversation_id}")
    return jsonify({"ok": True, **payload})

@app.route("/api/chat/private/<int:conversation_id>/messages/<int:message_id>/flag", methods=["POST"])
@login_required
def flag_private_message(conversation_id, message_id):
    ensure_chat_schema()
    user_id = session["user_id"]

    db = get_db_connection()
    cur = db.cursor()

    allowed, _ = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)

    cur.execute("""
        SELECT sender_id
        FROM private_messages
        WHERE id=%s
          AND conversation_id=%s
          AND deleted_at IS NULL
    """, (message_id, conversation_id))
    row = cur.fetchone()
    if not row:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Message not found"}), 404

    if int(row["sender_id"]) == int(user_id):
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Cannot report your own message"}), 400

    cur.execute("""
        UPDATE private_messages
        SET is_flagged=1,
            moderation_status='flagged'
        WHERE id=%s
          AND conversation_id=%s
    """, (message_id, conversation_id))

    cur.execute("""
        SELECT user_id
        FROM User_Details
        WHERE role='admin'
          AND is_active=1
    """)
    for admin_row in cur.fetchall():
        _create_notification(
            cur,
            int(admin_row["user_id"]),
            "Flagged private message",
            f"Conversation #{conversation_id}, message #{message_id} was reported.",
            ntype="moderation",
            send_email=False
        )

    db.commit()
    cur.close()
    db.close()

    payload = {"conversation_id": conversation_id, "id": message_id, "is_flagged": 1}
    socketio.emit("private_message_flagged", payload, room=f"private_{conversation_id}")
    return jsonify({"ok": True, **payload})

@app.route("/api/chat/group/<int:post_id>/messages/<int:message_id>/edit", methods=["POST"])
@login_required
def edit_group_message(post_id, message_id):
    ensure_chat_schema()
    new_message = _normalize_message(request.form.get("message", ""))
    if not _is_valid_message(new_message):
        return jsonify({"ok": False, "error": "Invalid message"}), 400

    user_id = session["user_id"]
    db = get_db_connection()
    cur = db.cursor()

    if not _is_user_in_trip_chat(cur, post_id, user_id):
        cur.close()
        db.close()
        abort(403)

    if not _message_is_from_sender(cur, "trip_messages", message_id, "user_id", user_id):
        cur.close()
        db.close()
        abort(403)

    cur.execute("""
        UPDATE trip_messages
        SET message=%s,
            edited_at=NOW()
        WHERE id=%s
          AND post_id=%s
          AND deleted_at IS NULL
    """, (new_message, message_id, post_id))
    if not cur.rowcount:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Message not found"}), 404

    cur.execute("""
        SELECT created_at, edited_at
        FROM trip_messages
        WHERE id=%s
    """, (message_id,))
    row = cur.fetchone() or {}

    db.commit()
    cur.close()
    db.close()

    payload = {
        "trip_id": post_id,
        "id": message_id,
        "message": new_message,
        "created_at": _dt_to_str(row.get("created_at")),
        "edited_at": _dt_to_str(row.get("edited_at"))
    }
    socketio.emit("trip_message_updated", payload, room=str(post_id))
    return jsonify({"ok": True, **payload})

@app.route("/api/chat/group/<int:post_id>/messages/<int:message_id>/delete", methods=["POST"])
@login_required
def delete_group_message(post_id, message_id):
    ensure_chat_schema()
    user_id = session["user_id"]

    db = get_db_connection()
    cur = db.cursor()

    if not _is_user_in_trip_chat(cur, post_id, user_id):
        cur.close()
        db.close()
        abort(403)

    if not _message_is_from_sender(cur, "trip_messages", message_id, "user_id", user_id):
        cur.close()
        db.close()
        abort(403)

    cur.execute("""
        UPDATE trip_messages
        SET deleted_at=NOW()
        WHERE id=%s
          AND post_id=%s
          AND deleted_at IS NULL
    """, (message_id, post_id))
    if not cur.rowcount:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Message not found"}), 404

    db.commit()
    cur.close()
    db.close()

    payload = {"trip_id": post_id, "id": message_id}
    socketio.emit("trip_message_deleted", payload, room=str(post_id))
    return jsonify({"ok": True, **payload})

@app.route("/api/chat/group/<int:post_id>/messages/<int:message_id>/flag", methods=["POST"])
@login_required
def flag_group_message(post_id, message_id):
    ensure_chat_schema()
    user_id = session["user_id"]

    db = get_db_connection()
    cur = db.cursor()

    if not _is_user_in_trip_chat(cur, post_id, user_id):
        cur.close()
        db.close()
        abort(403)

    cur.execute("""
        SELECT user_id
        FROM trip_messages
        WHERE id=%s
          AND post_id=%s
          AND deleted_at IS NULL
    """, (message_id, post_id))
    row = cur.fetchone()
    if not row:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Message not found"}), 404
    if int(row["user_id"]) == int(user_id):
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Cannot report your own message"}), 400

    cur.execute("""
        UPDATE trip_messages
        SET is_flagged=1,
            moderation_status='flagged'
        WHERE id=%s
          AND post_id=%s
    """, (message_id, post_id))

    cur.execute("""
        SELECT user_id
        FROM User_Details
        WHERE role='admin'
          AND is_active=1
    """)
    for admin_row in cur.fetchall():
        _create_notification(
            cur,
            int(admin_row["user_id"]),
            "Flagged group message",
            f"Trip #{post_id}, message #{message_id} was reported.",
            ntype="moderation",
            send_email=False
        )

    db.commit()
    cur.close()
    db.close()

    payload = {"trip_id": post_id, "id": message_id, "is_flagged": 1}
    socketio.emit("trip_message_flagged", payload, room=str(post_id))
    return jsonify({"ok": True, **payload})

@app.route("/api/trips/<int:post_id>/reviews/<int:review_id>/flag", methods=["POST"])
@login_required
def flag_trip_review(post_id, review_id):
    ensure_chat_schema()
    ensure_trip_feedback_schema()
    user_id = int(session["user_id"])

    db = get_db_connection()
    cur = db.cursor()

    cur.execute("""
        SELECT user_id AS host_id
        FROM travel_posts
        WHERE post_id=%s
        LIMIT 1
    """, (post_id,))
    trip_row = cur.fetchone()
    if not trip_row:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Trip not found"}), 404

    host_id = int(trip_row.get("host_id") or 0)
    can_flag = (host_id == user_id)
    if not can_flag:
        cur.execute("""
            SELECT status
            FROM trip_members
            WHERE post_id=%s
              AND user_id=%s
            LIMIT 1
        """, (post_id, user_id))
        member_row = cur.fetchone()
        can_flag = bool(member_row and str(member_row.get("status") or "") == "approved")

    if not can_flag and session.get("role") != "admin":
        cur.close()
        db.close()
        abort(403)

    cur.execute("""
        SELECT id, reviewer_id, is_flagged
        FROM trip_reviews
        WHERE id=%s
          AND post_id=%s
        LIMIT 1
    """, (review_id, post_id))
    row = cur.fetchone()
    if not row:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Review not found"}), 404

    if int(row.get("reviewer_id") or 0) == user_id:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Cannot report your own review"}), 400

    if int(row.get("is_flagged") or 0) != 1:
        cur.execute("""
            UPDATE trip_reviews
            SET is_flagged=1,
                moderation_status='flagged',
                moderated_at=NULL,
                moderated_by=NULL
            WHERE id=%s
              AND post_id=%s
        """, (review_id, post_id))

        cur.execute("""
            SELECT user_id
            FROM User_Details
            WHERE role='admin'
              AND is_active=1
        """)
        for admin_row in cur.fetchall():
            _create_notification(
                cur,
                int(admin_row["user_id"]),
                "Flagged trip review",
                f"Trip #{post_id}, review #{review_id} was reported.",
                ntype="moderation",
                send_email=False
            )

    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True, "trip_id": post_id, "id": review_id, "is_flagged": 1})

@app.route("/api/chat/private/<int:conversation_id>/support", methods=["POST"])
@login_required
def mark_private_support(conversation_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    requested_priority = (request.form.get("priority") or "normal").strip().lower()
    if requested_priority not in {"low", "normal", "high", "urgent"}:
        requested_priority = "normal"

    db = get_db_connection()
    cur = db.cursor()

    allowed, other_user_id = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)
    if other_user_id is None or not _is_admin_user(cur, other_user_id):
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Support chat requires an admin conversation"}), 400

    cur.execute("""
        UPDATE private_conversations
        SET is_support=1,
            support_status='open',
            support_priority=%s,
            support_opened_by=COALESCE(support_opened_by, %s)
        WHERE id=%s
    """, (requested_priority, user_id, conversation_id))

    cur.execute("""
        SELECT user_id
        FROM User_Details
        WHERE role='admin'
          AND is_active=1
    """)
    admins = [int(r["user_id"]) for r in cur.fetchall()]
    for admin_id in admins:
        _create_notification(
            cur,
            admin_id,
            "Support issue opened",
            f"Conversation #{conversation_id} marked as support ({requested_priority}).",
            ntype="support",
            send_email=SUPPORT_EMAIL_ENABLED
        )

    db.commit()
    cur.close()
    db.close()

    payload = {
        "conversation_id": conversation_id,
        "is_support": 1,
        "support_status": "open",
        "support_priority": requested_priority
    }
    socketio.emit("private_support_updated", payload, room=f"private_{conversation_id}")
    return jsonify({"ok": True, **payload})

@app.route("/api/admin/conversations/<int:conversation_id>/support", methods=["POST"])
@admin_required
def update_support_thread(conversation_id):
    ensure_chat_schema()
    support_status = (request.form.get("status") or "").strip().lower()
    support_priority = (request.form.get("priority") or "").strip().lower()
    assigned_admin_id = _parse_int(request.form.get("assigned_admin_id"))

    if support_status not in {"open", "in_progress", "resolved"}:
        support_status = "open"
    if support_priority not in {"low", "normal", "high", "urgent"}:
        support_priority = "normal"

    db = get_db_connection()
    cur = db.cursor()

    cur.execute("""
        SELECT pc.id,
               pc.user1_id,
               pc.user2_id,
               a.role AS role1,
               b.role AS role2
        FROM private_conversations pc
        JOIN User_Details a ON a.user_id = pc.user1_id
        JOIN User_Details b ON b.user_id = pc.user2_id
        WHERE pc.id=%s
        LIMIT 1
    """, (conversation_id,))
    row = cur.fetchone()
    if not row:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Conversation not found"}), 404

    has_admin_participant = (row.get("role1") == "admin") or (row.get("role2") == "admin")
    if not has_admin_participant:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Not a support-eligible conversation"}), 400

    if assigned_admin_id:
        cur.execute("""
            SELECT 1
            FROM User_Details
            WHERE user_id=%s
              AND role='admin'
              AND is_active=1
            LIMIT 1
        """, (assigned_admin_id,))
        if not cur.fetchone():
            cur.close()
            db.close()
            return jsonify({"ok": False, "error": "Assigned admin is invalid"}), 400

    cur.execute("""
        UPDATE private_conversations
        SET is_support=1,
            support_status=%s,
            support_priority=%s,
            assigned_admin_id=%s
        WHERE id=%s
    """, (support_status, support_priority, assigned_admin_id, conversation_id))
    _write_admin_action(
        cur,
        session["user_id"],
        "support_thread_update",
        "private_conversation",
        conversation_id,
        _safe_json_dumps({
            "support_status": support_status,
            "support_priority": support_priority,
            "assigned_admin_id": assigned_admin_id
        })
    )

    cur.execute("""
        SELECT u.username
        FROM User_Details u
        WHERE u.user_id=%s
    """, (assigned_admin_id,))
    assignee_row = cur.fetchone() if assigned_admin_id else None
    assigned_admin_name = assignee_row["username"] if assignee_row else None

    db.commit()
    cur.close()
    db.close()

    payload = {
        "conversation_id": conversation_id,
        "is_support": 1,
        "support_status": support_status,
        "support_priority": support_priority,
        "assigned_admin_id": assigned_admin_id,
        "assigned_admin_name": assigned_admin_name
    }
    socketio.emit("private_support_updated", payload, room=f"private_{conversation_id}")
    if request.headers.get("X-Requested-With") == "XMLHttpRequest":
        return jsonify({"ok": True, **payload})
    return redirect(request.referrer or url_for("admin_messages"))

@app.route("/api/chat/group/<int:post_id>/broadcast", methods=["POST"])
@login_required
def host_broadcast_message(post_id):
    ensure_chat_schema()
    message = _normalize_message(request.form.get("message") or "")
    if not _is_valid_message(message):
        return jsonify({"ok": False, "error": "Invalid message"}), 400
    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
        SELECT user_id, trip_status
        FROM travel_posts
        WHERE post_id=%s
        LIMIT 1
    """, (post_id,))
    trip = cur.fetchone()
    if not trip or int(trip["user_id"]) != int(session["user_id"]):
        cur.close()
        db.close()
        abort(403)
    if trip["trip_status"] in {"completed", "cancelled"}:
        cur.close()
        db.close()
        return jsonify({"ok": False, "error": "Trip chat is closed"}), 400
    message_id = _create_trip_system_message(
        cur,
        post_id,
        session["user_id"],
        f"[Broadcast] {message}",
        event_type="broadcast"
    )
    cur.execute("SELECT username FROM User_Details WHERE user_id=%s", (session["user_id"],))
    sender_row = cur.fetchone() or {}
    cur.execute("""
        SELECT user_id
        FROM trip_members
        WHERE post_id=%s
          AND status='approved'
    """, (post_id,))
    for row in cur.fetchall():
        uid = int(row["user_id"])
        if uid == int(session["user_id"]):
            continue
        _create_notification(
            cur,
            uid,
            "Trip broadcast",
            message,
            ntype="chat",
            send_email=False
        )
    db.commit()
    cur.close()
    db.close()
    payload = {
        "trip_id": post_id,
        "id": message_id,
        "user_id": session["user_id"],
        "username": sender_row.get("username") or "Host",
        "message": f"[Broadcast] {message}",
        "message_type": "broadcast",
        "created_at": _dt_to_str(datetime.now()),
        "is_flagged": 0,
        "edited_at": None,
        "reactions": {},
        "starred": 0,
        "delivered_count": 0,
        "seen_count": 0,
        "recipient_count": 0,
        "receipt_status": "sent"
    }
    socketio.emit("message", payload, room=str(post_id))
    return jsonify({"ok": True, **payload})

def _parse_schedule_time(value):
    text = (value or "").strip()
    if not text:
        return None
    formats = ["%Y-%m-%d %H:%M:%S", "%Y-%m-%d %H:%M", "%Y-%m-%dT%H:%M:%S", "%Y-%m-%dT%H:%M"]
    for fmt in formats:
        try:
            return datetime.strptime(text, fmt)
        except ValueError:
            continue
    return None

@app.route("/api/chat/private/<int:conversation_id>/schedule", methods=["POST"])
@login_required
def schedule_private_message(conversation_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    message = _normalize_message(request.form.get("message") or "")
    run_at = _parse_schedule_time(request.form.get("run_at"))
    if not _is_valid_message(message):
        return jsonify({"ok": False, "error": "Invalid message"}), 400
    if not run_at:
        return jsonify({"ok": False, "error": "Invalid schedule time"}), 400
    if run_at <= datetime.now():
        return jsonify({"ok": False, "error": "Schedule time must be in future"}), 400
    if run_at > (datetime.now() + timedelta(days=30)):
        return jsonify({"ok": False, "error": "Schedule time too far"}), 400
    db = get_db_connection()
    cur = db.cursor()
    allowed, _ = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)
    cur.execute("""
        INSERT INTO scheduled_messages
            (channel_type, channel_id, sender_id, message, run_at, status, created_at)
        VALUES ('private', %s, %s, %s, %s, 'scheduled', NOW())
    """, (conversation_id, user_id, message, run_at))
    schedule_id = int(cur.lastrowid or 0)
    _enqueue_background_job(cur, "dispatch_scheduled", {"source": "private", "schedule_id": schedule_id}, run_at=run_at)
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True, "schedule_id": schedule_id, "run_at": _dt_to_str(run_at)})

@app.route("/api/chat/group/<int:post_id>/schedule", methods=["POST"])
@login_required
def schedule_group_message(post_id):
    ensure_chat_schema()
    user_id = session["user_id"]
    message = _normalize_message(request.form.get("message") or "")
    run_at = _parse_schedule_time(request.form.get("run_at"))
    if not _is_valid_message(message):
        return jsonify({"ok": False, "error": "Invalid message"}), 400
    if not run_at:
        return jsonify({"ok": False, "error": "Invalid schedule time"}), 400
    if run_at <= datetime.now():
        return jsonify({"ok": False, "error": "Schedule time must be in future"}), 400
    db = get_db_connection()
    cur = db.cursor()
    if not _is_user_in_trip_chat(cur, post_id, user_id):
        cur.close()
        db.close()
        abort(403)
    cur.execute("""
        INSERT INTO scheduled_messages
            (channel_type, channel_id, sender_id, message, run_at, status, created_at)
        VALUES ('group', %s, %s, %s, %s, 'scheduled', NOW())
    """, (post_id, user_id, message, run_at))
    schedule_id = int(cur.lastrowid or 0)
    _enqueue_background_job(cur, "dispatch_scheduled", {"source": "group", "schedule_id": schedule_id}, run_at=run_at)
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True, "schedule_id": schedule_id, "run_at": _dt_to_str(run_at)})

@app.route("/api/chat/private/<int:conversation_id>/export")
@login_required
def export_private_chat(conversation_id):
    ensure_chat_schema()
    fmt = (request.args.get("format") or "csv").strip().lower()
    user_id = session["user_id"]
    db = get_db_connection()
    cur = db.cursor()
    allowed, _ = _can_access_private_conversation(cur, conversation_id, user_id)
    if not allowed:
        cur.close()
        db.close()
        abort(403)
    cur.execute("""
        SELECT pm.id, pm.sender_id, u.username, pm.message, pm.message_type, pm.created_at
        FROM private_messages pm
        JOIN User_Details u ON u.user_id=pm.sender_id
        WHERE pm.conversation_id=%s
          AND pm.deleted_at IS NULL
        ORDER BY pm.id
    """, (conversation_id,))
    rows = cur.fetchall()
    cur.close()
    db.close()
    if fmt == "pdf":
        lines = [
            f"{_dt_to_str(r.get('created_at'))} | {r.get('username')}: {r.get('message') or ''}"
            for r in rows
        ]
        pdf_bytes = _build_simple_pdf(f"Private Chat #{conversation_id}", lines)
        return Response(
            pdf_bytes,
            mimetype="application/pdf",
            headers={"Content-Disposition": f"attachment; filename=private-chat-{conversation_id}.pdf"}
        )
    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(["id", "created_at", "sender_id", "username", "message_type", "message"])
    for row in rows:
        writer.writerow([
            row.get("id"),
            _dt_to_str(row.get("created_at")),
            row.get("sender_id"),
            row.get("username"),
            row.get("message_type") or "text",
            row.get("message") or ""
        ])
    return Response(
        output.getvalue(),
        mimetype="text/csv",
        headers={"Content-Disposition": f"attachment; filename=private-chat-{conversation_id}.csv"}
    )

@app.route("/api/chat/group/<int:post_id>/export")
@login_required
def export_group_chat(post_id):
    ensure_chat_schema()
    fmt = (request.args.get("format") or "csv").strip().lower()
    user_id = session["user_id"]
    db = get_db_connection()
    cur = db.cursor()
    if not _is_user_in_trip_chat(cur, post_id, user_id):
        cur.close()
        db.close()
        abort(403)
    cur.execute("""
        SELECT tm.id, tm.user_id, u.username, tm.message, tm.message_type, tm.created_at
        FROM trip_messages tm
        JOIN User_Details u ON u.user_id=tm.user_id
        WHERE tm.post_id=%s
          AND tm.deleted_at IS NULL
        ORDER BY tm.id
    """, (post_id,))
    rows = cur.fetchall()
    cur.close()
    db.close()
    if fmt == "pdf":
        lines = [
            f"{_dt_to_str(r.get('created_at'))} | {r.get('username')}: {r.get('message') or ''}"
            for r in rows
        ]
        pdf_bytes = _build_simple_pdf(f"Group Chat #{post_id}", lines)
        return Response(
            pdf_bytes,
            mimetype="application/pdf",
            headers={"Content-Disposition": f"attachment; filename=group-chat-{post_id}.pdf"}
        )
    output = io.StringIO()
    writer = csv.writer(output)
    writer.writerow(["id", "created_at", "user_id", "username", "message_type", "message"])
    for row in rows:
        writer.writerow([
            row.get("id"),
            _dt_to_str(row.get("created_at")),
            row.get("user_id"),
            row.get("username"),
            row.get("message_type") or "text",
            row.get("message") or ""
        ])
    return Response(
        output.getvalue(),
        mimetype="text/csv",
        headers={"Content-Disposition": f"attachment; filename=group-chat-{post_id}.csv"}
    )

@app.route("/notifications")
@login_required
def notifications_page():
    ensure_chat_schema()
    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
        SELECT id, title, message, type, is_read, created_at
        FROM user_notifications
        WHERE user_id=%s
        ORDER BY created_at DESC
        LIMIT 300
    """, (session["user_id"],))
    notifications = cur.fetchall()
    cur.execute("""
        SELECT COUNT(*) AS unread
        FROM user_notifications
        WHERE user_id=%s
          AND is_read=0
    """, (session["user_id"],))
    unread = int((cur.fetchone() or {}).get("unread") or 0)
    cur.close()
    db.close()
    return render_template(
        "notifications.html",
        notifications=notifications,
        unread_count=unread
    )

@app.route("/api/notifications")
@login_required
def notifications_api():
    ensure_chat_schema()
    limit = _parse_int(request.args.get("limit")) or 80
    limit = max(1, min(500, limit))
    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
        SELECT id, title, message, type, is_read, created_at
        FROM user_notifications
        WHERE user_id=%s
        ORDER BY created_at DESC
        LIMIT %s
    """, (session["user_id"], limit))
    rows = cur.fetchall()
    cur.close()
    db.close()
    return jsonify({
        "ok": True,
        "rows": [
            {
                "id": int(r["id"]),
                "title": r.get("title") or "",
                "message": r.get("message") or "",
                "type": r.get("type") or "info",
                "is_read": int(r.get("is_read") or 0),
                "created_at": _dt_to_str(r.get("created_at"))
            }
            for r in rows
        ]
    })

@app.route("/api/notifications/read_all", methods=["POST"])
@login_required
def notifications_mark_all_read():
    ensure_chat_schema()
    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
        UPDATE user_notifications
        SET is_read=1
        WHERE user_id=%s
          AND is_read=0
    """, (session["user_id"],))
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True})

@app.route("/api/notifications/<int:notification_id>/read", methods=["POST"])
@login_required
def notifications_mark_read(notification_id):
    ensure_chat_schema()
    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
        UPDATE user_notifications
        SET is_read=1
        WHERE id=%s
          AND user_id=%s
    """, (notification_id, session["user_id"]))
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True})

@app.route("/api/notifications/<int:notification_id>/dismiss", methods=["POST"])
@login_required
def notifications_dismiss(notification_id):
    ensure_chat_schema()
    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
        DELETE FROM user_notifications
        WHERE id=%s
          AND user_id=%s
    """, (notification_id, session["user_id"]))
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True})

@app.route("/admin/moderation")
@admin_required
def admin_moderation():
    ensure_chat_schema()
    ensure_trip_feedback_schema()
    status_filter = (request.args.get("status") or "flagged").strip().lower()
    if status_filter not in {"flagged", "resolved", "dismissed", "all"}:
        status_filter = "flagged"
    page = max(1, _parse_int(request.args.get("page")) or 1)
    per_page = _parse_int(request.args.get("per_page")) or 60
    per_page = max(20, min(200, per_page))
    offset = (page - 1) * per_page

    db = get_db_connection()
    cur = db.cursor()
    private_where = "pm.is_flagged=1" if status_filter == "all" else "pm.moderation_status=%s"
    group_where = "tm.is_flagged=1" if status_filter == "all" else "tm.moderation_status=%s"
    review_where = "tr.is_flagged=1" if status_filter == "all" else "tr.moderation_status=%s"
    count_sql = f"""
        SELECT
            (
                SELECT COUNT(*)
                FROM private_messages pm
                WHERE {private_where}
                  AND pm.deleted_at IS NULL
            ) +
            (
                SELECT COUNT(*)
                FROM trip_messages tm
                WHERE {group_where}
                  AND tm.deleted_at IS NULL
            ) +
            (
                SELECT COUNT(*)
                FROM trip_reviews tr
                WHERE {review_where}
            ) AS total
    """
    list_sql = f"""
        SELECT *
        FROM (
            SELECT
                'private' AS channel_type,
                pm.id AS message_id,
                pm.conversation_id AS channel_id,
                pm.message,
                pm.created_at,
                pm.moderation_status,
                u.username AS sender_name
            FROM private_messages pm
            JOIN User_Details u ON u.user_id = pm.sender_id
            WHERE {private_where}
              AND pm.deleted_at IS NULL

            UNION ALL

            SELECT
                'group' AS channel_type,
                tm.id AS message_id,
                tm.post_id AS channel_id,
                tm.message,
                tm.created_at,
                tm.moderation_status,
                u.username AS sender_name
            FROM trip_messages tm
            JOIN User_Details u ON u.user_id = tm.user_id
            WHERE {group_where}
              AND tm.deleted_at IS NULL

            UNION ALL

            SELECT
                'review' AS channel_type,
                tr.id AS message_id,
                tr.post_id AS channel_id,
                COALESCE(
                    NULLIF(tr.comment, ''),
                    CONCAT('[', UPPER(tr.review_type), ' ', tr.rating, '★ review]')
                ) AS message,
                tr.created_at,
                tr.moderation_status,
                u.username AS sender_name
            FROM trip_reviews tr
            JOIN User_Details u ON u.user_id = tr.reviewer_id
            WHERE {review_where}
        ) AS combined_rows
        ORDER BY created_at DESC
        LIMIT %s OFFSET %s
    """

    if status_filter == "all":
        cur.execute(count_sql)
        total = int((cur.fetchone() or {}).get("total") or 0)
        cur.execute(list_sql, (per_page, offset))
    else:
        cur.execute(count_sql, (status_filter, status_filter, status_filter))
        total = int((cur.fetchone() or {}).get("total") or 0)
        cur.execute(list_sql, (status_filter, status_filter, status_filter, per_page, offset))
    items = cur.fetchall()
    total_pages = max(1, int(math.ceil(total / float(per_page)))) if total else 1
    has_prev = page > 1
    has_next = (page * per_page) < total
    cur.close()
    db.close()
    return render_template(
        "admin_moderation.html",
        items=items,
        status_filter=status_filter,
        page=page,
        per_page=per_page,
        total=total,
        total_pages=total_pages,
        has_prev=has_prev,
        has_next=has_next
    )

@app.route("/api/admin/moderation/bulk", methods=["POST"])
@admin_required
def moderation_bulk_action():
    ensure_chat_schema()
    ensure_trip_feedback_schema()
    channel_type = (request.form.get("channel_type") or "").strip().lower()
    action = (request.form.get("action") or "").strip().lower()
    ids_raw = (request.form.get("message_ids") or "").strip()
    ids = [int(x) for x in ids_raw.split(",") if x.strip().isdigit()]
    if channel_type not in {"private", "group", "review"} or action not in {"resolve", "dismiss", "delete"} or not ids:
        return jsonify({"ok": False, "error": "Invalid payload"}), 400
    db = get_db_connection()
    cur = db.cursor()
    placeholders = ",".join(["%s"] * len(ids))
    if channel_type in {"private", "group"}:
        table = "private_messages" if channel_type == "private" else "trip_messages"
        if action == "delete":
            cur.execute(f"""
                UPDATE {table}
                SET deleted_at=NOW(),
                    moderation_status='removed',
                    moderated_at=NOW(),
                    moderated_by=%s
                WHERE id IN ({placeholders})
            """, (session["user_id"], *ids))
        else:
            next_status = "resolved" if action == "resolve" else "dismissed"
            cur.execute(f"""
                UPDATE {table}
                SET is_flagged=0,
                    moderation_status=%s,
                    moderated_at=NOW(),
                    moderated_by=%s
                WHERE id IN ({placeholders})
            """, (next_status, session["user_id"], *ids))
    else:
        if action == "delete":
            cur.execute(f"""
                UPDATE trip_reviews
                SET comment='[Removed by moderation]',
                    is_flagged=0,
                    moderation_status='removed',
                    moderated_at=NOW(),
                    moderated_by=%s
                WHERE id IN ({placeholders})
            """, (session["user_id"], *ids))
        else:
            next_status = "resolved" if action == "resolve" else "dismissed"
            cur.execute(f"""
                UPDATE trip_reviews
                SET is_flagged=0,
                    moderation_status=%s,
                    moderated_at=NOW(),
                    moderated_by=%s
                WHERE id IN ({placeholders})
            """, (next_status, session["user_id"], *ids))
    _write_admin_action(
        cur,
        session["user_id"],
        "moderation_bulk",
        channel_type,
        None,
        _safe_json_dumps({"action": action, "count": len(ids)})
    )
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True, "updated": len(ids)})

@app.route("/api/admin/chat/search")
@admin_required
def admin_chat_search():
    ensure_chat_schema()
    q = (request.args.get("q") or "").strip().lower()
    sender_id = _parse_int(request.args.get("sender_id"))
    date_from = _parse_date_only(request.args.get("date_from"))
    date_to = _parse_date_only(request.args.get("date_to"))
    limit = _parse_int(request.args.get("limit")) or 100
    limit = max(1, min(300, limit))
    private_conditions = ["pm.deleted_at IS NULL"]
    private_args = []
    group_conditions = ["tm.deleted_at IS NULL"]
    group_args = []
    if q:
        like_q = f"%{q}%"
        private_conditions.append("LOWER(pm.message) LIKE %s")
        group_conditions.append("LOWER(tm.message) LIKE %s")
        private_args.append(like_q)
        group_args.append(like_q)
    if sender_id:
        private_conditions.append("pm.sender_id=%s")
        group_conditions.append("tm.user_id=%s")
        private_args.append(sender_id)
        group_args.append(sender_id)
    if date_from:
        private_conditions.append("DATE(pm.created_at) >= %s")
        group_conditions.append("DATE(tm.created_at) >= %s")
        private_args.append(date_from.strftime("%Y-%m-%d"))
        group_args.append(date_from.strftime("%Y-%m-%d"))
    if date_to:
        private_conditions.append("DATE(pm.created_at) <= %s")
        group_conditions.append("DATE(tm.created_at) <= %s")
        private_args.append(date_to.strftime("%Y-%m-%d"))
        group_args.append(date_to.strftime("%Y-%m-%d"))
    db = get_db_connection()
    cur = db.cursor()
    cur.execute(f"""
        SELECT 'private' AS channel_type, pm.id AS message_id, pm.conversation_id AS channel_id,
               pm.message, pm.created_at, u.username
        FROM private_messages pm
        JOIN User_Details u ON u.user_id=pm.sender_id
        WHERE {" AND ".join(private_conditions)}
        ORDER BY pm.created_at DESC
        LIMIT %s
    """, (*private_args, limit))
    private_rows = cur.fetchall()
    cur.execute(f"""
        SELECT 'group' AS channel_type, tm.id AS message_id, tm.post_id AS channel_id,
               tm.message, tm.created_at, u.username
        FROM trip_messages tm
        JOIN User_Details u ON u.user_id=tm.user_id
        WHERE {" AND ".join(group_conditions)}
        ORDER BY tm.created_at DESC
        LIMIT %s
    """, (*group_args, limit))
    group_rows = cur.fetchall()
    rows = sorted(private_rows + group_rows, key=lambda r: r.get("created_at") or datetime.min, reverse=True)[:limit]
    cur.close()
    db.close()
    return jsonify({
        "ok": True,
        "rows": [
            {
                "channel_type": row.get("channel_type"),
                "channel_id": int(row.get("channel_id") or 0),
                "message_id": int(row.get("message_id") or 0),
                "message": row.get("message") or "",
                "created_at": _dt_to_str(row.get("created_at")),
                "username": row.get("username") or ""
            }
            for row in rows
        ]
    })

@app.route("/admin/chat_analytics")
@admin_required
def admin_chat_analytics():
    ensure_chat_schema()
    ensure_trip_feedback_schema()
    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
        SELECT COUNT(*) AS private_count
        FROM private_messages
        WHERE deleted_at IS NULL
    """)
    private_count = int((cur.fetchone() or {}).get("private_count") or 0)
    cur.execute("""
        SELECT COUNT(*) AS group_count
        FROM trip_messages
        WHERE deleted_at IS NULL
    """)
    group_count = int((cur.fetchone() or {}).get("group_count") or 0)
    cur.execute("""
        SELECT COUNT(*) AS unresolved_support
        FROM private_conversations
        WHERE is_support=1
          AND support_status IN ('open', 'in_progress')
    """)
    unresolved_support = int((cur.fetchone() or {}).get("unresolved_support") or 0)
    cur.execute("""
        SELECT COUNT(*) AS flagged_total
        FROM (
            SELECT id FROM private_messages WHERE is_flagged=1 AND deleted_at IS NULL
            UNION ALL
            SELECT id FROM trip_messages WHERE is_flagged=1 AND deleted_at IS NULL
            UNION ALL
            SELECT id FROM trip_reviews WHERE is_flagged=1
        ) t
    """)
    flagged_total = int((cur.fetchone() or {}).get("flagged_total") or 0)
    cur.execute("""
        SELECT DATE(created_at) AS day, COUNT(*) AS cnt
        FROM user_reports
        WHERE created_at >= (NOW() - INTERVAL 14 DAY)
        GROUP BY DATE(created_at)
        ORDER BY day DESC
    """)
    flagged_trend = cur.fetchall()
    cur.execute("""
        SELECT
            AVG(TIMESTAMPDIFF(MINUTE, pm.created_at, r.seen_at)) AS avg_seen_minutes
        FROM private_messages pm
        JOIN chat_message_receipts r
          ON r.channel_type='private'
         AND r.message_id=pm.id
        WHERE pm.created_at >= (NOW() - INTERVAL 30 DAY)
          AND r.seen_at IS NOT NULL
    """)
    avg_seen_minutes = float((cur.fetchone() or {}).get("avg_seen_minutes") or 0.0)
    cur.close()
    db.close()
    return render_template(
        "admin_chat_analytics.html",
        private_count=private_count,
        group_count=group_count,
        unresolved_support=unresolved_support,
        flagged_total=flagged_total,
        avg_seen_minutes=avg_seen_minutes,
        flagged_trend=flagged_trend
    )

@app.route("/admin/audit")
@admin_required
def admin_audit_log():
    ensure_chat_schema()
    page = max(1, _parse_int(request.args.get("page")) or 1)
    per_page = _parse_int(request.args.get("per_page")) or 80
    per_page = max(20, min(250, per_page))
    offset = (page - 1) * per_page

    db = get_db_connection()
    cur = db.cursor()
    cur.execute("SELECT COUNT(*) AS total FROM admin_action_logs")
    total = int((cur.fetchone() or {}).get("total") or 0)
    cur.execute("""
        SELECT a.id, a.action_type, a.target_type, a.target_id, a.details, a.created_at, u.username AS admin_name
        FROM admin_action_logs a
        JOIN User_Details u ON u.user_id = a.admin_user_id
        ORDER BY a.created_at DESC
        LIMIT %s OFFSET %s
    """, (per_page, offset))
    rows = cur.fetchall()
    total_pages = max(1, int(math.ceil(total / float(per_page)))) if total else 1
    has_prev = page > 1
    has_next = (page * per_page) < total
    cur.close()
    db.close()
    return render_template(
        "admin_audit.html",
        rows=rows,
        page=page,
        per_page=per_page,
        total=total,
        total_pages=total_pages,
        has_prev=has_prev,
        has_next=has_next
    )

@app.route("/api/admin/chat/retention/run", methods=["POST"])
@admin_required
def run_chat_retention():
    ensure_chat_schema()
    days = _parse_int(request.form.get("days")) or CHAT_RETENTION_DEFAULT_DAYS
    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
        INSERT INTO system_settings (setting_key, setting_value)
        VALUES ('chat_retention_days', %s)
        ON DUPLICATE KEY UPDATE setting_value=VALUES(setting_value)
    """, (str(days),))
    summary = _run_retention_cleanup(cur, days)
    _write_admin_action(
        cur,
        session["user_id"],
        "retention_run",
        "chat",
        None,
        _safe_json_dumps({"days": days, **summary})
    )
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True, **summary, "days": days})

@app.route("/api/admin/chat/retention/restore", methods=["POST"])
@admin_required
def restore_chat_retention():
    ensure_chat_schema()
    days = _parse_int(request.form.get("restore_days")) or CHAT_RETENTION_RESTORE_DAYS
    db = get_db_connection()
    cur = db.cursor()
    summary = _restore_archived_messages(cur, days)
    _write_admin_action(
        cur,
        session["user_id"],
        "retention_restore",
        "chat",
        None,
        _safe_json_dumps({"restore_days": days, **summary})
    )
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True, **summary, "restore_days": days})

@app.route("/api/admin/jobs/run", methods=["POST"])
@admin_required
def run_background_jobs():
    ensure_chat_schema()
    limit = _parse_int(request.form.get("limit")) or 80
    db = get_db_connection()
    cur = db.cursor()
    job_summary = _run_background_jobs(cur, limit=limit)
    sched_summary = _process_due_scheduled_messages(cur, limit=limit)
    db.commit()
    cur.close()
    db.close()
    return jsonify({"ok": True, "jobs": job_summary, "scheduled": sched_summary})

@app.route("/api/admin/notifications/broadcast", methods=["POST"])
@admin_required
def admin_broadcast_notifications():
    ensure_auth_schema()
    ensure_chat_schema()

    payload = request.get_json(silent=True) or {}

    def _req_value(key, default=""):
        if key in request.form:
            return request.form.get(key, default)
        return payload.get(key, default)

    title = (_req_value("title", "") or "").strip()
    message = (_req_value("message", "") or "").strip()
    send_email = _parse_bool_flag(_req_value("send_email", "1"), True)
    send_sms = _parse_bool_flag(_req_value("send_sms", "0"), False)
    include_admins = _parse_bool_flag(_req_value("include_admins", "0"), False)

    if not title or not message:
        return jsonify({"ok": False, "error": "title and message are required"}), 400

    db = get_db_connection()
    cur = db.cursor()

    sql = """
        SELECT user_id
        FROM User_Details
        WHERE is_active=1
    """
    if not include_admins:
        sql += " AND role!='admin'"

    cur.execute(sql)
    rows = cur.fetchall()
    recipient_ids = [int(row["user_id"]) for row in rows]

    for uid in recipient_ids:
        _create_notification(
            cur,
            uid,
            title,
            message,
            ntype="announcement",
            send_email=send_email,
            send_sms=send_sms
        )

    _write_admin_action(
        cur,
        session["user_id"],
        "notification_broadcast",
        "users",
        None,
        _safe_json_dumps({
            "title": title[:120],
            "recipients": len(recipient_ids),
            "send_email": bool(send_email),
            "send_sms": bool(send_sms),
            "include_admins": bool(include_admins)
        })
    )

    db.commit()
    cur.close()
    db.close()

    return jsonify({
        "ok": True,
        "recipients": len(recipient_ids),
        "queued_email": bool(send_email),
        "queued_sms": bool(send_sms),
        "title": title
    })

@app.route("/delete/<int:post_id>", methods=["POST"])
@login_required
def delete_trip(post_id):
    db = get_db_connection()
    cur = db.cursor()

    # Ensure only host can cancel
    cur.execute("""
        SELECT user_id, trip_status
        FROM travel_posts
        WHERE post_id = %s
    """, (post_id,))
    trip = cur.fetchone()

    if not trip or trip["user_id"] != session["user_id"]:
        cur.close()
        db.close()
        abort(403)
    if trip["trip_status"] == "completed":
        cur.close()
        db.close()
        abort(403)

    cur.execute("""
        UPDATE travel_posts
        SET trip_status = 'cancelled',
            cancel_reason = %s,
            cancelled_at = NOW()
        WHERE post_id = %s
    """, (
        request.form.get("reason", "Cancelled by host"),
        post_id
    ))

    db.commit()

    cur.close()
    db.close()

    return redirect(request.referrer or url_for("mainpage", view="mine"))

@app.route("/admin")
@admin_required
def admin_root():
    return redirect(url_for("admin_dashboard"))


@app.route("/admin/verify")
@admin_required
def admin_verify():
    return admin_dashboard()

@app.route("/complete/<int:post_id>", methods=["POST"])
@login_required
def complete_trip(post_id):
    db = get_db_connection()
    cur = db.cursor()

    # 🔒 Ensure only host can complete + prevent re-complete
    cur.execute("""
        SELECT user_id, trip_status, travel_date
        FROM travel_posts
        WHERE post_id = %s
    """, (post_id,))
    trip = cur.fetchone()

    if not trip or trip["user_id"] != session["user_id"]:
        cur.close()
        db.close()
        abort(403)

    if trip["trip_status"] in {"completed", "cancelled"}:
        cur.close()
        db.close()
        flash("Only active trips can be marked as completed.", "error")
        return redirect(request.referrer or url_for("mainpage", view="mine"))

    trip_date = _parse_date_only(trip.get("travel_date"))
    today = datetime.now().date()
    if trip_date and trip_date > today:
        cur.close()
        db.close()
        flash("You can mark this trip completed only on or after the travel date.", "error")
        return redirect(request.referrer or url_for("mainpage", view="mine"))

    cur.execute("""
        SELECT COUNT(*) AS approved_count
        FROM trip_members
        WHERE post_id=%s
          AND status='approved'
    """, (post_id,))
    approved_count = int((cur.fetchone() or {}).get("approved_count") or 0)
    if approved_count <= 0:
        cur.close()
        db.close()
        flash("Add at least one approved traveler before marking a trip completed.", "error")
        return redirect(request.referrer or url_for("mainpage", view="mine"))

    cur.execute("""
        UPDATE travel_posts
        SET trip_status = 'completed',
            completed_at = NOW()
        WHERE post_id = %s
    """, (post_id,))
    _create_trip_system_message(
        cur,
        post_id,
        session["user_id"],
        "Trip was marked as closed by host.",
        event_type="system"
    )

    db.commit()

    cur.close()
    db.close()

    flash("Trip marked as completed. Travelers can now submit reviews.", "success")
    return redirect(url_for("mainpage", view="mine"))

@app.route("/approve_member/<int:member_id>", methods=["POST"])
@login_required
def approve_member(member_id):
    db = get_db_connection()
    cur = db.cursor()

    cur.execute("""
        SELECT tp.user_id AS host_id,
               tp.post_id,
               tp.destination,
               tm.user_id AS traveler_id,
               COALESCE(tm.member_name, u.username, 'Traveler') AS member_name
        FROM trip_members tm
        JOIN travel_posts tp ON tp.post_id = tm.post_id
        LEFT JOIN User_Details u ON u.user_id = tm.user_id
        WHERE tm.id = %s
    """, (member_id,))
    row = cur.fetchone()
    if not row or int(row["host_id"]) != int(session["user_id"]):
        cur.close()
        db.close()
        abort(403)

    cur.execute("""
        UPDATE trip_members
        SET status='approved'
        WHERE id=%s
    """, (member_id,))
    _create_trip_system_message(
        cur,
        int(row["post_id"]),
        session["user_id"],
        f"{row['member_name']} was approved to join this trip.",
        event_type="system"
    )
    # Notify the traveler
    if row.get("traveler_id"):
        _create_notification(
            cur,
            row["traveler_id"],
            "Trip Request Approved ✅",
            f"Your request to join '{row['destination']}' has been approved! You can now join the group chat.",
            ntype="trip",
            send_email=False
        )

    db.commit()
    cur.close()
    db.close()

    return redirect(request.referrer)

@app.route("/reject_member/<int:member_id>", methods=["POST"])
@login_required
def reject_member(member_id):
    db = get_db_connection()
    cur = db.cursor()

    cur.execute("""
        SELECT tp.user_id AS host_id,
               tp.post_id,
               tp.destination,
               tm.user_id AS traveler_id,
               COALESCE(tm.member_name, u.username, 'Traveler') AS member_name
        FROM trip_members tm
        JOIN travel_posts tp ON tp.post_id = tm.post_id
        LEFT JOIN User_Details u ON u.user_id = tm.user_id
        WHERE tm.id = %s
    """, (member_id,))
    row = cur.fetchone()
    if not row or int(row["host_id"]) != int(session["user_id"]):
        cur.close()
        db.close()
        abort(403)

    cur.execute("""
        UPDATE trip_members
        SET status='rejected'
        WHERE id=%s
    """, (member_id,))
    _create_trip_system_message(
        cur,
        int(row["post_id"]),
        session["user_id"],
        f"{row['member_name']} was rejected from this trip.",
        event_type="system"
    )
    # Notify the traveler
    if row.get("traveler_id"):
        _create_notification(
            cur,
            row["traveler_id"],
            "Trip Request Update",
            f"Your request to join '{row['destination']}' was not approved this time.",
            ntype="trip",
            send_email=False
        )

    db.commit()
    cur.close()
    db.close()

    return redirect(request.referrer)

@app.route("/admin/dashboard")
@admin_required
def admin_dashboard():
    db = get_db_connection()
    cur = db.cursor()
    admin_unread_count = get_admin_unread_private_count(cur, session["user_id"])

    cur.execute("SELECT COUNT(*) AS total FROM User_Details")
    users = cur.fetchone()["total"]

    cur.execute("SELECT COUNT(*) AS total FROM travel_posts")
    trips = cur.fetchone()["total"]

    cur.execute("SELECT COUNT(*) AS total FROM trip_members")
    members = cur.fetchone()["total"]

    stats = {
        "users": users,
        "trips": trips,
        "members": members
    }

    cur.execute("""
        SELECT h.user_id,
       h.full_name,
       h.phone,
       h.id_proof,
       h.verification_status,
       u.username
FROM host_profiles h
JOIN User_Details u ON u.user_id = h.user_id
WHERE h.verification_status = 'pending'
    """)
    hosts = cur.fetchall()

    cur.execute("""
        SELECT t.user_id,
               t.full_name,
               t.phone,
               t.id_proof,
               t.verification_status,
               u.username
        FROM traveler_profiles t
        JOIN User_Details u ON u.user_id = t.user_id
        WHERE t.verification_status = 'pending'
        ORDER BY t.user_id DESC
    """)
    travelers = cur.fetchall()

    cur.execute("""
        SELECT
            u.user_id,
            u.username,
            u.role,
            u.is_active,
            MAX(CASE WHEN ll.status = 'success' THEN ll.created_at END) AS last_login_at,
            SUBSTRING_INDEX(
                GROUP_CONCAT(
                    CASE WHEN ll.status = 'success' THEN COALESCE(ll.ip_address, '') END
                    ORDER BY ll.created_at DESC
                    SEPARATOR ','
                ),
                ',',
                1
            ) AS last_ip,
            SUM(
                CASE
                    WHEN ll.status = 'success'
                     AND ll.created_at >= (NOW() - INTERVAL 7 DAY)
                    THEN 1 ELSE 0
                END
            ) AS logins_7d
        FROM User_Details u
        LEFT JOIN login_logs ll ON ll.username = u.username
        GROUP BY u.user_id, u.username, u.role, u.is_active
        ORDER BY COALESCE(MAX(CASE WHEN ll.status = 'success' THEN ll.created_at END), '1970-01-01') DESC,
                 u.user_id DESC
        LIMIT 12
    """)
    recent_users = cur.fetchall()
    for row in recent_users:
        row["logins_7d"] = int(row.get("logins_7d") or 0)

    cur.close()
    db.close()

    return render_template(
        "admin.html",
        stats=stats,
        hosts=hosts,
        travelers=travelers,
        recent_users=recent_users,
        admin_unread_count=admin_unread_count
    )

@app.route("/admin/users")
@admin_required
def admin_users():
    db = get_db_connection()
    cur = db.cursor()
    admin_unread_count = get_admin_unread_private_count(cur, session["user_id"])

    cur.execute("""
        SELECT
            u.user_id,
            u.username,
            u.role,
            u.is_active,
            MAX(CASE WHEN ll.status = 'success' THEN ll.created_at END) AS last_login_at,
            SUBSTRING_INDEX(
                GROUP_CONCAT(
                    CASE WHEN ll.status = 'success' THEN COALESCE(ll.ip_address, '') END
                    ORDER BY ll.created_at DESC
                    SEPARATOR ','
                ),
                ',',
                1
            ) AS last_ip,
            SUM(
                CASE
                    WHEN ll.status = 'success'
                     AND ll.created_at >= (NOW() - INTERVAL 7 DAY)
                    THEN 1 ELSE 0
                END
            ) AS logins_7d
        FROM User_Details u
        LEFT JOIN login_logs ll ON ll.username = u.username
        GROUP BY u.user_id, u.username, u.role, u.is_active
        ORDER BY u.user_id DESC
    """)
    users = cur.fetchall()
    for row in users:
        row["logins_7d"] = int(row.get("logins_7d") or 0)

    cur.close()
    db.close()

    return render_template(
        "admin_users.html",
        users=users,
        admin_unread_count=admin_unread_count
    )

@app.route("/admin/toggle_user/<int:user_id>", methods=["POST"])
@admin_required
def toggle_user(user_id):

    if user_id == session.get("user_id"):
        abort(403)

    db = get_db_connection()
    cur = db.cursor()

    cur.execute("""
        SELECT is_active
        FROM User_Details
        WHERE user_id=%s
    """, (user_id,))

    user = cur.fetchone()

    if not user:
        cur.close()
        db.close()
        abort(404)

    current_status = bool(user["is_active"])
    new_status = 0 if current_status else 1

    cur.execute("""
        UPDATE User_Details
        SET is_active=%s
        WHERE user_id=%s
    """, (new_status, user_id))
    _write_admin_action(
        cur,
        session["user_id"],
        "toggle_user_status",
        "user",
        user_id,
        _safe_json_dumps({"is_active": new_status})
    )

    db.commit()
    cur.close()
    db.close()

    return redirect(url_for("admin_users"))

@app.route("/api/admin/<string:role>s/<int:profile_id>/reject", methods=["POST"])
@admin_required
def reject_profile(role, profile_id):

    if role not in ("host", "traveler"):
        return jsonify({"success": False, "error": "Invalid role"}), 400

    table = f"{role}_profiles"

    db = get_db_connection()
    cur = db.cursor()

    cur.execute(f"""
        UPDATE {table}
        SET verification_status='rejected'
        WHERE user_id=%s
    """, (profile_id,))
    _write_admin_action(
        cur,
        session["user_id"],
        "profile_reject",
        role,
        profile_id,
        _safe_json_dumps({"status": "rejected"})
    )
    _create_notification(
        cur,
        profile_id,
        "Verification Update",
        f"Your {role} verification was reviewed and needs changes. Please update your profile and resubmit.",
        ntype="verification",
        send_email=True
    )

    db.commit()
    cur.close()
    db.close()

    return jsonify({"success": True})

@app.route("/chat/<int:post_id>")
@login_required
def chat_trip(post_id):
    ensure_chat_schema()
    db = get_db_connection()
    cur = db.cursor()

    if not _is_user_in_trip_chat(cur, post_id, session["user_id"]):
        cur.close()
        db.close()
        abort(403)

    cur.execute("""
        SELECT tm.id,
               tm.message,
               tm.message_type,
               tm.created_at,
               tm.edited_at,
               tm.is_flagged,
               tm.moderation_status,
               tm.reply_to_id,
               rp.message AS reply_to_text,
               tm.attachment_path,
               tm.attachment_name,
               tm.attachment_type,
               tm.attachment_size,
               u.username,
               tm.user_id
        FROM trip_messages tm
        JOIN User_Details u ON u.user_id = tm.user_id
        LEFT JOIN trip_messages rp
          ON rp.id = tm.reply_to_id
        WHERE tm.post_id = %s
          AND tm.deleted_at IS NULL
        ORDER BY tm.id DESC
        LIMIT %s
    """, (post_id, CHAT_PAGE_SIZE))
    latest = cur.fetchall()
    messages = list(reversed(latest))
    message_ids = [int(m["id"]) for m in messages if m.get("id")]
    reaction_map = _fetch_reaction_map(cur, "group", message_ids)
    receipt_map = _fetch_receipt_counts(cur, "group", message_ids)
    star_map = _fetch_starred_map(cur, "group", message_ids, session["user_id"])
    for m in messages:
        mid = int(m["id"])
        m["reactions"] = reaction_map.get(mid, {})
        m["starred"] = int(star_map.get(mid, 0))
        m["attachment_url"] = _public_attachment_url(m.get("attachment_path"))
        rc = receipt_map.get(mid, {})
        m["delivered_count"] = int(rc.get("delivered_count") or 0)
        m["seen_count"] = int(rc.get("seen_count") or 0)
        m["recipient_count"] = int(rc.get("recipient_count") or 0)
        m["receipt_status"] = _receipt_status(
            m["delivered_count"],
            m["seen_count"],
            m["recipient_count"]
        )

    cur.execute("""
        SELECT COUNT(*) AS total_count
        FROM trip_messages
        WHERE post_id = %s
          AND deleted_at IS NULL
    """, (post_id,))
    count_row = cur.fetchone()
    total_count = int(count_row["total_count"] if count_row else 0)
    has_older = total_count > len(messages)

    cur.execute("""
        SELECT tp.trip_status, u.user_id, u.username
        FROM travel_posts tp
        JOIN User_Details u ON u.user_id = tp.user_id
        WHERE tp.post_id=%s
    """, (post_id,))
    trip_row = cur.fetchone()
    trip_status = trip_row["trip_status"] if trip_row else ""

    members = []
    host_id = None
    if trip_row:
        host_id = trip_row["user_id"]
        members.append({
            "user_id": trip_row["user_id"],
            "username": trip_row["username"],
            "role": "host"
        })

    cur.execute("""
        SELECT tm.user_id, u.username
        FROM trip_members tm
        JOIN User_Details u ON u.user_id = tm.user_id
        WHERE tm.post_id=%s
          AND tm.status='approved'
        ORDER BY u.username
    """, (post_id,))

    for row in cur.fetchall():
        if host_id is not None and row["user_id"] == host_id:
            continue
        members.append({
            "user_id": row["user_id"],
            "username": row["username"],
            "role": "traveler"
        })

    cur.execute("""
        SELECT last_read_at
        FROM trip_chat_reads
        WHERE post_id=%s
          AND user_id=%s
        LIMIT 1
    """, (post_id, session["user_id"]))
    read_row = cur.fetchone() or {}

    cur.execute("""
        SELECT pinned, archived, starred, muted_until, draft_text
        FROM chat_channel_user_state
        WHERE channel_type='group'
          AND channel_id=%s
          AND user_id=%s
        LIMIT 1
    """, (post_id, session["user_id"]))
    group_state = cur.fetchone() or {}

    cur.close()
    db.close()

    return render_template(
        "group_chat.html",
        post_id=post_id,
        messages=messages,
        has_older=has_older,
        trip_status=trip_status,
        members=members,
        host_id=host_id,
        can_broadcast=int(host_id or 0) == int(session["user_id"]),
        last_read_at=read_row.get("last_read_at"),
        conversation_pinned=int(group_state.get("pinned") or 0),
        conversation_archived=int(group_state.get("archived") or 0),
        conversation_starred=int(group_state.get("starred") or 0),
        conversation_muted_until=group_state.get("muted_until"),
        conversation_draft=group_state.get("draft_text") or ""
    )

@socketio.on("join_trip")
def join_trip_socket(data):
    ensure_chat_schema()
    trip_id = _parse_int(data.get("trip_id"))
    user_id = session.get("user_id")

    if not user_id or not trip_id:
        return _chat_ack(False, "invalid", error="Invalid trip")

    db = get_db_connection()
    cur = db.cursor()

    cur.execute("""
        SELECT 1 FROM travel_posts
        WHERE post_id=%s AND user_id=%s
        UNION
        SELECT 1 FROM trip_members
        WHERE post_id=%s AND user_id=%s AND status='approved'
    """, (trip_id, user_id, trip_id, user_id))

    allowed = cur.fetchone()

    cur.close()
    db.close()

    if not allowed:
        return _chat_ack(False, "forbidden", error="Not allowed")

    db2 = get_db_connection()
    cur2 = db2.cursor()
    _mark_group_delivered(cur2, trip_id, user_id)
    _touch_presence(cur2, user_id, True, str(trip_id))
    _save_channel_state(cur2, "group", trip_id, user_id, touch_open=True, touch_seen=True)
    _emit_receipt_snapshot(cur2, "group", trip_id, str(trip_id), "group_receipts_updated")
    db2.commit()
    cur2.close()
    db2.close()

    join_room(str(trip_id))
    return _chat_ack(True, "joined")

@socketio.on("leave_trip")
def leave_trip_socket(data):
    trip_id = _parse_int(data.get("trip_id"))
    user_id = session.get("user_id")

    if not user_id or not trip_id:
        return

    db = get_db_connection()
    cur = db.cursor()
    _touch_presence(cur, user_id, False, "")
    db.commit()
    cur.close()
    db.close()

    leave_room(str(trip_id))

@socketio.on("send_message")
def send_message(data):
    ensure_chat_schema()
    trip_id = _parse_int(data.get("trip_id"))
    message = _normalize_message(data.get("message", ""))
    client_id = str(data.get("client_id") or "").strip()[:64]
    reply_to_id = _parse_int(data.get("reply_to_id"))
    upload_id = _parse_int(data.get("upload_id"))
    user_id = session.get("user_id")

    if not user_id or not trip_id:
        return _chat_ack(False, "invalid", error="Message is invalid")
    if not message and not upload_id:
        return _chat_ack(False, "invalid", error="Message is invalid")
    if message and not _is_valid_message(message):
        return _chat_ack(False, "invalid", error="Message is invalid")

    if not _throttle_ok(user_id, f"group:{trip_id}"):
        return _chat_ack(False, "rate_limited", error="Please slow down")
    if not _redis_rate_ok_with_ip(user_id, f"group:{trip_id}", request.remote_addr):
        return _chat_ack(False, "rate_limited", error="Please slow down")

    db = get_db_connection()
    cur = db.cursor()

    if not _is_user_in_trip_chat(cur, trip_id, user_id):
        cur.close()
        db.close()
        return _chat_ack(False, "forbidden", error="Not allowed")

    cur.execute("""
        SELECT trip_status
        FROM travel_posts
        WHERE post_id = %s
    """, (trip_id,))
    trip_row = cur.fetchone()
    if not trip_row:
        cur.close()
        db.close()
        return _chat_ack(False, "not_found", error="Trip not found")

    if trip_row["trip_status"] in ("completed", "cancelled"):
        cur.close()
        db.close()
        return _chat_ack(False, "chat_closed", error="Chat is closed")

    if not _spam_window_ok(cur, "trip_messages", "post_id", trip_id, "user_id", user_id):
        cur.close()
        db.close()
        return _chat_ack(False, "spam_limited", error="Too many messages, slow down")

    if message and _is_duplicate_message(cur, "trip_messages", "post_id", trip_id, "user_id", user_id, message):
        cur.close()
        db.close()
        return _chat_ack(False, "duplicate", error="Duplicate message blocked")

    attachment_path = None
    attachment_name = None
    attachment_type = None
    attachment_size = None
    if upload_id:
        cur.execute("""
            SELECT id, rel_path, original_name, mime_type, file_size, is_malicious
            FROM chat_uploads
            WHERE id=%s
              AND owner_id=%s
              AND channel_type='group'
              AND channel_id=%s
              AND used_at IS NULL
            LIMIT 1
        """, (upload_id, user_id, trip_id))
        upload_row = cur.fetchone()
        if not upload_row:
            cur.close()
            db.close()
            return _chat_ack(False, "invalid_attachment", error="Attachment not found")
        if int(upload_row.get("is_malicious") or 0) == 1:
            cur.close()
            db.close()
            return _chat_ack(False, "invalid_attachment", error="Attachment blocked")
        attachment_path = upload_row.get("rel_path")
        attachment_name = upload_row.get("original_name")
        attachment_type = upload_row.get("mime_type")
        attachment_size = upload_row.get("file_size")
        cur.execute("UPDATE chat_uploads SET used_at=NOW() WHERE id=%s", (upload_id,))

    if reply_to_id:
        cur.execute("""
            SELECT id
            FROM trip_messages
            WHERE id=%s
              AND post_id=%s
              AND deleted_at IS NULL
            LIMIT 1
        """, (reply_to_id, trip_id))
        if not cur.fetchone():
            cur.close()
            db.close()
            return _chat_ack(False, "invalid_reply", error="Reply target not found")

    cur.execute("""
        INSERT INTO trip_messages (
            post_id, user_id, message, reply_to_id,
            attachment_path, attachment_name, attachment_type, attachment_size, message_type
        )
        VALUES (%s, %s, %s, %s, %s, %s, %s, %s, %s)
    """, (
        trip_id, user_id, message, reply_to_id,
        attachment_path, attachment_name, attachment_type, attachment_size,
        "attachment" if attachment_path else "text"
    ))

    message_id = cur.lastrowid
    cur.execute("SELECT created_at FROM trip_messages WHERE id = %s", (message_id,))
    row = cur.fetchone()
    created_at = row["created_at"] if row else datetime.now()
    _create_group_receipts(cur, trip_id, message_id, user_id)
    _mark_group_delivered(cur, trip_id, user_id)

    cur.execute("""
        SELECT user_id
        FROM travel_posts
        WHERE post_id=%s
        UNION
        SELECT user_id
        FROM trip_members
        WHERE post_id=%s
          AND status='approved'
    """, (trip_id, trip_id))
    recipients = [int(r["user_id"]) for r in cur.fetchall() if int(r["user_id"]) != int(user_id)]
    preview = message or (attachment_name and f"Attachment: {attachment_name}") or "New message"
    for recipient_id in recipients:
        _create_notification(
            cur,
            recipient_id,
            "New group message",
            f"{session.get('username', 'User')}: {preview}",
            ntype="chat",
            send_email=False
        )

    db.commit()
    cur.close()
    db.close()

    emit("message", {
        "trip_id": trip_id,
        "id": message_id,
        "user_id": user_id,
        "username": session.get("username", "User"),
        "message": message,
        "reply_to_id": reply_to_id,
        "created_at": created_at.strftime("%Y-%m-%d %H:%M:%S"),
        "edited_at": None,
        "is_flagged": 0,
        "attachment_path": attachment_path,
        "attachment_name": attachment_name,
        "attachment_type": attachment_type,
        "attachment_size": attachment_size,
        "attachment_url": (
            _public_attachment_url(attachment_path)
            if attachment_path else None
        ),
        "message_type": "attachment" if attachment_path else "text",
        "delivered_count": 0,
        "seen_count": 0,
        "recipient_count": max(0, len(recipients)),
        "receipt_status": "sent",
        "client_id": client_id
    }, room=str(trip_id))
    return _chat_ack(
        True,
        "sent",
        message_id=message_id,
        created_at=created_at.strftime("%Y-%m-%d %H:%M:%S"),
        client_id=client_id
    )
def notify_verification_update(user_id=None):
    socketio.emit("verification_updated", {
        "user_id": user_id
    })

@app.route("/members/<int:post_id>")
@login_required
def members(post_id):
    db = get_db_connection()
    cur = db.cursor()

    cur.execute("""
        SELECT user_id, destination
        FROM travel_posts
        WHERE post_id = %s
    """, (post_id,))
    trip = cur.fetchone()

    if not trip or trip["user_id"] != session["user_id"]:
        cur.close()
        db.close()
        abort(403)

    cur.execute("""
                SELECT tm.id,
                       tm.user_id,
                       tm.member_name,
                       tm.contact_no,
                       tm.language,
                       tm.amount_due,
                       tm.amount_paid,
                       (tm.amount_due - tm.amount_paid) AS remaining,
                       tm.payment_status,
                       tm.status,
                       tm.joined_at
                FROM trip_members tm
                WHERE tm.post_id = %s
                """, (post_id,))

    members = cur.fetchall()

    cur.close()
    db.close()

    return render_template(
        "members.html",
        members=members,
        destination=trip["destination"],
        post_id=post_id
    )

@app.route("/api/admin/<string:role>s/<int:profile_id>/approve", methods=["POST"])
@admin_required
def approve_profile(role, profile_id):

    if role not in ("host", "traveler"):
        return jsonify({"success": False, "error": "Invalid role"}), 400

    table = f"{role}_profiles"

    db = get_db_connection()
    cur = db.cursor()

    cur.execute(f"""
        UPDATE {table}
        SET verification_status='approved'
        WHERE user_id=%s
    """, (profile_id,))
    _write_admin_action(
        cur,
        session["user_id"],
        "profile_approve",
        role,
        profile_id,
        _safe_json_dumps({"status": "approved"})
    )
    _create_notification(
        cur,
        profile_id,
        "Verification Approved ✅",
        f"Your {role} verification has been approved. You can now continue using all related features.",
        ntype="verification",
        send_email=True
    )

    db.commit()
    cur.close()
    db.close()

    notify_verification_update(profile_id)

    return jsonify({"success": True})

@app.route("/payment/<int:member_id>", methods=["POST"])
@login_required
def update_payment(member_id):
    try:
        add_amount = float(request.form.get("amount", 0))
    except (TypeError, ValueError):
        abort(400)
    if add_amount <= 0:
        abort(400)

    db = get_db_connection()
    cur = db.cursor()

    # Get host ownership + current payment info
    cur.execute("""
        SELECT tp.user_id,
               tp.post_id,
               tm.amount_due,
               tm.amount_paid,
               COALESCE(tm.member_name, u.username, 'Traveler') AS member_name
        FROM trip_members tm
        JOIN travel_posts tp ON tm.post_id = tp.post_id
        LEFT JOIN User_Details u ON u.user_id = tm.user_id
        WHERE tm.id=%s
    """, (member_id,))
    row = cur.fetchone()

    if not row or row["user_id"] != session["user_id"]:
        cur.close()
        db.close()
        abort(403)

    due = float(row["amount_due"])
    paid = float(row["amount_paid"])

    new_paid = paid + add_amount

    if new_paid > due:
        new_paid = due

    if new_paid == 0:
        status = "unpaid"
    elif new_paid < due:
        status = "partial"
    else:
        status = "paid"

    cur.execute("""
        UPDATE trip_members
        SET amount_paid=%s,
            payment_status=%s
        WHERE id=%s
    """, (new_paid, status, member_id))
    _create_trip_system_message(
        cur,
        int(row["post_id"]),
        session["user_id"],
        f"Payment updated for {row['member_name']}: +{add_amount:.2f}, status {status}.",
        event_type="payment"
    )

    db.commit()
    cur.close()
    db.close()

    return redirect(url_for("members", post_id=request.form.get("post_id")))

@socketio.on("typing")
def typing(data):
    trip_id = _parse_int(data.get("trip_id"))
    user_id = session.get("user_id")
    if not user_id or not trip_id:
        return

    db = get_db_connection()
    cur = db.cursor()
    allowed = _is_user_in_trip_chat(cur, trip_id, user_id)
    cur.close()
    db.close()
    if not allowed:
        return

    emit("typing", {
        "trip_id": str(trip_id),
        "user_id": user_id
    }, room=str(trip_id), include_self=False)

@socketio.on("stop_typing")
def stop_typing(data):
    trip_id = _parse_int(data.get("trip_id"))
    user_id = session.get("user_id")
    if not user_id or not trip_id:
        return

    db = get_db_connection()
    cur = db.cursor()
    allowed = _is_user_in_trip_chat(cur, trip_id, user_id)
    cur.close()
    db.close()
    if not allowed:
        return

    emit("stop_typing", {
        "trip_id": str(trip_id),
        "user_id": user_id
    }, room=str(trip_id), include_self=False)

# ── PRIVATE CHAT TYPING EVENTS ──────────────────────────────────────────────

@socketio.on("typing_start")
def private_typing_start(data):
    """Emitted by private_chat.html when the user starts typing."""
    convo_id = _parse_int(data.get("conversation_id"))
    user_id  = session.get("user_id")
    if not convo_id or not user_id:
        return
    db  = get_db_connection()
    cur = db.cursor()
    allowed, _ = _can_access_private_conversation(cur, convo_id, user_id)
    cur.close()
    db.close()
    if not allowed:
        return
    emit("user_typing", {
        "conversation_id": convo_id,
        "user_id": user_id,
        "username": session.get("username", "")
    }, room=f"private_{convo_id}", include_self=False)

@socketio.on("typing_stop")
def private_typing_stop(data):
    """Emitted by private_chat.html when the user stops typing."""
    convo_id = _parse_int(data.get("conversation_id"))
    user_id  = session.get("user_id")
    if not convo_id or not user_id:
        return
    db  = get_db_connection()
    cur = db.cursor()
    allowed, _ = _can_access_private_conversation(cur, convo_id, user_id)
    cur.close()
    db.close()
    if not allowed:
        return
    emit("user_stopped_typing", {
        "conversation_id": convo_id,
        "user_id": user_id
    }, room=f"private_{convo_id}", include_self=False)

@app.route("/my_payments")
@login_required
def my_payments():
    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
        SELECT
            tm.id            AS member_id,
            tp.post_id,
            tp.destination,
            tp.travel_date,
            tm.member_name,
            tm.amount_due,
            tm.amount_paid,
            (tm.amount_due - tm.amount_paid) AS remaining,
            tm.payment_status,
            tm.status        AS join_status
        FROM trip_members tm
        JOIN travel_posts tp ON tp.post_id = tm.post_id
        WHERE tm.user_id=%s
        ORDER BY tp.travel_date DESC
    """, (session["user_id"],))

    payments = cur.fetchall()

    cur.close()
    db.close()

    return render_template("my_payments.html", payments=payments)

@app.route("/bulk_approve_members", methods=["POST"])
@login_required
def bulk_approve_members():
    ids = request.form.get("ids", "")
    id_list = [
        int(x) for x in ids.split(",")
        if x.strip().isdigit()
    ]
    if not id_list:
        return redirect(request.referrer or url_for("mainpage", view="mine"))

    conn = get_db_connection()
    cursor = conn.cursor()

    placeholders = ",".join(["%s"] * len(id_list))
    cursor.execute(f"""
        SELECT tm.id
        FROM trip_members tm
        JOIN travel_posts tp ON tp.post_id = tm.post_id
        WHERE tm.id IN ({placeholders})
          AND tp.user_id = %s
    """, (*id_list, session["user_id"]))
    allowed_ids = {int(row["id"]) for row in cursor.fetchall()}
    if len(allowed_ids) != len(set(id_list)):
        cursor.close()
        conn.close()
        abort(403)

    for member_id in id_list:
        cursor.execute("UPDATE trip_members SET status='approved' WHERE id=%s", (member_id,))

    conn.commit()
    cursor.close()
    conn.close()

    return redirect(request.referrer or url_for("mainpage", view="mine"))

@app.route("/bulk_reject_members", methods=["POST"])
@login_required
def bulk_reject_members():
    ids = request.form.get("ids", "")
    id_list = [
        int(x) for x in ids.split(",")
        if x.strip().isdigit()
    ]
    if not id_list:
        return redirect(request.referrer or url_for("mainpage", view="mine"))

    conn = get_db_connection()
    cursor = conn.cursor()

    placeholders = ",".join(["%s"] * len(id_list))
    cursor.execute(f"""
        SELECT tm.id
        FROM trip_members tm
        JOIN travel_posts tp ON tp.post_id = tm.post_id
        WHERE tm.id IN ({placeholders})
          AND tp.user_id = %s
    """, (*id_list, session["user_id"]))
    allowed_ids = {int(row["id"]) for row in cursor.fetchall()}
    if len(allowed_ids) != len(set(id_list)):
        cursor.close()
        conn.close()
        abort(403)

    for member_id in id_list:
        cursor.execute("UPDATE trip_members SET status='rejected' WHERE id=%s", (member_id,))

    conn.commit()
    cursor.close()
    conn.close()

    return redirect(request.referrer or url_for("mainpage", view="mine"))

@app.route("/host/dashboard")
@login_required
def host_dashboard():
    db = get_db_connection()
    cur = db.cursor()

    if not is_host_verified(session["user_id"]):
        cur.close()
        db.close()
        return redirect(url_for("host_profile"))

    cur.execute("""
        SELECT COUNT(*) AS total_trips
        FROM travel_posts
        WHERE user_id = %s
    """, (session["user_id"],))
    total_trips = cur.fetchone()["total_trips"]

    cur.execute("""
        SELECT COUNT(*) AS completed_trips
        FROM travel_posts
        WHERE user_id = %s
          AND trip_status = 'completed'
    """, (session["user_id"],))
    completed_trips = cur.fetchone()["completed_trips"]

    cur.execute("""
        SELECT COUNT(*) AS active_trips
        FROM travel_posts
        WHERE user_id = %s
          AND trip_status IN ('open', 'full')
    """, (session["user_id"],))
    active_trips = cur.fetchone()["active_trips"]

    cur.execute("""
        SELECT COUNT(DISTINCT tm.user_id) AS total_travelers
        FROM trip_members tm
        JOIN travel_posts tp ON tp.post_id = tm.post_id
        WHERE tp.user_id = %s
          AND tm.status = 'approved'
    """, (session["user_id"],))
    total_travelers = cur.fetchone()["total_travelers"]

    cur.execute("""
        SELECT COALESCE(SUM(tm.amount_paid), 0) AS total_earnings
        FROM trip_members tm
        JOIN travel_posts tp ON tp.post_id = tm.post_id
        WHERE tp.user_id = %s
          AND tm.payment_status = 'paid'
    """, (session["user_id"],))
    total_earnings = cur.fetchone()["total_earnings"]

    stats = {
        "total_trips": total_trips,
        "active_trips": active_trips,
        "completed_trips": completed_trips,
        "total_members": total_travelers,
        "total_travelers": total_travelers,
        "total_earnings": total_earnings,
        "avg_rating": "N/A"
    }

    cur.execute("""
        SELECT tp.post_id,
               tp.destination,
               tp.travel_date,
               tp.max_people,
               tp.trip_status,
               COUNT(DISTINCT CASE
                    WHEN tm.status = 'approved' THEN tm.user_id
               END) AS approved_members,
               COALESCE(
                    SUM(CASE
                        WHEN tm.payment_status = 'paid'
                        THEN tm.amount_paid
                    END),
                    0
               ) AS earnings
        FROM travel_posts tp
        LEFT JOIN trip_members tm
               ON tm.post_id = tp.post_id
        WHERE tp.user_id = %s
        GROUP BY tp.post_id
        ORDER BY tp.travel_date DESC
    """, (session["user_id"],))

    trips = cur.fetchall()

    cur.close()
    db.close()

    return render_template(
        "host_dashboard.html",
        stats=stats,
        trips=trips
    )


@app.route("/trip/<int:post_id>/review", methods=["POST"])
@login_required
def submit_trip_review(post_id):
    ensure_chat_schema()
    try:
        ensure_trip_feedback_schema()
    except Exception:
        flash("Review feature is temporarily unavailable.", "error")
        return redirect(url_for("trip_detail", post_id=post_id))
    user_id = int(session["user_id"])
    review_type = (request.form.get("review_type") or "").strip().lower()
    reviewee_user_id = _parse_int(request.form.get("reviewee_user_id")) or 0
    rating = _parse_int(request.form.get("rating"))
    comment = _normalize_message(request.form.get("comment") or "")
    if rating is None or rating < 1 or rating > 5:
        abort(400)
    if len(comment) > 1000:
        comment = comment[:1000]

    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
        SELECT post_id, user_id AS host_id, destination, trip_status
        FROM travel_posts
        WHERE post_id=%s
        LIMIT 1
    """, (post_id,))
    trip = cur.fetchone()
    if not trip:
        cur.close()
        db.close()
        abort(404)

    host_id = int(trip["host_id"] or 0)
    trip_status = str(trip.get("trip_status") or "")
    if trip_status != "completed":
        cur.close()
        db.close()
        abort(403)

    if review_type in {"trip", "host"}:
        if user_id == host_id:
            cur.close()
            db.close()
            abort(403)
        cur.execute("""
            SELECT status
            FROM trip_members
            WHERE post_id=%s
              AND user_id=%s
            LIMIT 1
        """, (post_id, user_id))
        member_row = cur.fetchone()
        if not member_row or str(member_row.get("status") or "") != "approved":
            cur.close()
            db.close()
            abort(403)
        reviewee_user_id = host_id if review_type == "host" else 0
    elif review_type == "traveler":
        if user_id != host_id:
            cur.close()
            db.close()
            abort(403)
        if reviewee_user_id <= 0 or reviewee_user_id == user_id:
            cur.close()
            db.close()
            abort(400)
        cur.execute("""
            SELECT status
            FROM trip_members
            WHERE post_id=%s
              AND user_id=%s
            LIMIT 1
        """, (post_id, reviewee_user_id))
        member_row = cur.fetchone()
        if not member_row or str(member_row.get("status") or "") != "approved":
            cur.close()
            db.close()
            abort(403)
    else:
        cur.close()
        db.close()
        abort(400)

    cur.execute("""
        INSERT INTO trip_reviews (
            post_id, review_type, reviewer_id, reviewee_user_id, rating, comment
        ) VALUES (%s, %s, %s, %s, %s, %s)
        ON DUPLICATE KEY UPDATE
            rating=VALUES(rating),
            comment=VALUES(comment),
            updated_at=NOW()
    """, (
        post_id,
        review_type,
        user_id,
        reviewee_user_id,
        rating,
        comment
    ))

    if review_type == "host":
        _create_notification(
            cur,
            host_id,
            "New Host Review ⭐",
            f"A traveler posted a host review for trip '{trip['destination']}'.",
            ntype="trip",
            send_email=False
        )
    elif review_type == "traveler":
        _create_notification(
            cur,
            reviewee_user_id,
            "Host Review Received ⭐",
            f"The host reviewed you for trip '{trip['destination']}'.",
            ntype="trip",
            send_email=False
        )

    db.commit()
    cur.close()
    db.close()
    return redirect(url_for("trip_detail", post_id=post_id))

@app.route('/trip/<int:post_id>')
@login_required
def trip_detail(post_id):
    feedback_enabled = True
    try:
        ensure_trip_feedback_schema()
    except Exception:
        feedback_enabled = False
    user_id = int(session["user_id"])
    db = get_db_connection()
    cur = db.cursor()
    cur.execute("""
                SELECT tp.*,
                       tp.user_id                     AS host_id,
                       u.username                     AS host_name,
                       hp.full_name                   AS host_full_name,
                       hp.phone                       AS host_phone,
                       hp.bio                         AS host_bio,
                       hp.verification_status         AS host_verification_status,
                       (SELECT COUNT(*)
                        FROM trip_members tm
                        WHERE tm.post_id = tp.post_id
                          AND tm.status = 'approved') AS joined
                FROM travel_posts tp
                         JOIN User_Details u ON u.user_id = tp.user_id
                         LEFT JOIN host_profiles hp ON hp.user_id = tp.user_id
                WHERE tp.post_id = %s
                """, (post_id,))
    trip_row = cur.fetchone()
    if not trip_row:
        cur.close()
        db.close()
        abort(404)

    trip = dict(trip_row)
    host_id = int(trip.get("host_id") or 0)
    is_host = host_id == user_id

    cur.execute("""
                SELECT status, amount_due, amount_paid,
                       (amount_due - amount_paid) AS remaining,
                       payment_status
                FROM trip_members
                WHERE post_id = %s
                  AND user_id = %s
                """, (post_id, user_id))
    join_row = cur.fetchone()
    is_joined = join_row is not None
    join_status = join_row["status"] if join_row else None
    can_view_host_contact = is_host or (is_joined and str(join_status or "") == "approved")
    can_report_reviews = is_host or (is_joined and str(join_status or "") == "approved") or session.get("role") == "admin"

    if join_row:
        trip["amount_paid"] = join_row["amount_paid"]
        trip["remaining"] = join_row["remaining"]
        trip["payment_status"] = join_row["payment_status"]

    members = []
    if is_host:
        cur.execute("""
                    SELECT tm.*, u.username AS name
                    FROM trip_members tm
                             JOIN User_Details u ON u.user_id = tm.user_id
                    WHERE tm.post_id = %s
                    """, (post_id,))
        members = cur.fetchall()

    hosted_trips_count = 0
    completed_trips_count = 0
    cur.execute("""
                SELECT COUNT(*) AS hosted_count,
                       SUM(CASE WHEN trip_status = 'completed' THEN 1 ELSE 0 END) AS completed_count
                FROM travel_posts
                WHERE user_id = %s
                """, (host_id,))
    host_trip_counts = cur.fetchone() or {}
    hosted_trips_count = int(host_trip_counts.get("hosted_count") or 0)
    completed_trips_count = int(host_trip_counts.get("completed_count") or 0)

    trip_reviews = []
    host_reviews_count = 0
    host_avg_rating = None
    host_recent_reviews = []

    can_traveler_review = (
        (not is_host)
        and is_joined
        and str(join_status or "") == "approved"
        and str(trip.get("trip_status") or "") == "completed"
        and feedback_enabled
    )

    traveler_trip_review = None
    traveler_host_review = None
    can_host_review_travelers = (
        is_host
        and str(trip.get("trip_status") or "") == "completed"
        and feedback_enabled
    )
    host_reviews_by_user = {}

    if feedback_enabled:
        try:
            cur.execute("""
                SELECT r.id, r.reviewer_id, r.rating, r.comment, r.created_at, r.is_flagged, u.username AS reviewer_name
                FROM trip_reviews r
                JOIN User_Details u ON u.user_id = r.reviewer_id
                WHERE r.post_id=%s
                  AND r.review_type='trip'
                  AND COALESCE(r.moderation_status, 'clear') != 'removed'
                ORDER BY r.created_at DESC
                LIMIT 50
            """, (post_id,))
            trip_reviews = cur.fetchall()

            cur.execute("""
                SELECT COUNT(*) AS review_count, AVG(rating) AS avg_rating
                FROM trip_reviews
                WHERE review_type='host'
                  AND reviewee_user_id=%s
                  AND COALESCE(moderation_status, 'clear') != 'removed'
            """, (host_id,))
            host_rating_row = cur.fetchone() or {}
            host_reviews_count = int(host_rating_row.get("review_count") or 0)
            host_avg_rating = host_rating_row.get("avg_rating")
            if host_avg_rating is not None:
                host_avg_rating = round(float(host_avg_rating), 2)

            cur.execute("""
                SELECT
                    r.id,
                    r.reviewer_id,
                    r.rating,
                    r.comment,
                    r.created_at,
                    r.is_flagged,
                    u.username AS reviewer_name,
                    tp.destination
                FROM trip_reviews r
                JOIN User_Details u ON u.user_id = r.reviewer_id
                LEFT JOIN travel_posts tp ON tp.post_id = r.post_id
                WHERE r.review_type='host'
                  AND r.reviewee_user_id=%s
                  AND COALESCE(r.moderation_status, 'clear') != 'removed'
                ORDER BY r.created_at DESC
                LIMIT 8
            """, (host_id,))
            host_recent_reviews = cur.fetchall()

            if can_traveler_review:
                cur.execute("""
                    SELECT rating, comment
                    FROM trip_reviews
                    WHERE post_id=%s
                      AND review_type='trip'
                      AND reviewer_id=%s
                      AND reviewee_user_id=0
                    LIMIT 1
                """, (post_id, user_id))
                traveler_trip_review = cur.fetchone()
                cur.execute("""
                    SELECT rating, comment
                    FROM trip_reviews
                    WHERE post_id=%s
                      AND review_type='host'
                      AND reviewer_id=%s
                      AND reviewee_user_id=%s
                    LIMIT 1
                """, (post_id, user_id, host_id))
                traveler_host_review = cur.fetchone()

            if can_host_review_travelers and members:
                approved_ids = [int(m["user_id"]) for m in members if str(m.get("status") or "") == "approved"]
                if approved_ids:
                    placeholders = ",".join(["%s"] * len(approved_ids))
                    cur.execute(f"""
                        SELECT reviewee_user_id, rating, comment, created_at, updated_at
                        FROM trip_reviews
                        WHERE post_id=%s
                          AND review_type='traveler'
                          AND reviewer_id=%s
                          AND reviewee_user_id IN ({placeholders})
                    """, (post_id, user_id, *approved_ids))
                    host_reviews_by_user = {
                        int(row["reviewee_user_id"]): row
                        for row in cur.fetchall()
                    }
        except Exception:
            feedback_enabled = False
            can_traveler_review = False
            can_host_review_travelers = False
            trip_reviews = []
            host_reviews_count = 0
            host_avg_rating = None
            host_recent_reviews = []
            traveler_trip_review = None
            traveler_host_review = None
            host_reviews_by_user = {}

    banner_color_list = [
        '#e8622a,#f5a623',
        '#2a7d4f,#34d399',
        '#1d6fa4,#60a5fa',
        '#7c3aed,#a78bfa',
        '#be185d,#f472b6',
        '#b45309,#fbbf24'
    ]
    banner_gradient = banner_color_list[post_id % 6]

    cur.close()
    db.close()

    return render_template(
        "trip_detail.html",
        trip=trip,
        is_host=is_host,
        is_joined=is_joined,
        members=members,
        join_status=join_status,
        banner_gradient=banner_gradient,
        trip_photos=[],
        trip_reviews=trip_reviews,
        host_avg_rating=host_avg_rating,
        host_reviews_count=host_reviews_count,
        host_recent_reviews=host_recent_reviews,
        hosted_trips_count=hosted_trips_count,
        completed_trips_count=completed_trips_count,
        can_view_host_contact=can_view_host_contact,
        can_report_reviews=can_report_reviews,
        current_user_id=user_id,
        can_traveler_review=can_traveler_review,
        traveler_trip_review=traveler_trip_review,
        traveler_host_review=traveler_host_review,
        can_host_review_travelers=can_host_review_travelers,
        host_reviews_by_user=host_reviews_by_user,
        user_reviewed=bool(traveler_trip_review or traveler_host_review)
    )

@app.after_request
def add_no_cache_headers(response):
    response.headers["Cache-Control"] = "no-cache, no-store, must-revalidate"
    response.headers["Pragma"] = "no-cache"
    response.headers["Expires"] = "0"
    return response

@app.route("/logout")
def logout():
    session.clear()
    return redirect(url_for("home"))

if __name__ == "__main__":
    socketio.run(app, debug=True)