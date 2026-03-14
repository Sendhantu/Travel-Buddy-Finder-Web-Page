from datetime import datetime

from flask import session

import app as app_module


class FakeCursor:
    def __init__(self):
        self._one = None
        self._all = []
        self.lastrowid = 0

    def execute(self, sql, params=None):
        normalized = " ".join((sql or "").lower().split())
        self._one = None
        self._all = []

        if "select trip_status" in normalized:
            self._one = {"trip_status": "open"}
        elif "insert into trip_messages" in normalized:
            self.lastrowid = 99
        elif "select created_at from trip_messages where id" in normalized:
            self._one = {"created_at": datetime(2026, 1, 1, 10, 0, 0)}
        elif "select user_id" in normalized and "from travel_posts" in normalized:
            self._all = [{"user_id": 1}, {"user_id": 2}]

    def fetchone(self):
        return self._one

    def fetchall(self):
        return self._all

    def close(self):
        return None


class FakeDB:
    def __init__(self):
        self.cursor_obj = FakeCursor()
        self.committed = False

    def cursor(self):
        return self.cursor_obj

    def commit(self):
        self.committed = True

    def close(self):
        return None



def _patch_common(monkeypatch, fake_db):
    monkeypatch.setattr(app_module, "ensure_chat_schema", lambda: None)
    monkeypatch.setattr(app_module, "get_db_connection", lambda: fake_db)
    monkeypatch.setattr(app_module, "_throttle_ok", lambda *args, **kwargs: True)
    monkeypatch.setattr(app_module, "_redis_rate_ok_with_ip", lambda *args, **kwargs: True)
    monkeypatch.setattr(app_module, "emit", lambda *args, **kwargs: None)



def test_send_message_forbidden_when_not_member(monkeypatch):
    fake_db = FakeDB()
    _patch_common(monkeypatch, fake_db)
    monkeypatch.setattr(app_module, "_is_user_in_trip_chat", lambda *args, **kwargs: False)

    with app_module.app.test_request_context("/", environ_base={"REMOTE_ADDR": "127.0.0.1"}):
        session["user_id"] = 1
        session["username"] = "host"
        ack = app_module.send_message({"trip_id": 11, "message": "hello"})

    assert ack["ok"] is False
    assert ack["code"] == "forbidden"
    assert fake_db.committed is False



def test_send_message_spam_limited(monkeypatch):
    fake_db = FakeDB()
    _patch_common(monkeypatch, fake_db)
    monkeypatch.setattr(app_module, "_is_user_in_trip_chat", lambda *args, **kwargs: True)
    monkeypatch.setattr(app_module, "_spam_window_ok", lambda *args, **kwargs: False)

    with app_module.app.test_request_context("/", environ_base={"REMOTE_ADDR": "127.0.0.1"}):
        session["user_id"] = 1
        session["username"] = "host"
        ack = app_module.send_message({"trip_id": 11, "message": "hello"})

    assert ack["ok"] is False
    assert ack["code"] == "spam_limited"
    assert fake_db.committed is False



def test_send_message_success_commits(monkeypatch):
    fake_db = FakeDB()
    _patch_common(monkeypatch, fake_db)
    monkeypatch.setattr(app_module, "_is_user_in_trip_chat", lambda *args, **kwargs: True)
    monkeypatch.setattr(app_module, "_spam_window_ok", lambda *args, **kwargs: True)
    monkeypatch.setattr(app_module, "_is_duplicate_message", lambda *args, **kwargs: False)
    monkeypatch.setattr(app_module, "_create_group_receipts", lambda *args, **kwargs: None)
    monkeypatch.setattr(app_module, "_mark_group_delivered", lambda *args, **kwargs: None)
    monkeypatch.setattr(app_module, "_create_notification", lambda *args, **kwargs: None)

    with app_module.app.test_request_context("/", environ_base={"REMOTE_ADDR": "127.0.0.1"}):
        session["user_id"] = 1
        session["username"] = "host"
        ack = app_module.send_message({"trip_id": 11, "message": "hello world", "client_id": "cid-1"})

    assert ack["ok"] is True
    assert ack["code"] == "sent"
    assert fake_db.committed is True



def test_attachment_route_rejects_path_traversal(monkeypatch):
    monkeypatch.setattr(app_module, "ensure_chat_schema", lambda: None)
    app_module.app.config["TESTING"] = True

    with app_module.app.test_client() as client:
        with client.session_transaction() as sess:
            sess["user_id"] = 99
        res = client.get("/chat/attachment/%2E%2E/evil.txt")
    assert res.status_code == 404



def test_public_attachment_url_points_to_protected_route():
    with app_module.app.test_request_context("/"):
        url = app_module._public_attachment_url("uploads/chat/group/8/sample.pdf")
    assert "/chat/attachment/uploads/chat/group/8/sample.pdf" in url
