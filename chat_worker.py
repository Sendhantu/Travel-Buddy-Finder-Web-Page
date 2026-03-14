#!/usr/bin/env python3
import os
import time
from datetime import datetime

from app import (
    app,
    ensure_chat_schema,
    get_db_connection,
    _run_background_jobs,
    _process_due_scheduled_messages,
)

POLL_SECONDS = max(5, int(os.environ.get("CHAT_WORKER_POLL_SECONDS", "20")))
BATCH_LIMIT = max(10, min(300, int(os.environ.get("CHAT_WORKER_BATCH_LIMIT", "120"))))
ONESHOT = os.environ.get("CHAT_WORKER_ONESHOT", "0").strip() == "1"


def _run_once():
    ensure_chat_schema()
    db = get_db_connection()
    cur = db.cursor()
    try:
        job_summary = _run_background_jobs(cur, limit=BATCH_LIMIT)
        sched_summary = _process_due_scheduled_messages(cur, limit=BATCH_LIMIT)
        db.commit()
        return job_summary, sched_summary
    except Exception:
        db.rollback()
        raise
    finally:
        cur.close()
        db.close()


def main():
    with app.app_context():
        while True:
            now = datetime.now().strftime("%Y-%m-%d %H:%M:%S")
            try:
                jobs, sched = _run_once()
                if jobs.get("total") or sched.get("total"):
                    print(
                        f"[{now}] jobs={jobs.get('processed', 0)}/{jobs.get('total', 0)} "
                        f"failed={jobs.get('failed', 0)} "
                        f"scheduled_sent={sched.get('sent', 0)} scheduled_failed={sched.get('failed', 0)}",
                        flush=True,
                    )
            except Exception as exc:
                print(f"[{now}] worker_error: {exc}", flush=True)

            if ONESHOT:
                break
            time.sleep(POLL_SECONDS)


if __name__ == "__main__":
    main()
