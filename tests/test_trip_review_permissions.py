import pytest
from werkzeug.exceptions import HTTPException

from flask import session

import app as app_module


class ReviewCursor:
    def __init__(self, host_id=10, trip_status="completed", member_status_by_user=None):
        self.host_id = int(host_id)
        self.trip_status = trip_status
        self.member_status_by_user = member_status_by_user or {}
        self._one = None
        self._all = []
        self.review_upserts = []

    def execute(self, sql, params=None):
        normalized = " ".join((sql or "").lower().split())
        self._one = None
        self._all = []

        if "from travel_posts" in normalized and "where post_id=%s" in normalized and "limit 1" in normalized:
            self._one = {
                "post_id": int((params or [0])[0]),
                "host_id": self.host_id,
                "destination": "Goa",
                "trip_status": self.trip_status,
            }
            return 1

        if "from trip_members" in normalized and "where post_id=%s" in normalized and "and user_id=%s" in normalized:
            uid = int((params or [0, 0])[1])
            status = self.member_status_by_user.get(uid)
            if status is not None:
                self._one = {"status": status}
            return 1

        if "insert into trip_reviews" in normalized:
            self.review_upserts.append(params)
            return 1

        return 0

    def fetchone(self):
        return self._one

    def fetchall(self):
        return self._all

    def close(self):
        return None


class ReviewDB:
    def __init__(self, cursor):
        self.cursor_obj = cursor
        self.committed = False

    def cursor(self):
        return self.cursor_obj

    def commit(self):
        self.committed = True

    def close(self):
        return None


def _invoke_submit(monkeypatch, fake_db, post_id, form_data, session_user_id):
    monkeypatch.setattr(app_module, "ensure_chat_schema", lambda: None)
    monkeypatch.setattr(app_module, "ensure_trip_feedback_schema", lambda: None)
    monkeypatch.setattr(app_module, "get_db_connection", lambda: fake_db)
    monkeypatch.setattr(app_module, "_create_notification", lambda *args, **kwargs: None)
    app_module.app.config["TESTING"] = True

    with app_module.app.test_request_context(
        f"/trip/{post_id}/review",
        method="POST",
        data=form_data
    ):
        session["user_id"] = int(session_user_id)
        return app_module.submit_trip_review(post_id)


def test_traveler_cannot_review_before_trip_completed(monkeypatch):
    cursor = ReviewCursor(host_id=9, trip_status="open", member_status_by_user={21: "approved"})
    fake_db = ReviewDB(cursor)

    with pytest.raises(HTTPException) as exc:
        _invoke_submit(
            monkeypatch,
            fake_db,
            post_id=51,
            form_data={"review_type": "host", "rating": "5", "comment": "Great host"},
            session_user_id=21
        )
    assert exc.value.code == 403

    assert fake_db.committed is False
    assert cursor.review_upserts == []


def test_traveler_can_review_host_after_trip_completed(monkeypatch):
    cursor = ReviewCursor(host_id=9, trip_status="completed", member_status_by_user={21: "approved"})
    fake_db = ReviewDB(cursor)

    response = _invoke_submit(
        monkeypatch,
        fake_db,
        post_id=52,
        form_data={"review_type": "host", "rating": "4", "comment": "Well managed"},
        session_user_id=21
    )

    assert response.status_code == 302
    assert fake_db.committed is True
    assert len(cursor.review_upserts) == 1
    inserted = cursor.review_upserts[0]
    assert inserted[1] == "host"
    assert inserted[2] == 21
    assert inserted[3] == 9


def test_host_can_review_approved_traveler(monkeypatch):
    cursor = ReviewCursor(host_id=9, trip_status="completed", member_status_by_user={22: "approved"})
    fake_db = ReviewDB(cursor)

    response = _invoke_submit(
        monkeypatch,
        fake_db,
        post_id=53,
        form_data={"review_type": "traveler", "reviewee_user_id": "22", "rating": "5", "comment": "Great traveler"},
        session_user_id=9
    )

    assert response.status_code == 302
    assert fake_db.committed is True
    assert len(cursor.review_upserts) == 1
    inserted = cursor.review_upserts[0]
    assert inserted[1] == "traveler"
    assert inserted[2] == 9
    assert inserted[3] == 22


def test_host_cannot_review_unapproved_traveler(monkeypatch):
    cursor = ReviewCursor(host_id=9, trip_status="completed", member_status_by_user={22: "pending"})
    fake_db = ReviewDB(cursor)

    with pytest.raises(HTTPException) as exc:
        _invoke_submit(
            monkeypatch,
            fake_db,
            post_id=54,
            form_data={"review_type": "traveler", "reviewee_user_id": "22", "rating": "3", "comment": "Pending member"},
            session_user_id=9
        )
    assert exc.value.code == 403

    assert fake_db.committed is False
    assert cursor.review_upserts == []
