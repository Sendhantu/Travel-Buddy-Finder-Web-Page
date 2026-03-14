from datetime import date, timedelta

from flask import session

import app as app_module


class LifecycleCursor:
    def __init__(self, state):
        self.state = state
        self._one = None
        self._all = []
        self.lastrowid = 0

    def execute(self, sql, params=None):
        normalized = " ".join((sql or "").lower().split())
        self._one = None
        self._all = []
        params = params or ()

        if "select user_id, trip_status, travel_date from travel_posts" in normalized:
            post_id = int(params[0])
            trip = self.state["travel_posts"].get(post_id)
            self._one = {
                "user_id": trip["user_id"],
                "trip_status": trip["trip_status"],
                "travel_date": trip["travel_date"],
            } if trip else None
            return 1

        if "select count(*) as approved_count from trip_members" in normalized:
            post_id = int(params[0])
            count = sum(
                1 for m in self.state["trip_members"]
                if int(m["post_id"]) == post_id and str(m["status"]) == "approved"
            )
            self._one = {"approved_count": count}
            return 1

        if "update travel_posts set trip_status = 'completed'" in normalized:
            post_id = int(params[0])
            self.state["travel_posts"][post_id]["trip_status"] = "completed"
            return 1

        if "select post_id, user_id as host_id, destination, trip_status from travel_posts" in normalized:
            post_id = int(params[0])
            trip = self.state["travel_posts"].get(post_id)
            self._one = {
                "post_id": post_id,
                "host_id": trip["user_id"],
                "destination": trip["destination"],
                "trip_status": trip["trip_status"],
            } if trip else None
            return 1

        if "select status from trip_members" in normalized and "where post_id=%s and user_id=%s" in normalized:
            post_id = int(params[0])
            user_id = int(params[1])
            row = next(
                (
                    {"status": m["status"]}
                    for m in self.state["trip_members"]
                    if int(m["post_id"]) == post_id and int(m["user_id"]) == user_id
                ),
                None
            )
            self._one = row
            return 1

        if "insert into trip_reviews" in normalized:
            post_id, review_type, reviewer_id, reviewee_user_id, rating, comment = params
            row = next(
                (
                    r for r in self.state["trip_reviews"]
                    if int(r["post_id"]) == int(post_id)
                    and str(r["review_type"]) == str(review_type)
                    and int(r["reviewer_id"]) == int(reviewer_id)
                    and int(r["reviewee_user_id"]) == int(reviewee_user_id)
                ),
                None
            )
            if row is None:
                self.state["trip_reviews"].append({
                    "post_id": int(post_id),
                    "review_type": str(review_type),
                    "reviewer_id": int(reviewer_id),
                    "reviewee_user_id": int(reviewee_user_id),
                    "rating": int(rating),
                    "comment": str(comment),
                })
            else:
                row["rating"] = int(rating)
                row["comment"] = str(comment)
            self.lastrowid = len(self.state["trip_reviews"])
            return 1

        return 0

    def fetchone(self):
        return self._one

    def fetchall(self):
        return self._all

    def close(self):
        return None


class LifecycleDB:
    def __init__(self, state):
        self.state = state
        self.cursor_obj = LifecycleCursor(state)
        self.commits = 0

    def cursor(self):
        return self.cursor_obj

    def commit(self):
        self.commits += 1

    def close(self):
        return None


def _patch_common(monkeypatch, fake_db):
    monkeypatch.setattr(app_module, "get_db_connection", lambda: fake_db)
    monkeypatch.setattr(app_module, "_create_trip_system_message", lambda *args, **kwargs: None)
    monkeypatch.setattr(app_module, "_create_notification", lambda *args, **kwargs: None)
    monkeypatch.setattr(app_module, "ensure_chat_schema", lambda: None)
    monkeypatch.setattr(app_module, "ensure_trip_feedback_schema", lambda: None)
    app_module.app.config["TESTING"] = True


def test_lifecycle_approved_join_then_complete_then_both_reviews(monkeypatch):
    post_id = 901
    host_id = 11
    traveler_id = 22
    state = {
        "travel_posts": {
            post_id: {
                "user_id": host_id,
                "destination": "Coorg",
                "trip_status": "open",
                "travel_date": (date.today() - timedelta(days=1)).strftime("%Y-%m-%d"),
            }
        },
        "trip_members": [
            {"post_id": post_id, "user_id": traveler_id, "status": "approved"},
        ],
        "trip_reviews": [],
    }
    fake_db = LifecycleDB(state)
    _patch_common(monkeypatch, fake_db)

    with app_module.app.test_request_context(f"/complete/{post_id}", method="POST"):
        session["user_id"] = host_id
        resp = app_module.complete_trip(post_id)
    assert resp.status_code == 302
    assert state["travel_posts"][post_id]["trip_status"] == "completed"

    with app_module.app.test_request_context(f"/trip/{post_id}/review", method="POST", data={
        "review_type": "host", "rating": "5", "comment": "Excellent host"
    }):
        session["user_id"] = traveler_id
        resp = app_module.submit_trip_review(post_id)
    assert resp.status_code == 302

    with app_module.app.test_request_context(f"/trip/{post_id}/review", method="POST", data={
        "review_type": "traveler", "reviewee_user_id": str(traveler_id), "rating": "5", "comment": "Great traveler"
    }):
        session["user_id"] = host_id
        resp = app_module.submit_trip_review(post_id)
    assert resp.status_code == 302

    assert len(state["trip_reviews"]) == 2
    assert any(r["review_type"] == "host" and r["reviewer_id"] == traveler_id and r["reviewee_user_id"] == host_id for r in state["trip_reviews"])
    assert any(r["review_type"] == "traveler" and r["reviewer_id"] == host_id and r["reviewee_user_id"] == traveler_id for r in state["trip_reviews"])


def test_complete_trip_requires_at_least_one_approved_member(monkeypatch):
    post_id = 902
    host_id = 11
    state = {
        "travel_posts": {
            post_id: {
                "user_id": host_id,
                "destination": "Pondicherry",
                "trip_status": "open",
                "travel_date": date.today().strftime("%Y-%m-%d"),
            }
        },
        "trip_members": [
            {"post_id": post_id, "user_id": 33, "status": "pending"},
        ],
        "trip_reviews": [],
    }
    fake_db = LifecycleDB(state)
    _patch_common(monkeypatch, fake_db)

    with app_module.app.test_request_context(f"/complete/{post_id}", method="POST"):
        session["user_id"] = host_id
        resp = app_module.complete_trip(post_id)

    assert resp.status_code == 302
    assert state["travel_posts"][post_id]["trip_status"] == "open"
    assert fake_db.commits == 0
