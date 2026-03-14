"""Add moderation fields for trip reviews.

Revision ID: 20260311_0002
Revises: 20260304_0001
Create Date: 2026-03-11 00:00:00
"""

from alembic import op
from sqlalchemy import text


# revision identifiers, used by Alembic.
revision = "20260311_0002"
down_revision = "20260304_0001"
branch_labels = None
depends_on = None


def _column_exists(conn, table_name: str, column_name: str) -> bool:
    row = conn.execute(
        text(
            """
            SELECT 1
            FROM information_schema.columns
            WHERE table_schema = DATABASE()
              AND table_name = :table_name
              AND column_name = :column_name
            LIMIT 1
            """
        ),
        {"table_name": table_name, "column_name": column_name},
    ).fetchone()
    return bool(row)


def _index_exists(conn, table_name: str, index_name: str) -> bool:
    row = conn.execute(
        text(
            """
            SELECT 1
            FROM information_schema.statistics
            WHERE table_schema = DATABASE()
              AND table_name = :table_name
              AND index_name = :index_name
            LIMIT 1
            """
        ),
        {"table_name": table_name, "index_name": index_name},
    ).fetchone()
    return bool(row)


def upgrade() -> None:
    conn = op.get_bind()
    op.execute("ALTER TABLE travel_posts ADD COLUMN IF NOT EXISTS itinerary TEXT NULL")
    op.execute(
        """
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
        """
    )

    if not _column_exists(conn, "trip_reviews", "is_flagged"):
        op.execute("ALTER TABLE trip_reviews ADD COLUMN is_flagged TINYINT(1) NOT NULL DEFAULT 0")
    if not _column_exists(conn, "trip_reviews", "moderation_status"):
        op.execute("ALTER TABLE trip_reviews ADD COLUMN moderation_status VARCHAR(20) NOT NULL DEFAULT 'clear'")
    if not _column_exists(conn, "trip_reviews", "moderated_at"):
        op.execute("ALTER TABLE trip_reviews ADD COLUMN moderated_at DATETIME NULL")
    if not _column_exists(conn, "trip_reviews", "moderated_by"):
        op.execute("ALTER TABLE trip_reviews ADD COLUMN moderated_by INT NULL")
    if not _index_exists(conn, "trip_reviews", "idx_trip_reviews_flag_status"):
        op.execute(
            """
            CREATE INDEX idx_trip_reviews_flag_status
            ON trip_reviews (is_flagged, moderation_status, created_at)
            """
        )


def downgrade() -> None:
    conn = op.get_bind()
    if _index_exists(conn, "trip_reviews", "idx_trip_reviews_flag_status"):
        op.execute("DROP INDEX idx_trip_reviews_flag_status ON trip_reviews")
    if _column_exists(conn, "trip_reviews", "moderated_by"):
        op.execute("ALTER TABLE trip_reviews DROP COLUMN moderated_by")
    if _column_exists(conn, "trip_reviews", "moderated_at"):
        op.execute("ALTER TABLE trip_reviews DROP COLUMN moderated_at")
    if _column_exists(conn, "trip_reviews", "moderation_status"):
        op.execute("ALTER TABLE trip_reviews DROP COLUMN moderation_status")
    if _column_exists(conn, "trip_reviews", "is_flagged"):
        op.execute("ALTER TABLE trip_reviews DROP COLUMN is_flagged")
