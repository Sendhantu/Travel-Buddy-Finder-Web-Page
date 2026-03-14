"""Baseline migration for chat system state.

Revision ID: 20260304_0001
Revises:
Create Date: 2026-03-04 00:00:00
"""

from alembic import op


# revision identifiers, used by Alembic.
revision = "20260304_0001"
down_revision = None
branch_labels = None
depends_on = None


def upgrade() -> None:
    # Existing deployments already create tables through ensure_chat_schema().
    # This baseline migration anchors future versioned SQL migrations.
    op.execute("SELECT 1")


def downgrade() -> None:
    op.execute("SELECT 1")
