# Database Migrations (Alembic)

This project now includes Alembic scaffolding for versioned schema changes.

## Setup

1. Install dependencies:
   - `pip install alembic sqlalchemy pymysql`
2. Set DB environment variables:
   - `DB_HOST`
   - `DB_USER`
   - `DB_PASSWORD`
   - `DB_NAME`

## Commands

- Create a migration:
  - `alembic revision -m "add new chat index"`
- Apply latest migrations:
  - `alembic upgrade head`
- Roll back one migration:
  - `alembic downgrade -1`
- Show current revision:
  - `alembic current`

## Notes

- Current app runtime still calls `ensure_chat_schema()` for backward compatibility.
- New schema changes should be added through Alembic revisions instead of inline runtime DDL.
