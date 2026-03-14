# Travel-Buddy-Finder-Web-Page
This Travel Buddy Finder Web Page helps find travellers a group and host a group to travel together, either Host or Traveller can choose from where they want to and with whom they want to.
# TravelBuddyFinder

TravelBuddyFinder is a Flask-based travel companion platform where users can create trips, request to join trips, manage host approvals, chat with members, and receive trip-related updates. The project also includes admin moderation tools, support workflows, reviews, and a development-friendly notification system.

## Features

- User registration, login, password reset, CSRF protection, and login attempt tracking
- Host and traveler profile flows, including host verification and admin approval/rejection
- Trip creation, editing, deletion, join requests, member approval/rejection, and trip completion
- Main dashboard for exploring trips, hosted trips, and joined trips
- Host dashboard with filters, export, trip management, and member views
- Group trip chat and private chat using Flask-SocketIO
- Chat attachments, reactions, starring, drafts, scheduled messages, exports, and support escalation
- In-app notifications plus development-mode email and SMS delivery hooks
- Admin tools for verification, moderation, user management, audit logs, message search, analytics, and broadcast updates
- Post-trip review flows for hosts and travelers

## Tech Stack

- Python
- Flask
- Flask-SocketIO
- PyMySQL
- Jinja2 templates
- MySQL
- Alembic
- Pytest
- Optional Redis integration for chat rate limiting

## Project Structure

```text
Travelbuddyfinder/
├── app.py
├── chat_worker.py
├── templates/
├── static/
├── tests/
├── migrations/
├── alembic.ini
└── README.md
```

## Getting Started

### 1. Create a virtual environment

```bash
python3 -m venv .venv
source .venv/bin/activate
```

### 2. Install dependencies

This repo does not currently include a `requirements.txt`, so install the core packages manually:

```bash
pip install flask flask-socketio pymysql redis alembic sqlalchemy pytest
```

### 3. Create the database

Start MySQL locally and create the database:

```sql
CREATE DATABASE travelbuddyfinder;
```

### 4. Configure database access

Current app runtime settings are defined near the top of [`app.py`](app.py). Before running locally, update these values to match your MySQL setup:

- `DB_HOST`
- `DB_USER`
- `DB_PASSWORD`
- `DB_NAME`

Alembic migrations use environment variables instead:

```bash
export DB_HOST=localhost
export DB_USER=root
export DB_PASSWORD=your_password
export DB_NAME=travelbuddyfinder
```

### 5. Optional environment variables

Useful runtime configuration:

```bash
export SECRET_KEY=replace-this-in-dev
export FLASK_ENV=development
export SOCKETIO_ASYNC_MODE=threading
export EMAIL_BACKEND=console
export SMS_BACKEND=console
export NOTIFICATION_EMAIL_ENABLED=1
export NOTIFICATION_SMS_ENABLED=1
export AUTO_EMAIL_FOR_ALL_NOTIFICATIONS=0
export AUTO_SMS_FOR_ALL_NOTIFICATIONS=0
export REDIS_URL=
```

### 6. Run the app

```bash
python app.py
```

The development server starts through Socket.IO. By default, it runs in debug mode.

### 7. Run the background worker

The worker processes queued notification jobs and scheduled chat messages:

```bash
python chat_worker.py
```

### 8. Open the app

Visit:

```text
http://127.0.0.1:5000
```

## Database and Migrations

- The app still performs some runtime schema checks and table updates through internal `ensure_*` helpers.
- Alembic is included for versioned migrations under [`migrations/`](migrations/).
- Existing migration docs are in [`migrations/README.md`](migrations/README.md).

Common Alembic commands:

```bash
alembic upgrade head
alembic current
alembic revision -m "describe change"
```

## Notifications

The project supports three layers of updates:

- In-app notifications stored in the database
- Development email delivery through `EMAIL_BACKEND=console` or SMTP later
- Development SMS logging through `SMS_BACKEND=console`

For local development, console backends are the easiest setup because they do not require paid providers.

## Testing

Run the test suite with:

```bash
pytest tests/
```

Current tests cover areas such as:

- Chat socket flow guards and attachment handling
- Trip completion and review lifecycle rules
- Host/traveler review permissions

## Main App Areas

- [`app.py`](app.py): Flask routes, Socket.IO events, schema helpers, notifications, admin flows
- [`chat_worker.py`](chat_worker.py): background job runner
- [`templates/mainpage.html`](templates/mainpage.html): main trip dashboard
- [`templates/host_dashboard.html`](templates/host_dashboard.html): host dashboard
- [`templates/create_post.html`](templates/create_post.html): trip creation UI
- [`templates/messages_page.html`](templates/messages_page.html): messages center

## Before Pushing to GitHub

- Move database credentials out of `app.py` and into environment variables
- Remove any real passwords, SMTP credentials, or API keys
- Add a `.gitignore` for `.venv`, `.idea`, `__pycache__`, `.pytest_cache`, `.DS_Store`, and `.env`
- Review uploads and local test data before committing
- Turn off `debug=True` for production

## Future Improvements

- Add a `requirements.txt` or `pyproject.toml`
- Move all runtime config to environment variables
- Add deployment instructions
- Add screenshots to the README
- Add a license if the repository will be public
