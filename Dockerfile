FROM python:3.12-slim

WORKDIR /app

ENV PYTHONDONTWRITEBYTECODE=1 \
    PYTHONUNBUFFERED=1 \
    PORT=8000

COPY requirements.txt .
RUN pip install --no-cache-dir -r requirements.txt

# templates/, static/ (inkl. i18n), flask_app.py, database.db falls vorhanden
COPY . .

EXPOSE 8000

# SocketIO nutzt async_mode=threading — python ist hier zuverlässiger
# als gunicorn --worker-class eventlet -w 1.
CMD ["python", "flask_app.py"]
