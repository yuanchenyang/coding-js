#!/usr/bin/env bash
PORT=${1:-8000}

function schedule_web {
  sleep 0.1
  python -m webbrowser -t "http://localhost:$PORT/tests/test.html"
}
schedule_web &
python -m SimpleHTTPServer $PORT