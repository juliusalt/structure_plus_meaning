#!/bin/sh
# Screenshots of every view of the run's console, for Claude to look at (it cannot start a browser inside its sandbox:
# the browsers' local sockets are refused there). Run it from your own shell — in Claude Code as
#   ! sh .claude/orchestration/notes/console-screenshots.sh
# It starts a console of its own on port 8798 (views only are opened; nothing is clicked), takes each view at the
# width of a desktop and tall enough to show it whole, stops that console, and leaves the PNGs in /tmp/claude-1000/shots.
set -u
OUT=/tmp/claude-1000/shots
PROJECT=$(cd "$(dirname "$0")/../../.." && pwd)
mkdir -p "$OUT"
rm -f /tmp/claude-1000/shots/*.png  # the last round's, so none is read by mistake
cd "$PROJECT" || exit 1
ORCH_DASHBOARD_TOKEN=shot python3 -B .claude/orchestration/dashboard.py --port 8798 >/dev/null 2>&1 &
CONSOLE=$!
sleep 2
PROFILE=$(mktemp -d)
shot() {  # view, file, height
  google-chrome-stable --headless=new --disable-gpu --hide-scrollbars --user-data-dir="$PROFILE" --no-first-run \
    --window-size=1440,"$3" --virtual-time-budget=9000 --screenshot="$OUT/$2.png" \
    "http://127.0.0.1:8798/?token=shot#$1" >/dev/null 2>&1
}
for v in now graph machine bases trains sessions tasks costs log control; do
  shot "$v" "$v" 1000
  shot "$v" "$v-full" 3200
done
# one session and one task opened whole: of the twelve newest implementers' and fixers' sessions the one with the longest
# transcript (the most to read), and the task landed last (its whole history, its result and review) or, with none,
# the highest-numbered task
S=$(python3 -c '
import json, os, sys
sys.path.insert(0, ".claude/orchestration")
import v2
s = json.load(open(".claude/orchestration/state/v2.json"))["sessions"]
newest = sorted((x for x in s.values() if x.get("role") in ("fixer", "implementer")), key=lambda x: x.get("started") or 0)[-12:]
def size(x):
    for d in v2.transcript_dirs():
        p = os.path.join(d, (x.get("sid") or "-") + ".jsonl")
        if os.path.exists(p):
            return os.path.getsize(p)
    return 0
print(max(newest, key=size)["name"])' 2>/dev/null)
T=$(python3 -c '
import json
try:
    q = json.load(open(".claude/orchestration/state/landing-queue.json"))
    print(max((t for t, e in q.items() if e.get("what") == "landed"), key=lambda t: q[t].get("decided") or 0))
except Exception:
    t = json.load(open(".claude/orchestration/state/v2.json"))["tasks"]
    print(max(t, key=lambda x: int(x) if x.isdigit() else 0))' 2>/dev/null)
[ -n "$S" ] && shot "sessions/$S" "session" 3200
[ -n "$T" ] && shot "tasks/$T" "task" 2400
# the long tables in a narrower window, where columns go out of view and the table's own scrollbar must show
for v in tasks sessions; do
  google-chrome-stable --headless=new --disable-gpu --user-data-dir="$PROFILE" --no-first-run \
    --window-size=1100,900 --virtual-time-budget=9000 --screenshot="$OUT/$v-1100.png" \
    "http://127.0.0.1:8798/?token=shot#$v" >/dev/null 2>&1
done
# and the page at a phone's width
google-chrome-stable --headless=new --disable-gpu --hide-scrollbars --user-data-dir="$PROFILE" --no-first-run \
  --window-size=390,1600 --virtual-time-budget=9000 --screenshot="$OUT/now-phone.png" \
  "http://127.0.0.1:8798/?token=shot#now" >/dev/null 2>&1
kill "$CONSOLE" 2>/dev/null
rm -rf "$PROFILE"
ls -la "$OUT"
