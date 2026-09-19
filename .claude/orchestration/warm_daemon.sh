#!/bin/sh
# The orchestration daemon: once a minute it runs watchdog.py (the sessions, what is held warm for consultation, then
# the dispatch), and it keeps the sealed bases' prompt-cache entries alive: impl (the planner's base, which the
# knowledge base forks) and, once the base topic has built them, mid (the middle base of task designers, investigators
# and reviewers) and impl2 (the implementation base of implementers and fixers). A cache entry lives one TTL past its
# last hit, and a working fork's requests count as hits on its base (measured 2026-09-18), so the gauge hook refreshes
# <who>-base.hit on every tool call of a live fork. This daemon pings a base only when that mark, or a seal, fork start
# or earlier ping, is older than ORCH_WARM_EVERY seconds: that is, while nothing forked from the base is active. A base
# nobody has used for ORCH_WARM_IDLE_MAX seconds is left to go cold (one cold write then costs less than the pings);
# two misses in a row also stop the pings for that base, since they would only pay for cold writes. It runs while the
# orchestration is active (state/v2.json) or a base is sealed.
#   warm_daemon.sh --ensure   start it, fully detached, unless it is already running (returns at once)
HERE=$(cd "$(dirname "$0")" && pwd); STATE="${ORCH_STATE_DIR:-$HERE/state}"; mkdir -p "$STATE"
if [ "${1:-}" = "--ensure" ]; then
  p=$(cat "$STATE/warm.pid" 2>/dev/null)
  if [ -n "$p" ] && kill -0 "$p" 2>/dev/null; then exit 0; fi
  # a simple background command with every stream redirected: nothing of the caller's stays open
  setsid nohup "$HERE/warm_daemon.sh" >/dev/null 2>&1 </dev/null &
  exit 0
fi
echo $$ > "$STATE/warm.pid"
every=${ORCH_WARM_EVERY:-3000}; idle_max=${ORCH_WARM_IDLE_MAX:-43200}
age() { [ -e "$1" ] && echo $(( $(date +%s) - $(stat -c %Y "$1") )) || echo 999999999; }
active() { python3 -c 'import json, sys; sys.exit(0 if json.load(open(sys.argv[1])).get("active") else 1)' "$STATE/v2.json" 2>/dev/null; }
while :; do
  "$HERE/watchdog.py" >/dev/null 2>&1
  any=0
  for who in impl mid impl2; do
    [ -e "$STATE/$who-base.json" ] || continue
    any=1
    [ "$(age "$STATE/$who-base.used")" -gt "$idle_max" ] && continue
    [ "$(wc -l < "$STATE/$who-base.miss" 2>/dev/null || echo 0)" -ge 2 ] && continue
    [ "$(age "$STATE/$who-base.hit")" -ge "$every" ] && "$HERE/base.sh" "$who" warm >> "$STATE/warm.log" 2>&1
  done
  [ "$any" = 0 ] && ! active && break
  sleep "${ORCH_DAEMON_EVERY:-60}"
done
rm -f "$STATE/warm.pid"
