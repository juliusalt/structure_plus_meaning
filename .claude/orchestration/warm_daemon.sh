#!/bin/sh
# The orchestration daemon: once a minute it runs watchdog.py (the sessions, what is held warm for consultation, then
# the dispatch), and it keeps the sealed bases' prompt-cache entries alive: max (the planner's base, which the
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
"$HERE/v2.py" control || exit 3  # started inside Claude Code's sandbox it could start and stop nothing
if [ "${1:-}" = "--ensure" ]; then
  p=$(cat "$STATE/warm.pid" 2>/dev/null)
  # the number alone can belong to whatever took that pid after a daemon died without clearing the file, and then
  # nothing ever starts one again while health.py reports it alive: the process must name the daemon too. A cmdline
  # that cannot be read counts as alive, so a second daemon is never started by mistake (2026-09-21).
  if [ -n "$p" ] && kill -0 "$p" 2>/dev/null \
     && { [ ! -r "/proc/$p/cmdline" ] || tr '\0' ' ' < "/proc/$p/cmdline" | grep -q warm_daemon; }; then exit 0; fi
  # a simple background command with every stream redirected: nothing of the caller's stays open
  setsid nohup "$HERE/warm_daemon.sh" >/dev/null 2>&1 </dev/null &
  exit 0
fi
echo $$ > "$STATE/warm.pid"
# A heartbeat for what cannot see this process: inside Claude Code's sandbox only a command's own processes are
# visible, and health.py run from a session read the live daemon as dead (2026-09-21). It ends with the daemon, and
# does not wait on a watchdog pass, which may take ten minutes.
( while kill -0 $$ 2>/dev/null; do touch "$STATE/warm.beat"; sleep "${ORCH_BEAT_EVERY:-5}"; done ) >/dev/null 2>&1 &
# 2400 against a cache entry's 3300 s: fifteen minutes of margin. At 3000 the margin was five, and the max and high
# bases both fell through it on 2026-09-20 while the orchestration was stopped — a miss costs a whole cold write
# (461K and 511K), and two misses in a row stop a base's pings for good.
every=${ORCH_WARM_EVERY:-2400}; idle_max=${ORCH_WARM_IDLE_MAX:-43200}
age() { [ -e "$1" ] && echo $(( $(date +%s) - $(stat -c %Y "$1") )) || echo 999999999; }
active() { python3 -c 'import json, sys; sys.exit(0 if json.load(open(sys.argv[1])).get("active") else 1)' "$STATE/v2.json" 2>/dev/null; }
while :; do
  # bounded: a watchdog that hangs (a claude or git call that never returns) would stop the dispatch and the pings
  # with the daemon still alive, and health.py would say "daemon: alive" while nothing happened
  timeout "${ORCH_WATCHDOG_MAX:-600}" "$HERE/watchdog.py" >/dev/null 2>&1 \
    || [ $? -ne 124 ] || echo "$(date +%Y-%m-%dT%H:%M:%S) ATTENTION the watchdog did not finish within ${ORCH_WATCHDOG_MAX:-600}s and was ended" >> "$STATE/v2.log"
  any=0
  for who in max xhigh high; do
    [ -e "$STATE/$who-base.json" ] || continue
    any=1
    # used: a session standing on the base started (v2.launch), or a build over it — through the knowledge base and the
    # roles' layers and churns as much as a fork of the base itself
    [ "$(age "$STATE/$who-base.used")" -gt "$idle_max" ] && continue
    [ "$( [ -e "$STATE/$who-base.miss" ] && wc -l < "$STATE/$who-base.miss" || echo 0)" -ge 1 ] && continue
    # base.sh writes the verdict to warm.log itself, so that a ping run by hand is recorded there too; only what
    # fails before it reaches that line is redirected
    # what the roles fork, while a role forks it: with every role of the base on its own churn nobody reads the
    # shared part, and its ping (about 60K) bought nothing — a role that falls back to it cold forks the medium layer
    [ "$(age "$STATE/$who-base.hit")" -ge "$every" ] && "$HERE/v2.py" base-forked "$who" \
      && "$HERE/base.sh" "$who" warm >/dev/null 2>> "$STATE/warm.log"
    # the stable base under a layer keeps an entry of its own, which a read of the layer does not refresh (the max
    # layer's refresh of 2026-09-21 wrote 339,381 tokens of it anew): pinged on its own while that entry is still warm,
    # and never once it is cold — a fork that misses writes its own prefix, not the base's, so a ping would buy a cold
    # write and bring nothing back; a rebuild of the base makes the entry again (base.sh seal)
    "$HERE/base.sh" "$who" warm stable --if-due >/dev/null 2>> "$STATE/warm.log"
    # under a delta (notes/plan-delta-layer.md) the layer's own entry is read only by the delta's builds: pinged the same
    # way while no build has read it within the interval
    "$HERE/base.sh" "$who" warm layer --if-due >/dev/null 2>> "$STATE/warm.log"
    # Each reusable intermediate prefix has its own cache entry; descendant reads do not keep it alive.
    for part in $(python3 -B "$HERE/base_stack.py" parts "$who" 2>/dev/null); do
      "$HERE/base.sh" "$who" warm "$part" --if-due >/dev/null 2>> "$STATE/warm.log"
    done
  done
  [ "$any" = 0 ] && ! active && break
  # A request from inside the sandbox (state/wanted/, v2.want: a session released, a dispatch, a final check) is
  # carried out within seconds rather than at the next minute. Only while the run is active and not stopped: then the
  # watchdog returns before the dispatch that takes requests, and they wait for the next start.
  left=${ORCH_DAEMON_EVERY:-60}
  while [ "$left" -gt 0 ]; do
    step=2; [ "$left" -lt 2 ] && step=$left
    sleep "$step"; left=$((left - step))
    ls "$STATE/wanted" 2>/dev/null | grep -q '\.json$' && [ ! -e "$STATE/stopped" ] && active && break
  done
done
rm -f "$STATE/warm.pid"
