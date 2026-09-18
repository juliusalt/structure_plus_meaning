#!/bin/sh
# Open the live implementer in this terminal and follow it: when the attached implementer is stopped by a
# rotation or a wake (or ends otherwise), wait for the implementer then named in state/current-impl and attach
# to it. Leaving the session view on purpose while the implementer still runs ends this, and so does stop.sh.
# start.sh ends by running this; run it alone to reopen the process without starting anything.
set -u
HERE=$(cd "$(dirname "$0")" && pwd); STATE="${ORCH_STATE_DIR:-$HERE/state}"
stopped() { [ -e "$STATE/stopped" ] && { echo "the orchestration is stopped; start.sh starts it again"; exit 0; }; }
live() {  # sets cur and id to the live implementer named in state/current-impl
  cur=$(cat "$STATE/current-impl" 2>/dev/null); id=""
  set -- $([ -n "$cur" ] && "$HERE/session_row.py" "$cur")
  [ "${1:-}" = background ] && [ -n "${2:-}" ] && id=$2
  [ -n "$id" ]
}
marked_since() { [ -e "$STATE/$1" ] && [ "$(stat -c %Y "$STATE/$1")" -ge "$since" ]; }
wait_live() {
  i=0
  until live; do
    stopped
    i=$((i + 1)); [ "$i" -gt 300 ] && { echo "no live implementer after 10 minutes; see health.py"; exit 1; }
    sleep 2
  done
}
stopped
wait_live
while :; do
  since=$(date +%s); name=$cur
  claude attach "$id"
  stopped
  # the watchdog writes its mark before it stops a session: a rotation `rotated`, a wake `<name>.woken`
  if ! marked_since rotated && ! marked_since "$name.woken" && live && [ "$cur" = "$name" ]; then
    echo "left $name, which keeps running; attach.sh opens it again"
    exit 0
  fi
  echo "$name has ended; waiting for the live implementer"
  wait_live
  echo "attaching to $cur"
done
