#!/bin/sh
# Start the process, or rejoin it: make sure the daemon runs (watchdog, rotation, keep-warm), start an
# implementer if none is live, and open the live implementer in this terminal, following it through rotations
# and wakes (attach.sh). `start.sh --no-attach` only starts.
set -u
[ "${1:-}" = "--no-attach" ] && START_NO_ATTACH=1
HERE=$(cd "$(dirname "$0")" && pwd); PROJECT=$(cd "$HERE/../.." && pwd); STATE="${ORCH_STATE_DIR:-$HERE/state}"
cd "$PROJECT" || exit 1; mkdir -p "$STATE"; rm -f "$STATE/stopped"
"$HERE/warm_daemon.sh" --ensure
cur=$(cat "$STATE/current-impl" 2>/dev/null); set -- $([ -n "$cur" ] && "$HERE/session_row.py" "$cur")
if [ -z "${2:-}" ]; then
  [ -e "$STATE/impl-base.json" ] || echo "note: no sealed base (base.sh impl build, status, seal): the implementer starts plain and reads for itself"
  "$HERE/rotate.sh" auto || exit $?
  cur=$(cat "$STATE/current-impl"); set -- $("$HERE/session_row.py" "$cur")
else
  echo "$cur is live (${3:-?}), id $2"
fi
if [ -z "${START_NO_ATTACH:-}" ] && [ -t 1 ] && [ -n "${2:-}" ]; then exec "$HERE/attach.sh"; fi
