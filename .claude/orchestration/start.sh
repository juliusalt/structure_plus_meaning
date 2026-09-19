#!/bin/sh
# Start the orchestration, or rejoin it: make it active (v2.py start: the knowledge base is built if there is none,
# and the dispatch runs), make sure the daemon runs (watchdog, dispatch, keep-warm), and follow the planning episodes
# in this terminal (attach.sh planner). `start.sh --no-attach` only starts.
set -u
[ "${1:-}" = "--no-attach" ] && START_NO_ATTACH=1
HERE=$(cd "$(dirname "$0")" && pwd); PROJECT=${ORCH_PROJECT:-$(cd "$HERE/../.." && pwd)}; STATE="${ORCH_STATE_DIR:-$HERE/state}"
cd "$PROJECT" || exit 1; mkdir -p "$STATE"
[ -e "$STATE/impl-base.json" ] || { echo "refused: no sealed base (base.sh impl build, status, seal): every session is a fork of it"; exit 3; }
rm -f "$STATE/stopped"
"$HERE/v2.py" start
"$HERE/warm_daemon.sh" --ensure
if [ -z "${START_NO_ATTACH:-}" ] && [ -t 1 ]; then exec "$HERE/attach.sh" planner; fi
