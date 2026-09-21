#!/bin/sh
# Start the orchestration, or rejoin it: make it active (v2.py start: the knowledge base is built if there is none,
# and the dispatch runs), make sure the daemon runs (watchdog, dispatch, keep-warm), and follow the planner in this
# terminal (attach.sh planner). `start.sh --no-attach` only starts.
#   start.sh --fresh   begin the run on a knowledge base built anew: the one that stands is left behind, the next
#                      loads HANDOFF.md, the ledger and the owner's words and nothing a planner accumulated, and the
#                      first planner is charged with taking stock of what has been produced, dropping what the graph
#                      no longer needs and re-planning the rest before it queues anything.
set -u
FRESH=
for a in "$@"; do
  case "$a" in
    --no-attach) START_NO_ATTACH=1 ;;
    --fresh) FRESH=--fresh ;;
    *) echo "usage: start.sh [--fresh] [--no-attach]" >&2; exit 2 ;;
  esac
done
HERE=$(cd "$(dirname "$0")" && pwd); PROJECT=${ORCH_PROJECT:-$(cd "$HERE/../.." && pwd)}; STATE="${ORCH_STATE_DIR:-$HERE/state}"
cd "$PROJECT" || exit 1; mkdir -p "$STATE"
"$HERE/v2.py" control || exit 3  # the supervisor it starts must run outside Claude Code's sandbox
[ -e "$STATE/max-base.json" ] || { echo "refused: no sealed base (base.sh max build, status, seal): every session is a fork of it"; exit 3; }
rm -f "$STATE/stopped"
"$HERE/v2.py" start $FRESH
"$HERE/warm_daemon.sh" --ensure
if [ -z "${START_NO_ATTACH:-}" ] && [ -t 1 ]; then exec "$HERE/attach.sh" planner; fi
