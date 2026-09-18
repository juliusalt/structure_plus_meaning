#!/bin/sh
# The implementer's two declarations to the turn control (see ctx_gauge.py):
#   impl_state.sh waiting   blocked on a kb or owner answer, no other work: the next stop is allowed
#   impl_state.sh ready     HANDOFF.md is current: rotation may happen now
HERE=$(cd "$(dirname "$0")" && pwd); STATE="${ORCH_STATE_DIR:-$HERE/state}"; mkdir -p "$STATE"
case "${1:-}" in
  waiting) date +"declared %Y-%m-%dT%H:%M:%S" > "$STATE/waiting"; echo "waiting declared" ;;
  ready)   [ -e "$STATE/rotate" ] || date +"declared-ready %Y-%m-%dT%H:%M:%S" > "$STATE/rotate"; echo "rotation requested" ;;
  *) echo "usage: impl_state.sh waiting|ready" >&2; exit 2 ;;
esac
