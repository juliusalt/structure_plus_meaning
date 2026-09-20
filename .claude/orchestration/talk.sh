#!/bin/sh
# Speak to the planner: join the one that lives (woken if it was between its events) and attach to it, or open one
# (a fork of the knowledge base) if none does. It records the owner's directions in the ledger, acts on them, and goes
# back to its events when the owner has gone; it ends, and its notes reach the knowledge base, only when its window is
# full.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
i=0
until name=$("$HERE/v2.py" talk) && [ -n "$name" ]; do  # the knowledge base may be integrating the last notes
  i=$((i + 1)); [ "$i" -gt 90 ] && { echo "no planner could start: the knowledge base is not ready (see health.py)"; exit 1; }
  [ "$i" = 1 ] && echo "waiting for the knowledge base (it integrates the last planner's notes, or loads)"
  sleep 2
done
echo "speaking with $name"
exec "$HERE/attach.sh" planner
