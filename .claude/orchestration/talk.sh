#!/bin/sh
# Speak to the planner: open a planning episode for the owner (a fork of the knowledge base, given the events gathered
# so far) and attach to it; if an episode is running, attach to that one. The episode records the owner's directions
# in the ledger, acts on them, and ends when the owner is done; its notes go to the knowledge base.
set -u
HERE=$(cd "$(dirname "$0")" && pwd)
i=0
until name=$("$HERE/v2.py" talk) && [ -n "$name" ]; do  # the knowledge base may be integrating the last notes
  i=$((i + 1)); [ "$i" -gt 90 ] && { echo "no episode could start: the knowledge base is not ready (see health.py)"; exit 1; }
  [ "$i" = 1 ] && echo "waiting for the knowledge base (it integrates the last episode's notes, or loads)"
  sleep 2
done
echo "speaking with $name"
exec "$HERE/attach.sh" planner
