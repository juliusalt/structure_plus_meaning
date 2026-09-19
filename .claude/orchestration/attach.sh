#!/bin/sh
# Open a role's live session in this terminal and follow the role: `attach.sh` (or `attach.sh planner`) the planning
# episodes, `attach.sh producer` the producing session, `support` the task designer or reviewer, `fix` a quick fix,
# `consultant` a consultation, `kb` the knowledge base while it loads or integrates. When the attached session is
# stopped (its piece of work ended, a wake) or ends otherwise, wait for the session then holding the role and attach
# to it. Leaving the session view on purpose while the session still holds the role ends this, and so does stop.sh.
# start.sh ends by running this for the planner; talk.sh opens an episode for the owner and runs it.
set -u
HERE=$(cd "$(dirname "$0")" && pwd); STATE="${ORCH_STATE_DIR:-$HERE/state}"
role=${1:-planner}
case "$role" in planner|producer|support|fix|consultant|kb) ;; *) echo "usage: attach.sh [planner|producer|support|fix|consultant|kb]" >&2; exit 2 ;; esac
stopped() { [ -e "$STATE/stopped" ] && { echo "the orchestration is stopped; start.sh starts it again"; exit 0; }; }
live() {  # sets cur and id to the live session holding the role
  cur=$("$HERE/v2.py" who "$role"); id=""
  set -- $([ -n "$cur" ] && "$HERE/session_row.py" "$cur")
  [ "${1:-}" = background ] && [ -n "${2:-}" ] && id=$2
  [ -n "$id" ]
}
marked_since() { [ -e "$STATE/$1" ] && [ "$(stat -c %Y "$STATE/$1")" -ge "$since" ]; }
wait_live() {
  i=0
  until live; do
    stopped
    i=$((i + 1)); [ "$i" -gt 300 ] && { echo "no live $role after 10 minutes; see health.py"; exit 1; }
    sleep 2
  done
}
stopped
wait_live
while :; do
  since=$(date +%s); name=$cur
  claude attach "$id"
  stopped
  # a wake (v2.wake) writes `<name>.woken` before it stops the session; a successor holds the role under a new name
  if ! marked_since "$name.woken" && live && [ "$cur" = "$name" ]; then
    echo "left $name, which keeps running; attach.sh $role opens it again"
    exit 0
  fi
  echo "$name has ended; waiting for the live $role"
  wait_live
  echo "attaching to $cur"
done
