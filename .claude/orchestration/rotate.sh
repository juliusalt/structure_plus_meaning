#!/bin/sh
# Replace the implementer: stop the old one, clear the turn-control state, start the next in the background.
#   rotate.sh auto                    old = state/current-impl (if it is still live), new = the next number
#   rotate.sh <old-name|none> <new>   explicit names
# When `base.sh impl` has sealed a base, the new implementer is a session-level fork of it and starts with the
# base's whole context read from the prompt cache; otherwise it starts plain. Exactly one implementer may
# exist: the repository's workflow forbids concurrent development agents, so nothing starts unless the old
# one is gone. Run by the watchdog when rotation is due, and by start.sh. Output: a few short lines.
set -u
HERE=$(cd "$(dirname "$0")" && pwd); PROJECT=$(cd "$HERE/../.." && pwd); STATE="${ORCH_STATE_DIR:-$HERE/state}"
cd "$PROJECT" || exit 1; mkdir -p "$STATE"
if [ "${1:-}" = auto ]; then
  old=$(cat "$STATE/current-impl" 2>/dev/null); n=$(echo "${old:-impl-0}" | sed 's/.*-//'); new="impl-$(( ${n:-0} + 1 ))"; old=${old:-none}
else
  old=${1:?usage: rotate.sh auto | rotate.sh <old-name|none> <new-name>}; new=${2:?usage: rotate.sh auto | rotate.sh <old-name|none> <new-name>}
fi

if [ -n "$("$HERE/session_row.py" "$new")" ]; then echo "refused: a session named $new is already live"; exit 3; fi
if [ "$old" != none ]; then
  set -- $("$HERE/session_row.py" "$old")
  case "${1:-}" in
    background) claude stop "$2" >/dev/null 2>&1
                sleep 2
                set -- $("$HERE/session_row.py" "$old")
                if [ -n "${1:-}" ]; then echo "refused: $old is still listed after stop"; exit 3; fi
                echo "stopped $old" ;;
    interactive) echo "refused: $old is an interactive session (pid $2); its owner ends it in its terminal, then rerun"; exit 3 ;;
    unknown) echo "refused: the session listing failed"; exit 3 ;;
    *) echo "$old is not running" ;;
  esac
fi
rm -f "$STATE/rotate" "$STATE/soft" "$STATE/waiting" "$STATE/waiting-declared"
# the owner's directions given since the curated ones: the new implementer reads them before anything else
if ! "$HERE/extract_owner_directions.py" --new >/dev/null 2>"$STATE/owner-directions-new.err"; then
  printf '# Owner directions given since the curated ones\n\nThey could not be collected for this start. Read the owner ledger, and ask the owner whether anything was said since.\n' > "$STATE/owner-directions-new.md"
  echo "note: owner directions since the curated ones could not be collected (see $STATE/owner-directions-new.err)"
fi
builds=$(pgrep -c -x poly 2>/dev/null || true)
[ "${builds:-0}" -gt 0 ] && echo "note: $builds poly processes are still running from earlier work"

if [ -e "$STATE/impl-base.json" ]; then
  # a fork of the sealed base: same model and effort as the base, or its cached prefix is not reused
  field() { python3 -c "import json,sys; print(json.load(open(sys.argv[1]))[sys.argv[2]])" "$STATE/impl-base.json" "$1"; }
  stale=$("$HERE/manifest.py" changed impl 2>/dev/null); echo "$stale"
  touch "$STATE/impl-base.hit" "$STATE/impl-base.used"
  prompt=$(sed -e "s/{NAME}/$new/g" -e "s|{STALE}|Held files that are ${stale:-unknown}|" "${IMPL_BOOTSTRAP_FILE:-$HERE/implementer-bootstrap-fork.txt}")
  out=$(claude --bg --resume "$(field sessionId)" --fork-session $(cat "$HERE/session-flags") --model "$(field model)" --effort "$(field effort)" \
    --permission-mode auto --autocompact "${IMPL_AUTOCOMPACT:-1M}" \
    --settings "${IMPL_SETTINGS:-$HERE/impl-settings.json}" -n "$new" "$prompt" 2>&1)
  mode="forked from base $(field sessionId | cut -c1-8) at $(field context) tokens"; echo fork-unverified > "$STATE/impl-mode"; base_sid=$(field sessionId)
else
  prompt=$(sed "s/{NAME}/$new/g" "${IMPL_BOOTSTRAP_FILE:-$HERE/implementer-bootstrap.txt}")
  out=$(claude --bg $(cat "$HERE/session-flags") --model "${IMPL_MODEL:-claude-opus-5[1m]}" --effort "${IMPL_EFFORT:-max}" \
    --permission-mode auto --autocompact "${IMPL_AUTOCOMPACT:-1M}" \
    --settings "${IMPL_SETTINGS:-$HERE/impl-settings.json}" \
    --append-system-prompt-file "${IMPL_PROMPT_FILE:-$HERE/implementer-prompt.md}" \
    -n "$new" "$prompt" 2>&1)
  mode="plain"; echo plain > "$STATE/impl-mode"
fi
sleep 2
set -- $("$HERE/session_row.py" "$new")
if [ -n "${2:-}" ]; then
  echo "$new" > "$STATE/current-impl"; echo "started $new id=$2 (${3:-?}, $mode); attach: claude attach $2"
  if [ -n "${base_sid:-}" ]; then  # did its first request read the base from cache? Only then does its work keep the base warm.
    i=0; verdict=""
    while [ $i -lt 25 ]; do verdict=$("$HERE/session_fork_check.py" "$4" "$base_sid" 2>/dev/null); case "$verdict" in OK*|MISS*) break ;; esac; i=$((i + 1)); sleep 3; done
    case "$verdict" in
      OK*) echo fork > "$STATE/impl-mode"; echo "cache: $(echo "$verdict" | sed 's/.*first own request \(.*\) (.*/\1/')" ;;
      MISS*) echo fork-cold > "$STATE/impl-mode"; echo "cache: MISS — $(echo "$verdict" | sed 's/.*first own request \(.*\) (.*/\1/'); this fork paid a cold write and does not keep the base warm" ;;
      *) echo "cache: first request not seen yet; run session_fork_check.py $4 $base_sid later" ;;
    esac
  fi
else echo "start of $new not confirmed: $(printf '%s' "$out" | head -3 | tr '\n' ' ' | cut -c1-300)"; exit 4; fi
