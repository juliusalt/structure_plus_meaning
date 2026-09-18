#!/bin/sh
# The base is a loaded, sealed session that never works. Every implementer is a session-level fork of it
# (`--resume <base> --fork-session`): they start with the base's whole context read from the prompt cache
# instead of re-reading and re-writing it, and are discarded when full. Sealing (stopping) the base keeps
# its prefix fixed, and the keep-warm daemon keeps its cache entry alive between forks.
#   base.sh impl build          freeze base-load.txt into a verified pack and start loading it in a background
#                               session, chunk by chunk through Bash (returns at once); BASE_PACK_DIR can name an
#                               already frozen pack. build-packed is the same command.
#   base.sh impl pack           prepare and verify a pack without launching a session
#   base.sh impl build-files    the older loader: the session reads every listed file with the Read tool
#   base.sh impl status         one line: load state, measured context against the expected size
#   base.sh impl seal           when the load has finished: verify its size, snapshot the held files, stop it, record it
#   base.sh impl extend <file>  have a file-loaded base read one more file (the prefix grows, the cache stays valid);
#                               seal again after. A packed base is rebuilt instead.
#   base.sh impl warm           hit the base's cache entry with a throwaway fork, verify the hit, delete the fork
#                                    (each ping's text is unique, so the longest cached prefix it can match is the base itself)
#   base.sh impl drop           forget the base; live sessions then start plain
set -u
HERE=$(cd "$(dirname "$0")" && pwd); PROJECT=$(cd "$HERE/../.." && pwd); STATE="${ORCH_STATE_DIR:-$HERE/state}"
cd "$PROJECT" || exit 1; mkdir -p "$STATE"
who=${1:-}; cmd=${2:-}
case "$who" in
  impl) name=${BASE_NAME:-impl-base}; model=${BASE_MODEL:-${IMPL_MODEL:-claude-opus-5[1m]}}; effort=${BASE_EFFORT:-${IMPL_EFFORT:-max}}; role="$HERE/implementer-prompt.md" ;;
  *) echo "usage: base.sh impl pack|build|build-files|status|seal|extend <file>|warm|drop" >&2; exit 2 ;;
esac
# The base and every session forked from it start with exactly these tools and no connectors or skills list:
# the prefix must be identical for a fork to read the base from cache. The same file is read by rotate.sh.
LEAN=$(cat "$HERE/session-flags")
rec="$STATE/$who-base.json"; building="$STATE/$who-base-building.json"; SESSIONS="$HOME/.claude/projects/$(echo "$PROJECT" | tr '/_' '--')"
field() { python3 -c "import json,sys; print(json.load(open(sys.argv[1])).get(sys.argv[2],''))" "$1" "$2" 2>/dev/null; }
expected() {
  frozen=$(field "$building" pack); [ -n "$frozen" ] || frozen=$(field "$rec" pack)
  if [ -n "$frozen" ]; then
    python3 -c 'import json,sys; d=json.load(open(sys.argv[1])); print(d.get("selected_loaded_token_estimate", d["variants"][-1]["loaded_token_estimate"]) // 1000)' "$frozen/pack.json"
  else
    "$HERE/manifest.py" size "$who" | sed -n 's/.*about \([0-9]*\)K tokens.*/\1/p'
  fi
}
daemon() { "$HERE/warm_daemon.sh" --ensure; }
prepare_pack() {
  packed=${BASE_PACK_DIR:-$STATE/base-pack-$(date +%Y%m%dT%H%M%S)-$$}
  case "$packed" in /*) ;; *) packed="$PROJECT/$packed" ;; esac
  if [ -e "$packed/pack.json" ]; then
    python3 "$HERE/base_pack.py" verify "$packed" || return $?
  else
    python3 "$HERE/base_pack.py" build --output "$packed" || return $?
  fi
  echo "packed base: $packed"
}

case "$cmd" in
  pack) prepare_pack ;;
  build|build-packed|build-files)
    [ -e "$rec" ] && { echo "refused: a $who base is recorded; run base.sh $who drop first"; exit 3; }
    [ -n "$("$HERE/session_row.py" "$name")" ] && { echo "refused: a session named $name is already live"; exit 3; }
    packed=""
    if [ "$cmd" != build-files ]; then
      prepare_pack || exit $?
      bootstrap=$(python3 "$HERE/base_pack.py" bootstrap "$packed") || exit $?
    else
      bootstrap=$(sed "s/{WHO}/$who/g" "${BASE_BOOTSTRAP_FILE:-$HERE/base-bootstrap.txt}")
    fi
    claude --bg $LEAN --model "$model" --effort "$effort" --permission-mode auto --autocompact "${BASE_AUTOCOMPACT:-1M}" \
      --settings "$HERE/base-settings.json" --append-system-prompt-file "${BASE_PROMPT_FILE:-$role}" \
      -n "$name" "$bootstrap" >/dev/null 2>&1
    sleep 2; set -- $("$HERE/session_row.py" "$name")
    [ -n "${4:-}" ] || { echo "start of $name not confirmed"; exit 4; }
    python3 - "$building" "$4" "$model" "$effort" "$name" "$packed" <<'PY'
import json, sys
path, sid, model, effort, name, packed = sys.argv[1:]
record = dict(sessionId=sid, model=model, effort=effort, name=name)
if packed:
    record["pack"] = packed
json.dump(record, open(path, "w"))
PY
    echo "loading $name id=$2: estimated $(expected)K loaded; check with base.sh $who status, then base.sh $who seal" ;;
  status)
    f="$rec"; [ -e "$f" ] || f="$building"; [ -e "$f" ] || { echo "no $who base"; exit 1; }
    recorded_name=$(field "$f" name); [ -z "$recorded_name" ] || name="$recorded_name"
    set -- $("$HERE/session_row.py" "$name")
    echo "$(basename "$f" .json): ${3:-sealed}, context $("$HERE/ctx_gauge.py" measure "$SESSIONS/$(field "$f" sessionId).jsonl") tokens; estimated about $(expected)K loaded in total" ;;
  seal)
    [ -e "$building" ] || { echo "nothing is loading"; exit 1; }
    recorded_name=$(field "$building" name); [ -z "$recorded_name" ] || name="$recorded_name"
    sid=$(field "$building" sessionId); set -- $("$HERE/session_row.py" "$name")
    case "${3:-}" in done|idle) ;; "") echo "refused: $name is not live"; exit 3 ;; *) echo "refused: $name is still ${3}"; exit 3 ;; esac
    ctx=$("$HERE/ctx_gauge.py" measure "$SESSIONS/$sid.jsonl")
    packed=$(field "$building" pack)
    if [ -n "$packed" ]; then
      python3 "$HERE/base_pack.py" check-load "$packed" "$SESSIONS/$sid.jsonl" || exit 3
      # The manifest must describe the frozen sources the model received, even
      # if the working files changed while it was loading.
      python3 "$HERE/base_pack.py" snapshot "$packed" "$STATE/$who-manifest.json" || exit 3
    else
      want=$(( $(expected) * 850 ))
      [ "$ctx" -ge "$want" ] || { echo "refused: context $ctx is below 85% of the expected load ($want tokens): the load is incomplete; look with claude attach $2"; exit 3; }
      "$HERE/manifest.py" snapshot "$who" >/dev/null
    fi
    claude stop "$2" >/dev/null 2>&1
    python3 - "$building" "$rec" "$ctx" <<'PY'
import json, sys, time
d = json.load(open(sys.argv[1])); d.update(context=int(sys.argv[3]), sealed=time.strftime("%Y-%m-%dT%H:%M:%S"))
json.dump(d, open(sys.argv[2], "w"))
PY
    rm -f "$building"; touch "$STATE/$who-base.hit" "$STATE/$who-base.used"; daemon
    target=${ORCH_BASE_TARGET:-530000}  # manifest.TARGET
    [ "$ctx" -gt $(( target * 103 / 100 )) ] && echo "note: measured $ctx is over the $target target; trim base-load.txt (select_base_load.py with a lower ORCH_BASE_TARGET) before the next build"
    echo "sealed $who base $sid at $ctx tokens (target $target); its forks have about $(( (${ORCH_WINDOW:-1000000} - ctx) / 1000 ))K of room; keep-warm daemon running" ;;
  extend)
    file=${3:?usage: base.sh $who extend <file>}; [ -e "$rec" ] || { echo "no sealed $who base"; exit 1; }
    [ -z "$(field "$rec" pack)" ] || { echo "refused: a packed base has a frozen, verified load; add the file to the load list and build a new pack"; exit 3; }
    [ -f "$file" ] || { echo "no such file: $file"; exit 1; }
    # no flags: a sealed background session resumed with flags starts a copy; resumed bare, it continues itself
    claude --bg --resume "$(field "$rec" sessionId)" \
      "You are being loaded as the base again: read $file in full with the Read tool (all of its parts together if it is large), then reply LOADED and end your turn. Do nothing else." >/dev/null 2>&1
    sleep 3
    mv "$rec" "$building"; echo "extending the $who base with $file; check with base.sh $who status, then base.sh $who seal" ;;
  warm)
    [ -e "$rec" ] || { echo "no sealed $who base"; exit 1; }
    sid=$(field "$rec" sessionId); n="warm-$who"
    claude --bg --resume "$sid" --fork-session $LEAN --model "$(field "$rec" model)" --effort "$(field "$rec" effort)" \
      --permission-mode auto --settings "$HERE/base-settings.json" -n "$n" \
      "Keep-warm ping $(date +%s). Use no tools. Reply with the single word WARM and end your turn." >/dev/null 2>&1
    i=0; while [ $i -lt 90 ]; do set -- $("$HERE/session_row.py" "$n"); case "${3:-}" in done|idle) break ;; esac; i=$((i + 1)); sleep 2; done
    result=$("$HERE/session_fork_check.py" "${4:-none}" "$sid" 2>&1)
    [ -n "${2:-}" ] && { claude stop "$2"; claude rm "$2"; } >/dev/null 2>&1
    [ -n "${4:-}" ] && rm -rf "$SESSIONS/$4" "$SESSIONS/$4.jsonl"
    # a MISS still rewrote the entry, so the base is warm either way; a ping nobody answered (usage limit) is neither
    case "$result" in OK*) touch "$STATE/$who-base.hit"; rm -f "$STATE/$who-base.miss" ;; MISS*) touch "$STATE/$who-base.hit"; echo x >> "$STATE/$who-base.miss" ;; esac
    echo "$(date +%Y-%m-%dT%H:%M:%S) warm $who: $result" ;;
  drop) rm -f "$rec" "$building" "$STATE/$who-manifest.json" "$STATE/$who-base.hit" "$STATE/$who-base.used" "$STATE/$who-base.miss"; echo "$who base forgotten; live sessions start plain" ;;
  *) echo "usage: base.sh impl pack|build|build-files|status|seal|extend <file>|warm|drop" >&2; exit 2 ;;
esac
