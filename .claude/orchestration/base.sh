#!/bin/sh
# The base is a loaded, sealed session that never works. Every implementer is a session-level fork of it
# (`--resume <base> --fork-session`): they start with the base's whole context read from the prompt cache
# instead of re-reading and re-writing it, and are discarded when full. Sealing (stopping) the base keeps
# its prefix fixed, and the keep-warm daemon keeps its cache entry alive between forks.
# The three bases, named by their effort: max (the planner and the knowledge base, base-load-max.txt), xhigh
# (designer, task designer,
# investigator, reviewer, xhigh, base-load-xhigh.txt) and impl2 (implementer, fixer, high, base-load-high.txt); each
# carries library-prompt.md as its system prompt, which every fork inherits.
#   base.sh WHO build           freeze the base's load list into a verified pack and start loading it in a background
#                               session, chunk by chunk through Bash (returns at once); BASE_PACK_DIR can name an
#                               already frozen pack. build-packed is the same command.
#   base.sh WHO pack            prepare and verify a pack without launching a session
#   base.sh WHO build-files     the older loader: the session reads every listed file with the Read tool
#   base.sh WHO status          one line: load state, measured context against the expected size
#   base.sh WHO seal            when the load has finished: verify its size, snapshot the held files, stop it, record it
#   base.sh WHO extend <file>   have a file-loaded base read one more file (the prefix grows, the cache stays valid);
#                               seal again after. A packed base is rebuilt instead.
#   base.sh WHO warm            hit the base's cache entry with a throwaway fork, verify the hit, delete the fork
#                                    (each ping's text is unique, so the longest cached prefix it can match is the base itself)
#   base.sh WHO layer           refresh the frontier layer of a split list (a `# === layer ===` line): re-measure the
#                               frontier, pack what stands below the mark, fork the sealed stable base, load it,
#                               verify it, seal it and record it. Every role of that base then forks the layer, which
#                               reads the whole prefix under it from cache (measured 2026-09-20: 99% of 538K). It
#                               blocks until sealed; repeatable, and the layer it replaces is stopped.
#   base.sh WHO drop            forget the base and its layer; the roles that fork it start from the planner's base instead
# BASE_LOAD_LIST overrides the list this base is built from; nothing inherited from the caller does.
set -u
HERE=$(cd "$(dirname "$0")" && pwd); PROJECT=$(cd "$HERE/../.." && pwd); STATE="${ORCH_STATE_DIR:-$HERE/state}"
cd "$PROJECT" || exit 1; mkdir -p "$STATE"
who=${1:-}; cmd=${2:-}
case "$who" in
  max)   name=${BASE_NAME:-max-base};   effort=${BASE_EFFORT:-max};   list=base-load-max.txt ;;
  xhigh) name=${BASE_NAME:-xhigh-base}; effort=${BASE_EFFORT:-xhigh}; list=base-load-xhigh.txt ;;
  high)  name=${BASE_NAME:-high-base};  effort=${BASE_EFFORT:-high};  list=base-load-high.txt ;;
  *) echo "usage: base.sh max|xhigh|high pack|build|build-files|status|seal|extend <file>|layer|warm|drop" >&2; exit 2 ;;
esac
model=${BASE_MODEL:-claude-opus-5[1m]}
role="$HERE/library-prompt.md"  # one role-neutral system prompt for every base; each fork's first message says its role
# The base being built names its list: an ORCH_LOAD_LIST inherited from whoever called this would silently pack
# another base's content into it, and the daemon that runs `base.sh WHO warm` was carrying max's on 2026-09-20.
# BASE_LOAD_LIST is the deliberate override, like BASE_NAME and BASE_PACK_DIR.
export ORCH_LOAD_LIST="${BASE_LOAD_LIST:-$HERE/$list}"
# The base and every session forked from it start with exactly these tools and no connectors or skills list:
# the prefix must be identical for a fork to read the base from cache. The same file is read by v2.py (fork).
LEAN=$(cat "$HERE/session-flags")
rec="$STATE/$who-base.json"; building="$STATE/$who-base-building.json"; SESSIONS="$HOME/.claude/projects/$(echo "$PROJECT" | tr '/_' '--')"
layer="$STATE/$who-layer.json"
# the list of the base asked for, named outright: manifest reads ORCH_LOAD_LIST, and without it falls back to max's
split=$(ORCH_LOAD_LIST="$HERE/$list" python3 -c 'import sys; sys.path.insert(0, sys.argv[1]); import manifest; print(1 if manifest.has_layer() else 0)' "$HERE" 2>/dev/null || echo 0)
field() { python3 -c "import json,sys; print(json.load(open(sys.argv[1])).get(sys.argv[2],''))" "$1" "$2" 2>/dev/null; }
# a layer is a fork of one particular stable base: once the owner has rebuilt the base under it, it is an orphan —
# a fork of a session that is gone — and nothing forks it or pings it (v2.layer_record says the same)
[ -e "$layer" ] && [ "$(field "$layer" base)" != "$(field "$rec" sessionId)" ] && layer="$STATE/$who-layer.orphan.json"
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
    python3 "$HERE/select_base_load.py" --refresh-index >/dev/null || return $?  # the generated indexes, current
    python3 "$HERE/base_pack.py" build --output "$packed" || return $?
  fi
  echo "packed base: $packed"
}

# Nothing here starts a session while the hold is on; packing and reporting still do, since they start none.
case "$cmd" in
  build|build-packed|build-files|layer|extend)
    [ -e "$STATE/no-launch" ] && { echo "refused: $cmd starts a session and the hold is on ($(cat "$STATE/no-launch" 2>/dev/null)). Take it off when you mean to begin: rm $STATE/no-launch" >&2; exit 3; } ;;
esac
case "$cmd" in
  pack) prepare_pack ;;
  build|build-packed|build-files)
    [ -e "$rec" ] && { echo "refused: a $who base is recorded; run base.sh $who drop first"; exit 3; }
    [ -n "$("$HERE/session_row.py" "$name")" ] && { echo "refused: a session named $name is already live"; exit 3; }
    packed=""
    [ "$split" = 1 ] && export ORCH_BASE_PART=stable  # the rest is the layer, built by `base.sh WHO layer`
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
    if [ -e "$layer" ]; then
      lsid=$(field "$layer" sessionId)
      echo "$who layer: sealed $(field "$layer" sealed), context $(field "$layer" context) tokens over the stable base $(field "$rec" sessionId | cut -c1-8); $(python3 "$HERE/manifest.py" stale-share "$who") of what it holds has changed"
    fi
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
    [ "$ctx" -gt $(( target * 103 / 100 )) ] && echo "note: measured $ctx is over the $target target; trim $list before the next build"
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
    [ -e "$rec" ] || { echo "no sealed $who base" >&2; exit 1; }
    # what the roles fork is what must stay warm: the layer when there is one, and a fork of it reads the whole
    # prefix under it, so the stable base stays warm with it (measured 2026-09-20: 538,051 of 538,044 tokens read)
    forked="$rec"; [ -e "$layer" ] && forked="$layer"
    sid=$(field "$forked" sessionId); n="warm-$who"
    claude --bg --resume "$sid" --fork-session $LEAN --model "$(field "$forked" model)" --effort "$(field "$forked" effort)" \
      --permission-mode auto --settings "$HERE/base-settings.json" -n "$n" \
      "Keep-warm ping $(date +%s). Use no tools. Reply with the single word WARM and end your turn." >/dev/null 2>&1
    i=0; while [ $i -lt 90 ]; do set -- $("$HERE/session_row.py" "$n"); case "${3:-}" in done|idle) break ;; esac; i=$((i + 1)); sleep 2; done
    result=$("$HERE/session_fork_check.py" "${4:-none}" "$sid" 2>&1)
    [ -n "${2:-}" ] && { claude stop "$2"; claude rm "$2"; } >/dev/null 2>&1
    [ -n "${4:-}" ] && rm -rf "$SESSIONS/$4" "$SESSIONS/$4.jsonl"
    # a MISS still rewrote the entry, so the base is warm either way; a ping nobody answered (usage limit) is neither
    case "$result" in OK*) touch "$STATE/$who-base.hit"; rm -f "$STATE/$who-base.miss" ;; MISS*) touch "$STATE/$who-base.hit"; echo x >> "$STATE/$who-base.miss" ;; esac
    # The verdict is recorded here, not by whoever redirects this command's output. health.py reads warm.log, and a
    # ping run by hand left nothing in it: on 2026-09-20 all three bases were refreshed by hand at 16:09 and answered
    # OK, and health.py went on reporting the 15:19 daemon ping's COLD for the fifty minutes after.
    line="$(date +%Y-%m-%dT%H:%M:%S) warm $who: $result"
    echo "$line" >> "$STATE/warm.log"
    echo "$line" ;;
  layer)
    [ "$split" = 1 ] || { echo "the $who list is not split by a layer line: there is no layer to refresh" >&2; exit 1; }
    [ -e "$rec" ] || { echo "no sealed $who base to layer over (base.sh $who build, then seal)" >&2; exit 1; }
    export ORCH_BASE_PART=layer
    lock="$STATE/$who-layer.building"
    if [ -e "$lock" ] && [ "$(( $(date +%s) - $(stat -c %Y "$lock") ))" -lt "${LAYER_LOCK:-2400}" ]; then
      echo "a $who layer is already being built (since $(stat -c %y "$lock" | cut -c12-19))" >&2; exit 3
    fi
    echo $$ > "$lock"
    trap 'rm -f "$lock"' EXIT INT TERM
    # the frontier is what the layer holds, so it is re-measured here, from the sessions of the roles that fork it
    python3 "$HERE/select_base_load.py" --frontier "$who" || exit $?
    prepare_pack || exit $?
    bootstrap=$(python3 "$HERE/base_pack.py" bootstrap "$packed") || exit $?
    old_row=$("$HERE/session_row.py" "$(field "$layer" name)")
    n="$who-layer-$(date +%H%M%S)"
    # a fork of the sealed stable base, with no --append-system-prompt-file: a fork inherits the prompt, and any
    # difference in the prefix would cost the whole base a cold write
    claude --bg --resume "$(field "$rec" sessionId)" --fork-session $LEAN --model "$(field "$rec" model)" \
      --effort "$(field "$rec" effort)" --permission-mode auto --autocompact "${BASE_AUTOCOMPACT:-1M}" \
      --settings "$HERE/base-settings.json" -n "$n" "$bootstrap" >/dev/null 2>&1
    i=0
    while [ $i -lt "${LAYER_WAIT:-450}" ]; do
      set -- $("$HERE/session_row.py" "$n")
      case "${3:-}" in done|idle) break ;; esac
      i=$((i + 1)); sleep 2
    done
    set -- $("$HERE/session_row.py" "$n")
    [ -n "${4:-}" ] || { echo "the $who layer did not load: no session $n" >&2; exit 4; }
    lsid=$4; lid=$2
    python3 "$HERE/base_pack.py" check-load "$packed" "$SESSIONS/$lsid.jsonl" || { echo "the $who layer is incomplete; it is not recorded (look with claude attach $lid)" >&2; exit 3; }
    python3 "$HERE/base_pack.py" snapshot "$packed" "$STATE/$who-layer-manifest.json" || exit 3
    cp "$STATE/$who-layer-manifest.json" "$STATE/layer-$lsid-manifest.json"  # kept under its session's name: a session
    # that holds the layer before this one is told what changed since the load it actually has, not since this one
    ctx=$("$HERE/ctx_gauge.py" measure "$SESSIONS/$lsid.jsonl")
    claude stop "$lid" >/dev/null 2>&1
    python3 - "$layer" "$lsid" "$(field "$rec" model)" "$(field "$rec" effort)" "$n" "$packed" "$ctx" "$(field "$rec" sessionId)" <<'LAYERREC'
import json, sys, time
path, sid, model, effort, name, packed, ctx, base_sid = sys.argv[1:]
json.dump(dict(sessionId=sid, model=model, effort=effort, name=name, pack=packed, context=int(ctx),
               base=base_sid, sealed=time.strftime("%Y-%m-%dT%H:%M:%S")), open(path, "w"))
LAYERREC
    # the layer this replaces is stopped, never removed: a fork launched from it while this ran must still find it,
    # and a sealed session is exactly what a base is
    if [ -n "$old_row" ]; then set -- $old_row; claude stop "$2" >/dev/null 2>&1; fi
    touch "$STATE/$who-base.hit" "$STATE/$who-base.used"; rm -f "$STATE/$who-base.miss"; daemon
    echo "sealed the $who layer $lsid at $ctx tokens; its forks have about $(( (${ORCH_WINDOW:-1000000} - ctx) / 1000 ))K of room" ;;
  drop) rm -f "$rec" "$building" "$layer" "$STATE/$who-manifest.json" "$STATE/$who-layer-manifest.json" "$STATE/$who-base.hit" "$STATE/$who-base.used" "$STATE/$who-base.miss"; echo "$who base and layer forgotten; live sessions start plain" ;;
  *) echo "usage: base.sh max pack|build|build-files|status|seal|extend <file>|layer|warm|drop" >&2; exit 2 ;;
esac
