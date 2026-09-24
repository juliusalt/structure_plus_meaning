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
#   base.sh WHO status          one line: load state, measured context against the expected size
#   base.sh WHO stable-warm     exit 0 while the stable base's own cache entry is there (no miss recorded, read within
#                               ORCH_WARM_MAX): what a layer build reads to know whether to load it again first
#   base.sh WHO seal            when the load has finished: verify its size, snapshot the held files, stop it, record it
#   base.sh WHO warm            hit the base's cache entry with a throwaway fork, verify the hit, delete the fork
#                                    (each ping's text is unique, so the longest cached prefix it can match is the base itself)
#   base.sh WHO layer           refresh the frontier layer of a split list (a `# === layer ===` line): re-measure the
#                               frontier, pack what stands below the mark, fork the sealed stable base, load it,
#                               verify it, seal it and record it. Every role of that base then forks the layer, which
#                               reads the whole prefix under it from cache (measured 2026-09-20: 99% of 538K). It
#                               blocks until sealed; repeatable, and the layer it replaces is stopped.
#   base.sh WHO layer --adopt NAME PACK   record a layer session that loaded completely but was not recorded (its
#                               checks refused it, or it was stopped first): the same checks, no second load
#   base.sh WHO delta           make the session the base's roles fork: what the base holds that has changed since its
#                               loads, in its new form, held by a fork of the delta's session or of the layer
#                               (base_stack.py delta; notes/plan-delta-layer.md). --text cuts what changed into a text of
#                               the chain and starts nothing; --whole begins the chain anew as one text first; --ask
#                               QUESTION asks a fork of its session, writing the answer to state/WHO-delta-answer.txt
#   base.sh WHO restable        load a split base's stable part again while the base and layer standing serve; its next
#                               `layer` is built over it, and the two replace the old pair together. A layer build
#                               does this itself when the stable base's cache entry is cold.
#   base.sh WHO drop            forget the base and its layer; the roles that fork it start from the planner's base instead
# BASE_LOAD_LIST overrides the list this base is built from; nothing inherited from the caller does.
set -u
HERE=$(cd "$(dirname "$0")" && pwd); PROJECT=${ORCH_PROJECT:-$(cd "$HERE/../.." && pwd)}; STATE="${ORCH_STATE_DIR:-$HERE/state}"
cd "$PROJECT" || exit 1; mkdir -p "$STATE"
# What a build that fails says, and where the run is read: these run unattended (the watchdog starts layer,
# delta and warm builds in the background), and a failure that leaves nothing behind but a pack said why to
# /dev/null - the high layer refresh of 2026-09-22 21:36 ended in rebuild_stable with no session started, and
# no line anywhere. The message goes to stderr as well, unless stderr is warm.log already (the daemon runs
# `base.sh WHO warm >/dev/null 2>> warm.log`), which would write it twice.
ERRLOG=""  # where stderr goes, read before anything redirects it (`2>/dev/null` in the substitution would be read)
[ -e /proc/self/fd/2 ] && ERRLOG=$(readlink -f /proc/self/fd/2)
fail() {
  echo "$(date +%Y-%m-%dT%H:%M:%S) $*" >> "$STATE/warm.log"
  [ "$ERRLOG" = "$(readlink -f "$STATE/warm.log")" ] || echo "$*" >&2
}
who=${1:-}; cmd=${2:-}
case "$who" in
  max)   name=${BASE_NAME:-max-base};   effort=${BASE_EFFORT:-max};   list=base-load-max.txt ;;
  xhigh) name=${BASE_NAME:-xhigh-base}; effort=${BASE_EFFORT:-xhigh}; list=base-load-xhigh.txt ;;
  high)  name=${BASE_NAME:-high-base};  effort=${BASE_EFFORT:-high};  list=base-load-high.txt ;;
  *) echo "usage: base.sh max|xhigh|high pack|build|status|seal|layer [--adopt NAME PACK]|restable|warm|drop" >&2; exit 2 ;;
esac
model=${BASE_MODEL:-$(cat "$HERE/base-model")}  # every base, and so every fork of one (v2.base_model)
role="$HERE/library-prompt.md"  # one role-neutral system prompt for every base; each fork's first message says its role
# The base being built names its list: an ORCH_LOAD_LIST inherited from whoever called this would silently pack
# another base's content into it, and the daemon that runs `base.sh WHO warm` was carrying max's on 2026-09-20.
# BASE_LOAD_LIST is the deliberate override, like BASE_NAME and BASE_PACK_DIR.
export ORCH_LOAD_LIST="${BASE_LOAD_LIST:-$HERE/$list}"
# The base and every session forked from it start with exactly these tools and no connectors or skills list:
# the prefix must be identical for a fork to read the base from cache. The same file is read by v2.py (fork).
LEAN=$(cat "$HERE/session-flags")
# A base records the flags it was started with, and nothing forks one started with others: every fork of it would
# write its whole prefix again (the tools come first in it). A record from before 2026-09-21 has none: rebuild it.
lean_as() { [ "$(field "$1" flags)" = "$(echo $LEAN)" ]; }
rec="$STATE/$who-base.json"; building="$STATE/$who-base-building.json"; SESSIONS="$HOME/.claude/projects/$(echo "$PROJECT" | tr '/_' '--')"
layer="$STATE/$who-layer.json"
next="$STATE/$who-base-next.json"; next_manifest="$STATE/$who-manifest-next.json"  # a stable base loaded again (restable)
# the list of the base asked for, named outright: manifest reads ORCH_LOAD_LIST, and without it falls back to max's
split=$(ORCH_LOAD_LIST="${BASE_LOAD_LIST:-$HERE/$list}" python3 -c 'import sys; sys.path.insert(0, sys.argv[1]); import manifest; print(1 if manifest.has_layer() else 0)' "$HERE" 2>/dev/null || echo 0)
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
# Whether the stable base's own cache entry is warm: read within its life (a seal, a layer that read it, a ping).
stable_warm() {
  # a recorded miss is the entry's absence, whatever its last read says: the max layer's refresh of 2026-09-22 21:28
  # forked a stable base evicted twelve minutes before, whose hit was 51 minutes old, and wrote its 341K inside the
  # layer's own prefix — leaving no stable entry for the refreshes after it
  if [ -e "$STATE/$who-stable.miss" ]; then
    # unless the base was sealed after the miss was recorded: that load wrote the entry the miss speaks of (a `seal`,
    # or a layer that adopted a base loaded again), and a miss left from the base before it would send every refresh
    # from here on through a fifteen-minute reload of the stable base
    # a record with no seal time is no seal: `date -d ""` is midnight today, not an error, and read so it made every
    # miss recorded before midnight look answered (found at 00:01 on 2026-09-23, when the test's miss fell before it)
    sealed=$(field "$rec" sealed); sealed_s=0
    [ -n "$sealed" ] && sealed_s=$(date -d "$sealed" +%s 2>/dev/null || echo 0)
    [ "${sealed_s:-0}" -gt "$(stat -c %Y "$STATE/$who-stable.miss")" ] || return 1
    rm -f "$STATE/$who-stable.miss"
  fi
  [ -e "$STATE/$who-stable.hit" ] && [ "$(( $(date +%s) - $(stat -c %Y "$STATE/$who-stable.hit") ))" -lt "${ORCH_WARM_MAX:-3300}" ]
}
# A layer is a fork of its stable base, and a fork of a base whose own entry is gone writes the whole base again — and
# so would every refresh after it, since a fork that misses never makes that entry again (each fork's first turn
# names the fork: the sandbox's instructions carry its session id). So a cold stable base is loaded again before its
# layer, which costs about what that one cold write would and leaves an entry the daemon keeps (the owner,
# 2026-09-21: the harness rebuilds it). The base and layer standing serve until the new pair is sealed: the new base
# is recorded in $next, its snapshot in $next_manifest, and seal_layer puts both in place with the layer.
rebuild_stable() {
  echo "$(date +%Y-%m-%dT%H:%M:%S) stable $who: ${1:-its entry is cold}, so the base is loaded again before its layer" >> "$STATE/warm.log"
  export ORCH_BASE_PART=stable
  prepare_pack || return $?
  bootstrap=$(python3 "$HERE/base_pack.py" bootstrap "$packed") || return $?
  cp "${BASE_PROMPT_FILE:-$role}" "$packed/prompt.md" || return $?
  prompt_hash=$(sha256sum "$packed/prompt.md" | cut -d' ' -f1)
  bn="$who-base-$(date +%H%M%S)"
  claude --bg $LEAN --model "$model" --effort "$effort" --permission-mode auto --autocompact "${BASE_AUTOCOMPACT:-1M}" \
    --settings "$HERE/base-settings.json" --append-system-prompt-file "$packed/prompt.md" \
    -n "$bn" "$bootstrap" >/dev/null 2>&1
  i=0
  while [ $i -lt "${STABLE_WAIT:-900}" ]; do
    set -- $("$HERE/session_row.py" "$bn")
    case "${3:-}" in done|idle) break ;; esac
    [ -z "${4:-}" ] && [ $i -ge 15 ] && break  # never listed: it did not start
    i=$((i + 1)); sleep 2
  done
  set -- $("$HERE/session_row.py" "$bn")
  [ -n "${4:-}" ] || { fail "the $who base was not loaded again: no session $bn; nothing is replaced"; return 4; }
  case "${3:-}" in done|idle) ;; *) claude stop "$2" >/dev/null 2>&1
    fail "the $who base did not finish loading ($bn); nothing is replaced"; return 4 ;; esac
  bsid=$4
  python3 "$HERE/base_pack.py" check-load "$packed" "$SESSIONS/$bsid.jsonl" \
    || { claude stop "$2" >/dev/null 2>&1; fail "the $who base's load is incomplete ($bn); nothing is replaced"; return 3; }
  python3 "$HERE/base_pack.py" snapshot "$packed" "$next_manifest" || return 3
  bctx=$("$HERE/ctx_gauge.py" measure "$SESSIONS/$bsid.jsonl")
  claude stop "$2" >/dev/null 2>&1
  python3 - "$next" "$bsid" "$model" "$effort" "$bn" "$packed" "$(echo $LEAN)" "$bctx" "$prompt_hash" <<'PY'
import json, sys, time
path, sid, model, effort, name, packed, flags, ctx, prompt_hash = sys.argv[1:]
json.dump(dict(sessionId=sid, model=model, effort=effort, name=name, flags=flags, pack=packed, context=int(ctx), prompt_sha256=prompt_hash,
               sealed=time.strftime("%Y-%m-%dT%H:%M:%S")), open(path, "w"))
PY
  export ORCH_BASE_PART=layer
  under="$next"
  echo "loaded the $who base again as $bn at $bctx tokens; its layer follows"
}
# A session forked before the stable base was rebuilt holds the old one: the snapshot kept under the layer it forked
# takes in the old stable snapshot, so that it is still told what changed since the load it actually holds.
keep_stable_snapshot() {
  python3 - "$HERE" "$who" "$STATE/$who-manifest.json" "$(field "$STATE/$who-layer.json" sessionId)" <<'PY'
import json, os, sys
here, who, stable, current = sys.argv[1:]
sys.path.insert(0, here)
import v2
held = {s.get("origin_sid") for s in v2.peek()["sessions"].values() if s.get("origin") == who} | {current}
try:
    old = json.load(open(stable))["files"]
except (OSError, ValueError, KeyError):
    sys.exit(0)
for sid in filter(None, held):
    path = os.path.join(v2.STATE, f"layer-{sid}-manifest.json")
    try:
        d = json.load(open(path))
    except (OSError, ValueError):
        continue
    if not d.get("stable"):
        d["files"], d["stable"] = {**old, **d["files"]}, True
        json.dump(d, open(path + ".tmp", "w"))
        os.replace(path + ".tmp", path)
PY
}
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
# What makes a loaded layer the one every role forks ($packed, $n, $lsid, $lid, $old_row): its load checked complete,
# its held files snapshotted, its context measured, the session stopped and recorded, the layer it replaces stopped.
# `layer` and `layer --adopt` both end here.
seal_layer() {
  python3 "$HERE/base_pack.py" check-load "$packed" "$SESSIONS/$lsid.jsonl" || { fail "the $who layer is incomplete; it is not recorded (look with claude attach $lid)"; exit 3; }
  python3 "$HERE/base_pack.py" snapshot "$packed" "$STATE/$who-layer-manifest.json" || exit 3
  under=${under:-$rec}  # the stable base this layer stands on: the one recorded, or the one just loaded again
  stable_manifest="$STATE/$who-manifest.json"; [ "$under" = "$rec" ] || stable_manifest="$next_manifest"
  # kept under its session's name, with the stable snapshot it stands on: a session that holds the layer before this
  # one is told what changed since the load it actually has, not since this one — nor since a stable base loaded again
  python3 - "$stable_manifest" "$STATE/$who-layer-manifest.json" "$STATE/layer-$lsid-manifest.json" <<'KEEP' || exit 3
import json, sys
stable, layer, kept = sys.argv[1:]
d = json.load(open(layer))
try:  # a base without a snapshot of its own: the layer's alone, as before
    d["files"], d["stable"] = {**json.load(open(stable))["files"], **d["files"]}, True
except (OSError, ValueError, KeyError):
    pass
json.dump(d, open(kept, "w"))
KEEP
  ctx=$("$HERE/ctx_gauge.py" measure "$SESSIONS/$lsid.jsonl")
  # Whether the layer read its stable base from cache or wrote it anew, said in warm.log where health.py reads it. A
  # read of the layer does not keep the base's own, shorter entry alive: the max layer's refresh of 2026-09-21 22:40
  # read 9,270 tokens and wrote 339,381, the base's last own read three hours before — so the stable base is pinged
  # on its own while its entry is warm (warm stable, warm_daemon.sh). Only a read that hit leaves it warm: a fork that
  # missed wrote its own prefix, which no later fork of the base reads — the refresh of 22:25 had written the same
  # 339,377 fifteen minutes before the one of 22:40 missed again. Once the entry is gone, only a rebuild makes one.
  read=$("$HERE/session_fork_check.py" "$lsid" "$(field "$under" sessionId)" 2>&1 | head -1)
  echo "$(date +%Y-%m-%dT%H:%M:%S) layer $who: $read" >> "$STATE/warm.log"
  claude stop "$lid" >/dev/null 2>&1
  python3 - "$STATE/$who-layer.json.new" "$lsid" "$(field "$under" model)" "$(field "$under" effort)" "$n" "$packed" "$ctx" "$(field "$under" sessionId)" "$(echo $LEAN)" <<'LAYERREC'
import json, sys, time
path, sid, model, effort, name, packed, ctx, base_sid, flags = sys.argv[1:]
json.dump(dict(sessionId=sid, model=model, effort=effort, name=name, pack=packed, context=int(ctx),
               base=base_sid, sealed=time.strftime("%Y-%m-%dT%H:%M:%S"), flags=flags), open(path, "w"))
LAYERREC
  if [ "$under" != "$rec" ]; then
    # the new stable base and its layer take the place of the old pair together, two renames apart: between them a
    # role would fork the layer standing (its base no longer recorded: v2.layer_record) or the new base alone
    keep_stable_snapshot
    mv "$next_manifest" "$STATE/$who-manifest.json"
    mv "$next" "$rec"
  fi
  mv "$STATE/$who-layer.json.new" "$STATE/$who-layer.json"
  # the layer this replaces is stopped, never removed: a fork launched from it while this ran must still find it,
  # and a sealed session is exactly what a base is
  if [ -n "$old_row" ]; then set -- $old_row; claude stop "$2" >/dev/null 2>&1; fi
  touch "$STATE/$who-base.hit" "$STATE/$who-base.used" "$STATE/$who-layer.hit"; rm -f "$STATE/$who-base.miss" "$STATE/$who-layer.miss"
  case "$read" in OK*) touch "$STATE/$who-stable.hit"; rm -f "$STATE/$who-stable.miss" ;; esac
  daemon
  # a base its layer takes over the owner's target is said when it is sealed: the high base grew from 525K to 602K
  # in a day and nothing said so (2026-09-22). The frontier is chosen within the layer's room (select_base_load),
  # so this says an estimate that did not hold.
  target=${ORCH_BASE_TARGET:-530000}  # manifest.TARGET
  if [ "$ctx" -gt $(( target * 103 / 100 )) ]; then
    fail "note: the $who base is $ctx tokens with its layer, over the $target target; its frontier was chosen within an estimated room (select_base_load --frontier $who, the tier's header)"
  fi
  echo "sealed the $who layer $lsid at $ctx tokens; its forks have about $(( (${ORCH_WINDOW:-1000000} - ctx) / 1000 ))K of room"
  echo "its read of the base: $read"
}

# A delta's text is cut locally and starts no session: neither the sandbox nor the hold is in its way.
if [ "$cmd" = delta ] && [ "${3:-}" = --text ]; then
  exec python3 -B "$HERE/base_stack.py" delta "$who" --text ${4:+"$4"}
fi
# Starting, stopping and removing sessions cannot be done from inside Claude Code's sandbox (v2.py control): these
# are run from the owner's own terminal, or by the daemon, which runs outside it.
case "$cmd" in
  build|build-packed|layer|restable|seal|warm|delta) "$HERE/v2.py" control || exit 3 ;;
esac
# Nothing here starts a session while the hold is on; packing and reporting still do, since they start none.
case "$cmd" in
  build|build-packed|layer|restable|delta)
    [ -e "$STATE/no-launch" ] && { echo "refused: $cmd starts a session and the hold is on ($(cat "$STATE/no-launch" 2>/dev/null)). Take it off when you mean to begin: rm $STATE/no-launch" >&2; exit 3; } ;;
esac
# Named boundaries use the same checked pack loader and v2.fork, with a reusable record per part.
if [ "$cmd" = layer ] && [ "${3:-}" != --adopt ] && \
   python3 -c 'import sys; sys.path.insert(0,sys.argv[1]); import manifest; sys.exit(0 if any(x != "layer" for x in manifest.layer_names()) else 1)' "$HERE"; then
  exec python3 -B "$HERE/base_stack.py" build "$who" ${3:+"$3"} ${4:+"$4"}   # --from PART: the watchdog's refresh_plan
fi
# the delta's session, made on demand over its chain of texts (base_stack.materialize); --ask is answered below
if [ "$cmd" = delta ] && [ "${3:-}" != --ask ]; then
  exec python3 -B "$HERE/base_stack.py" delta "$who" ${3:+"$3"} ${4:+"$4"}
fi
if [ "$cmd" = warm ] && [ -n "${3:-}" ] && [ "$3" != stable ] && [ "$3" != layer ]; then
  exec python3 -B "$HERE/base_stack.py" warm "$who" "$3"
fi
case "$cmd" in
  pack) prepare_pack ;;
  build|build-packed)
    [ -e "$rec" ] && { echo "refused: a $who base is recorded; run base.sh $who drop first"; exit 3; }
    [ -n "$("$HERE/session_row.py" "$name")" ] && { echo "refused: a session named $name is already live"; exit 3; }
    packed=""
    [ "$split" = 1 ] && export ORCH_BASE_PART=stable  # the rest is the layer, built by `base.sh WHO layer`
    # packed and loaded through Bash: the older loader read every file with the Read tool, which no base has had since
    # the owner took it out (2026-09-21), and `extend` went with it
    prepare_pack || exit $?
    bootstrap=$(python3 "$HERE/base_pack.py" bootstrap "$packed") || exit $?
    cp "${BASE_PROMPT_FILE:-$role}" "$packed/prompt.md" || exit $?
    prompt_hash=$(sha256sum "$packed/prompt.md" | cut -d' ' -f1)
    claude --bg $LEAN --model "$model" --effort "$effort" --permission-mode auto --autocompact "${BASE_AUTOCOMPACT:-1M}" \
      --settings "$HERE/base-settings.json" --append-system-prompt-file "$packed/prompt.md" \
      -n "$name" "$bootstrap" >/dev/null 2>&1
    sleep 2; set -- $("$HERE/session_row.py" "$name")
    [ -n "${4:-}" ] || { echo "start of $name not confirmed"; exit 4; }
    python3 - "$building" "$4" "$model" "$effort" "$name" "$packed" "$(echo $LEAN)" "$prompt_hash" <<'PY'
import json, sys
path, sid, model, effort, name, packed, flags, prompt_hash = sys.argv[1:]
record = dict(sessionId=sid, model=model, effort=effort, name=name, flags=flags, prompt_sha256=prompt_hash)
if packed:
    record["pack"] = packed
json.dump(record, open(path, "w"))
PY
    echo "loading $name id=$2: estimated $(expected)K loaded; check with base.sh $who status, then base.sh $who seal" ;;
  stable-warm)  # whether the stable base's own entry is there (exit 0), for a layer build and for the tests
    stable_warm ;;
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
    [ -n "$packed" ] || { echo "refused: $name was not loaded from a pack, which is the one loader there is"; exit 3; }
    python3 "$HERE/base_pack.py" check-load "$packed" "$SESSIONS/$sid.jsonl" || exit 3
    # The manifest must describe the frozen sources the model received, even
    # if the working files changed while it was loading.
    python3 "$HERE/base_pack.py" snapshot "$packed" "$STATE/$who-manifest.json" || exit 3
    claude stop "$2" >/dev/null 2>&1
    python3 - "$building" "$rec" "$ctx" <<'PY'
import json, sys, time
d = json.load(open(sys.argv[1])); d.update(context=int(sys.argv[3]), sealed=time.strftime("%Y-%m-%dT%H:%M:%S"))
json.dump(d, open(sys.argv[2], "w"))
PY
    rm -f "$building"; touch "$STATE/$who-base.hit" "$STATE/$who-base.used" "$STATE/$who-stable.hit"; daemon
    target=${ORCH_BASE_TARGET:-530000}  # manifest.TARGET
    [ "$ctx" -gt $(( target * 103 / 100 )) ] && echo "note: measured $ctx is over the $target target; trim $list before the next build"
    echo "sealed $who base $sid at $ctx tokens (target $target); its forks have about $(( (${ORCH_WINDOW:-1000000} - ctx) / 1000 ))K of room; keep-warm daemon running" ;;
  warm)
    [ -e "$rec" ] || { echo "no sealed $who base" >&2; exit 1; }
    # what the roles fork is what must stay warm: the layer when there is one. A fork of it reads the prefix under it
    # through the layer's own entry, which does not keep the stable base's shorter entry alive (the max refresh of
    # 2026-09-21 wrote 339,381 tokens of it anew): `warm stable` pings the stable base itself, and keeps its own time
    # Under a delta (notes/plan-delta-layer.md) the roles fork the delta, and the layer's own entry is read only by the
    # delta's builds: `warm layer` pings it, under the stable ping's rule.
    part=""; case "${3:-}" in stable|layer) part=$3 ;; esac
    stable=0; [ "$part" = stable ] && stable=1
    forks_delta() { python3 -c 'import sys; sys.path.insert(0, sys.argv[1]); import v2; sys.exit(0 if v2.base_file(sys.argv[2]).endswith("-delta.json") else 1)' "$HERE" "$who"; }
    if [ "${4:-}" = "--if-due" ]; then  # the daemon's: only under a layer (a delta), only while warm, not after 2 misses
      s_age=$( [ -e "$STATE/$who-$part.hit" ] && echo $(( $(date +%s) - $(stat -c %Y "$STATE/$who-$part.hit") )) || echo 999999999 )
      [ -e "$layer" ] && [ "$s_age" -ge "${ORCH_WARM_EVERY:-2400}" ] && [ "$s_age" -lt "${ORCH_WARM_MAX:-3300}" ] \
        && [ "$( [ -e "$STATE/$who-$part.miss" ] && wc -l < "$STATE/$who-$part.miss" || echo 0)" -lt 1 ] || exit 0
      [ "$part" = layer ] && { forks_delta || exit 0; }
      # the stable reference under a chain of parts: kept while its pings since its last use cost less than the chain
      # loaded again over it (base_stack.worth_keeping)
      [ "$part" = stable ] && { python3 -B "$HERE/base_stack.py" worth "$who" stable >/dev/null 2>&1 || exit 0; }
      # one ping of an entry at a time: the watchdog asks each minute while it is due, and the daemon too
      pinging="$STATE/$who-$part.pinging"
      [ -e "$pinging" ] && [ "$(( $(date +%s) - $(stat -c %Y "$pinging") ))" -lt 300 ] && exit 0
      touch "$pinging"; trap 'rm -f "$pinging"' EXIT
    fi
    # what the roles fork is the one rule v2.base_file keeps: the delta when its base is switched to it and it stands on
    # the layer, the layer when it stands on the base, the stable base otherwise
    case "$part" in
      stable) forked="$rec" ;;
      layer) forked="$layer" ;;
      *) forked=$(python3 -c 'import sys; sys.path.insert(0, sys.argv[1]); import v2; print(v2.base_file(sys.argv[2]))' "$HERE" "$who" 2>/dev/null)
         [ -e "$forked" ] || forked="$rec" ;;
    esac
    mark="$who-base"; [ -n "$part" ] && mark="$who-$part"
    lean_as "$forked" || { fail "refused: the $who base was started with other tools than session-flags gives now, so a ping would write its whole prefix again: build it again (base.sh $who build, then seal)"; exit 3; }
    sid=$(field "$forked" sessionId); n="warm-$who"; [ -n "$part" ] && n="warm-$who-$part"
    claude --bg --resume "$sid" --fork-session $LEAN --model "$(field "$forked" model)" --effort "$(field "$forked" effort)" \
      --permission-mode auto --settings "$HERE/base-settings.json" -n "$n" \
      "Keep-warm ping $(date +%s). Use no tools. Reply with the single word WARM and end your turn." >/dev/null 2>&1
    i=0; while [ $i -lt 90 ]; do set -- $("$HERE/session_row.py" "$n"); case "${3:-}" in done|idle) break ;; esac; i=$((i + 1)); sleep 2; done
    result=$("$HERE/session_fork_check.py" "${4:-none}" "$sid" 2>&1)
    [ -n "${2:-}" ] && { claude stop "$2"; claude rm "$2"; } >/dev/null 2>&1
    [ -n "${4:-}" ] && rm -rf "$SESSIONS/$4" "$SESSIONS/$4.jsonl"
    # A MISS wrote the fork's own prefix, never the entry it missed: every fork's first turn names the fork itself (the
    # sandbox's instructions carry its session id), so no later fork reads what a miss wrote — the max refreshes of
    # 2026-09-21 at 22:25 and 22:40 both missed. It is counted and not taken as a read, and one miss stops that entry's
    # pings: an entry that is gone does not come back, and each further ping writes its whole prefix for nothing — the
    # evicted stable bases of 2026-09-22 21:16-21:20 were pinged twice each, 341K and 268K a ping, both times missing.
    # What makes an entry again is a load: a layer refresh (which loads a cold stable base first), a delta's build, or
    # a base's rebuild, and each clears the misses of what it wrote. A ping nobody answered (usage limit) is neither.
    # and the entry's own mark, which base_stack reads for a part (warm): the two marks of one entry agree
    case "$result" in OK*) touch "$STATE/$mark.hit"; rm -f "$STATE/$mark.miss"; mkdir -p "$STATE/entry-hits"
                          touch "$STATE/entry-hits/$sid"; rm -f "$STATE/entry-hits/$sid.miss" ;;
                      MISS*) echo x >> "$STATE/$mark.miss" ;; esac
    # The verdict is recorded here, not by whoever redirects this command's output. health.py reads warm.log, and a
    # ping run by hand left nothing in it: on 2026-09-20 all three bases were refreshed by hand at 16:09 and answered
    # OK, and health.py went on reporting the 15:19 daemon ping's COLD for the fifty minutes after.
    line="$(date +%Y-%m-%dT%H:%M:%S) warm $who$([ -n "$part" ] && echo " $part"): $result"
    echo "$line" >> "$STATE/warm.log"
    echo "$line" ;;
  layer)
    [ "$split" = 1 ] || { fail "the $who list is not split by a layer line: there is no layer to refresh"; exit 1; }
    [ -e "$rec" ] || { fail "no sealed $who base to layer over (base.sh $who build, then seal)"; exit 1; }
    lean_as "$rec" || { fail "refused: the $who base was started with other tools than session-flags gives now, so a layer over it would write its whole prefix again: build it again (base.sh $who build, then seal)"; exit 3; }
    export ORCH_BASE_PART=layer
    lock="$STATE/$who-layer.building"
    if [ -e "$lock" ] && [ "$(( $(date +%s) - $(stat -c %Y "$lock") ))" -lt "${LAYER_LOCK:-2400}" ]; then
      echo "a $who layer is already being built (since $(stat -c %y "$lock" | cut -c12-19))" >&2; exit 3
    fi
    echo $$ > "$lock"
    trap 'rm -f "$lock"' EXIT INT TERM
    if [ "${3:-}" = "--adopt" ]; then
      # A layer session that loaded completely and was not recorded is recorded as it stands, not loaded again: on
      # 2026-09-21 the max layer's four chunks all arrived and one character of the id it replied was wrong, and
      # loading it again would have written 135K. The same checks as a new layer's: a complete load (seal_layer), and
      # a fork of this base.
      n=${4:-}; packed=${5:-}
      [ -n "$n" ] && [ -n "$packed" ] || { echo "usage: base.sh $who layer --adopt SESSION-NAME PACK-DIR" >&2; exit 2; }
      case "$packed" in /*) ;; *) packed="$PROJECT/$packed" ;; esac
      set -- $("$HERE/session_row.py" "$n")
      [ -n "${4:-}" ] || { echo "refused: no session named $n is listed" >&2; exit 4; }
      lsid=$4; lid=$2
      # a fork of the base recorded, or of the one loaded again for it (restable), which it then replaces
      under="$rec"
      if ! "$HERE/session_fork_check.py" --is-fork "$lsid" "$(field "$rec" sessionId)" >/dev/null 2>&1; then
        { [ -e "$next" ] && "$HERE/session_fork_check.py" --is-fork "$lsid" "$(field "$next" sessionId)" >/dev/null 2>&1 \
          && under="$next"; } || { echo "refused: $n is not a fork of the $who base; nothing is recorded" >&2; exit 3; }
      fi
      old_row=$("$HERE/session_row.py" "$(field "$layer" name)")
      case "$old_row" in *" $lid "*) old_row="" ;; esac  # the layer it replaces is not the one adopted
    else
      if [ -e "$next" ] && [ -e "$next_manifest" ] && [ "$(( $(date +%s) - $(stat -c %Y "$next") ))" -lt "${ORCH_WARM_MAX:-3300}" ]; then
        under="$next"  # loaded again for a layer that was not sealed, and still warm: not loaded a third time
      elif ! listed=$(python3 "$HERE/manifest.py" stable-listed "$who"); then
        rebuild_stable "$listed" || exit $?  # the list names another reference than the one recorded
      elif stable_warm; then
        under="$rec"
      else
        rebuild_stable || exit $?
      fi
      # the frontier is what the layer holds, so it is re-measured here, from the sessions of the roles that fork it
      python3 "$HERE/select_base_load.py" --frontier "$who" || exit $?
      prepare_pack || exit $?
      bootstrap=$(python3 "$HERE/base_pack.py" bootstrap "$packed") || exit $?
      old_row=$("$HERE/session_row.py" "$(field "$layer" name)")
      n="$who-layer-$(date +%H%M%S)"
      # a fork of the sealed stable base, with no --append-system-prompt-file: a fork inherits the prompt, and any
      # difference in the prefix would cost the whole base a cold write
      claude --bg --resume "$(field "$under" sessionId)" --fork-session $LEAN --model "$(field "$under" model)" \
        --effort "$(field "$under" effort)" --permission-mode auto --autocompact "${BASE_AUTOCOMPACT:-1M}" \
        --settings "$HERE/base-settings.json" -n "$n" "$bootstrap" >/dev/null 2>&1
      i=0
      while [ $i -lt "${LAYER_WAIT:-450}" ]; do
        set -- $("$HERE/session_row.py" "$n")
        case "${3:-}" in done|idle) break ;; esac
        i=$((i + 1)); sleep 2
      done
      set -- $("$HERE/session_row.py" "$n")
      [ -n "${4:-}" ] || { fail "the $who layer did not load: no session $n"; exit 4; }
      lsid=$4; lid=$2
    fi
    seal_layer ;;
  delta)
    # `delta --ask QUESTION` forks the delta's session with a question and writes its answer to
    # state/WHO-delta-answer.txt (the canary, notes/plan-delta-layer-tasks.md task 8); every other form of `delta` is
    # base_stack.py's (above): texts cut when something takes them, a session made when a fork of the base has paid.
    [ "$split" = 1 ] || { fail "the $who list is not split by a layer line: there is no layer to hold a delta over"; exit 1; }
    { [ -e "$rec" ] && [ -e "$layer" ]; } || { fail "no sealed $who base with a layer to hold a delta over"; exit 1; }
    [ "$(field "$layer" base)" = "$(field "$rec" sessionId)" ] || { fail "the $who layer stands on a base that is gone: refresh the layer first"; exit 1; }
    delta="$STATE/$who-delta.json"
    { [ -e "$delta" ] && [ "$(field "$delta" layer)" = "$(field "$layer" sessionId)" ] && [ -n "$(field "$delta" sessionId)" ]; } \
      || { fail "no $who delta session stands on its layer (base.sh $who delta makes one)"; exit 1; }
    n="$who-delta-ask-$(date +%H%M%S)"
    claude --bg --resume "$(field "$delta" sessionId)" --fork-session $LEAN --model "$(field "$delta" model)" \
      --effort "$(field "$delta" effort)" --permission-mode auto --settings "$HERE/base-settings.json" -n "$n" \
      "${4:-} Answer from what you hold, briefly, and use no tools." >/dev/null 2>&1
    i=0; while [ $i -lt "${LAYER_WAIT:-450}" ]; do set -- $("$HERE/session_row.py" "$n"); case "${3:-}" in done|idle) break ;; esac; i=$((i + 1)); sleep 2; done
    set -- $("$HERE/session_row.py" "$n")
    [ -n "${4:-}" ] || { fail "the $who delta was asked nothing: no session $n"; exit 4; }
    python3 "$HERE/base_pack.py" last-reply "$SESSIONS/$4.jsonl" > "$STATE/$who-delta-answer.txt"
    { claude stop "$2"; claude rm "$2"; } >/dev/null 2>&1
    rm -rf "${SESSIONS:?}/$4" "$SESSIONS/$4.jsonl"
    echo "the $who delta answered: $STATE/$who-delta-answer.txt" ;;
  restable)
    [ "$split" = 1 ] || { echo "the $who list is not split by a layer line: its base is rebuilt by drop, build and seal" >&2; exit 1; }
    [ -e "$rec" ] || { echo "no sealed $who base to load again (base.sh $who build, then seal)" >&2; exit 1; }
    lock="$STATE/$who-layer.building"
    if [ "${BASE_STACK_LOCKED:-0}" != 1 ] && [ -e "$lock" ] && [ "$(( $(date +%s) - $(stat -c %Y "$lock") ))" -lt "${LAYER_LOCK:-2400}" ]; then
      echo "a $who layer is being built (since $(stat -c %y "$lock" | cut -c12-19)): it loads the base again if it must" >&2; exit 3
    fi
    if [ "${BASE_STACK_LOCKED:-0}" != 1 ]; then
      echo $$ > "$lock"
      trap 'rm -f "$lock"' EXIT INT TERM
    fi
    rebuild_stable || exit $?
    echo "the next $who layer is built over it (base.sh $who layer), and the two replace the old pair together" ;;
  drop) rm -f "$STATE/$who-reasoning.json" "$STATE/$who-reasoning.hit" "$STATE/$who-reasoning.miss" "$STATE/$who-reasoning-failed.json" "$STATE/$who-load-next.txt" "$STATE/$who-part-"*.json; rm -f "$rec" "$building" "$layer" "$STATE/$who-base-next.json" "$STATE/$who-manifest-next.json" "$STATE/$who-manifest.json" "$STATE/$who-layer-manifest.json" "$STATE/$who-base.hit" "$STATE/$who-base.used" "$STATE/$who-base.miss" "$STATE/$who-stable.hit" "$STATE/$who-stable.miss"; echo "$who base and layer forgotten; live sessions start plain" ;;
  *) echo "usage: base.sh max pack|build|status|seal|layer [--adopt NAME PACK]|delta [--text|--whole|--ask QUESTION]|restable|warm|drop" >&2; exit 2 ;;
esac
