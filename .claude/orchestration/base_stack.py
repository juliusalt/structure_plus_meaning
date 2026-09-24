#!/usr/bin/env python3
"""Build and inspect a base's named material parts and the reasoning over its reference.

The load list supplies the ordered material boundaries. Each cached part records its direct parent, the entries it
holds and the exact text it loaded. A rebuild reuses an unchanged warm prefix and rebuilds only its dependent suffix.
The existing v2.launch and v2.fork, and base_pack's loader and checker, launch and verify every session; no new
execution path is invented. The final part remains the compatibility entry the delta and the role layers consume.

A build works on a candidate copy of the base's list and installs it as the base's list only once the chain it
describes is published: a list is always the description of the chain that stands, which is what the delta
(manifest.delta_entries) and each task's relations (select_base_load.task_relations) measure against. A build that
fails leaves both as they were (2026-09-23: the list written first and a failed build after made the delta carry
every newly listed file whole, and hid the failure from the next refresh).
"""
import argparse
import contextlib
import hashlib
import json
import os
from pathlib import Path
import subprocess
import sys
import time

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import base_pack  # noqa: E402
import manifest  # noqa: E402
from digest import held_text  # noqa: E402
import v2  # noqa: E402

STATE = Path(v2.STATE)
PROJECT = Path(v2.PROJECT)
DONE = "REFERENCE UNDERSTOOD"


def read(path):
    try:
        return json.loads(Path(path).read_text())
    except (OSError, ValueError):
        return {}


def write(path, value):
    path = Path(path)
    tmp = path.with_name(path.name + ".tmp-" + str(os.getpid()))
    try:
        base_pack.write_json(tmp, value)
        os.replace(tmp, path)
    finally:
        tmp.unlink(missing_ok=True)


def write_text(path, text):
    path = Path(path)
    tmp = path.with_name(path.name + ".tmp-" + str(os.getpid()))
    try:
        tmp.write_text(text)
        os.replace(tmp, path)
    finally:
        tmp.unlink(missing_ok=True)


def fingerprint(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True, separators=(",", ":")).encode()).hexdigest()


def layout(entries):
    """What a part holds, by entry: its tier, path and depth (not their text, which the delta follows)."""
    return fingerprint([(e["tier"], e["path"], e["level"]) for e in entries])


def list_path(who):
    return Path(os.environ.get("BASE_LOAD_LIST") or HERE / manifest.LISTS[who])


def spec(who):
    """The list's parts in order, each with its purposes, entries, layout and the fingerprint of its held text."""
    path = list_path(who)
    boundaries = manifest.layer_names(path)
    if len(boundaries) != len(set(boundaries)) or "stable" in boundaries:
        raise ValueError("Material boundaries must have distinct names above the stable reference.")
    entries = manifest.list_entries(path.read_text(), str(PROJECT), strict=True)
    out = []
    for name in dict.fromkeys(e["part"] for e in entries):
        es = [e for e in entries if e["part"] == name]
        out.append(dict(part=name, kind="material", purposes=sorted({e["purpose"] for e in es}), entries=es,
                        layout=layout(es),
                        inputs=fingerprint([(e["tier"], e["path"], e["level"], held_text(e["path"], e["level"])[0])
                                            for e in es])))
    return out


def record_path(who, part):
    return STATE / (f"{who}-{part}.json" if part == "reasoning" else f"{who}-part-{part}.json")


def record(who, part):
    """Only a part in the published chain is a current origin (pending builds are not published)."""
    for p in (v2.layer_record(who) or {}).get("parts", []):
        if p.get("part") == part:
            return p
    return None


def mark(who, part, suffix="hit"):
    return STATE / f"{who}-{part}.{suffix}"


def warm(who, part, rec):
    """Whether this very session's cache entry is warm: its own hit, or the part's mark naming it; a candidate's hit
    never warms an older published entry, and a longer prefix's read never warms a shorter one."""
    # the latest read of this very entry, under either of its marks: its own (entry-hits/SID, a fork's read or a part's
    # ping), or the part's mark while it names this session or nobody (base.sh's pings touch it alone) — the own mark
    # alone, set at the build, made a stable base pinged every forty minutes look cold at 56 and loaded again with its
    # whole chain (the simulation of the run of 09-21/22, 2026-09-23)
    marks = [STATE / "entry-hits" / str(rec.get("sessionId"))]
    hit = mark(who, part)
    with contextlib.suppress(OSError):
        if hit.read_text().strip() in ("", rec.get("sessionId")):
            marks.append(hit)
    seen = [m.stat().st_mtime for m in marks if m.exists()]
    miss = mark(who, part, "miss")
    missed = (STATE / "entry-hits" / (str(rec.get("sessionId")) + ".miss")).exists() or (
        miss.exists() and miss.read_text().strip() in ("", rec.get("sessionId")))
    return bool(rec.get("sessionId") and seen and time.time() - max(seen) < v2.WARM_MAX
                and not missed and not v2.other_tools(rec))


def touch(who, part, sid=None):
    mark(who, part).write_text(sid or "")
    if sid:
        (STATE / "entry-hits").mkdir(exist_ok=True)
        (STATE / "entry-hits" / sid).touch()
        (STATE / "entry-hits" / (sid + ".miss")).unlink(missing_ok=True)
    mark(who, part, "miss").unlink(missing_ok=True)


def say(text):
    STATE.mkdir(parents=True, exist_ok=True)
    with (STATE / "warm.log").open("a") as f:
        f.write(time.strftime("%Y-%m-%dT%H:%M:%S") + " " + text + "\n")


def checked(*args, env=None):
    result = subprocess.run([str(x) for x in args], cwd=PROJECT, env=env, capture_output=True, text=True)
    if result.returncode:
        raise RuntimeError(result.stderr.strip() or result.stdout.strip() or f"{args[0]} failed")
    return result.stdout.strip()


def wait_for(row, started):
    deadline = time.monotonic() + int(os.environ.get("LAYER_WAIT", 450)) * 2
    while time.monotonic() < deadline:
        current = v2.row(row["name"])
        if current and current.get("activity") in ("done", "idle"):
            return dict(current, name=row["name"])
        time.sleep(float(os.environ.get("ORCH_STACK_POLL", 2)))
    raise RuntimeError(f"{row['name']} did not finish; its parent remains published")


def forget(name):
    with v2.state() as state:
        state["sessions"].pop(name, None)


def fork(parent, name, prompt):
    """A fork of the part `parent` records, run to its end: (its row, when it started)."""
    org = dict(sid=parent["sessionId"], model=parent["model"], effort=parent["effort"], flags=parent.get("flags"))
    if v2.other_tools(org):
        raise RuntimeError("The parent has different session flags; rebuild its base.")
    started = time.time()
    who = name.split("-", 1)[0]
    if who in v2.BASES and name.startswith(who + "-reasoning-"):
        # The inert role is registered through the existing launcher before it can call a tool: the guard every
        # reasoning session has refuses each call, and the transcript is checked afterwards as well.
        pending = read(STATE / f"{who}-base-next.json")
        origin = f"{who}:next-stable" if pending.get("sessionId") == parent["sessionId"] else f"{who}:stable"
        launched = v2.launch("base-reasoning", str(time.time_ns()), lambda _: prompt, tree=None, origin=origin,
                             reference_base=who)
        if not launched:
            raise RuntimeError("The guarded reference reasoning did not start.")
        rec = v2.peek()["sessions"][launched]
        if rec.get("origin_sid") != parent["sessionId"]:
            v2.claude("stop", rec["id"])
            forget(launched)
            raise RuntimeError("The reference parent changed before launch.")
        row = dict(name=launched, id=rec["id"], sid=rec["sid"])
        try:
            return wait_for(row, rec["started"]), rec["started"]
        except BaseException:
            v2.claude("stop", row["id"])
            forget(launched)
            raise
    row = v2.fork(org, name, "base-settings.json", prompt, cwd=str(PROJECT))
    if not row:
        raise RuntimeError(f"{name} did not start")
    row["name"] = name
    try:
        return wait_for(row, started), started
    except BaseException:
        v2.claude("stop", row["id"])
        raise


def requests(sid, started):
    """[(context, output)] of a session's own main-chain requests since `started`, one per request, in order."""
    import role_evidence
    seen = {}
    for r in role_evidence.own(v2.transcript(sid), started):
        m = r.get("message") or {}
        u = m.get("usage") or {}
        if r.get("type") != "assistant" or not u:
            continue
        context = u.get("input_tokens", 0) + u.get("cache_read_input_tokens", 0) + u.get("cache_creation_input_tokens", 0)
        key = m.get("id") or len(seen)
        was = seen.get(key, (0, 0))
        seen[key] = (max(was[0], context), max(was[1], u.get("output_tokens", 0)))
    return list(seen.values())


def used(sid):
    """A real read of this entry — a build over it, a fork of it — or its making: what its keep-warm pings are weighed
    from (worth_keeping). A ping is a read that keeps it warm, not a use."""
    if sid:
        (STATE / "entry-used").mkdir(exist_ok=True)
        (STATE / "entry-used" / sid).touch()


def worth_keeping(who, part, rec):
    """Whether keeping this part's entry warm still costs less than letting it go cold would: the pings since its last
    use (a build over it, a fork of it, its own load), each a read of its whole prefix (0.1 a token), against what its
    next use then costs to make it again — an intermediate part its own load (2 a token of what it adds, 0.1 of what it
    reads, and its thinking for the reference reasoning), the stable reference the whole chain, which is loaded again
    over a cold reference (reference). The chain's top part stands under everything the roles fork: always kept. The
    rent-or-buy every other upkeep of the harness keeps (worth_holding for a role's layer and churn). Found by the
    simulation of the run of 09-21/22: every part of every base pinged every forty minutes, 7M in fifteen hours in which
    no refresh read any of them — a cold intermediate part costs about what one or two of its pings do."""
    chain = (v2.layer_record(who) or {}).get("parts") or []
    if not chain or not rec.get("sessionId"):
        return True
    ids = [node.get("sessionId") for node in chain]
    if rec["sessionId"] == ids[-1]:
        return True
    mark = STATE / "entry-used" / rec["sessionId"]
    try:
        last = mark.stat().st_mtime
    except OSError:
        last = time.mktime(time.strptime(rec["sealed"], "%Y-%m-%dT%H:%M:%S")) if rec.get("sealed") else time.time()
    pings = int((time.time() - last) // int(os.environ.get("ORCH_WARM_EVERY", 2400)))
    context = int(rec.get("context") or 0)
    if rec["sessionId"] == ids[0]:
        remake = 2 * int(chain[-1].get("context") or 0)  # the whole chain, over the reference loaded again
    else:
        i = ids.index(rec["sessionId"]) if rec["sessionId"] in ids else 1
        under = int(chain[i - 1].get("context") or 0)
        remake = 2 * max(0, context - under) + 0.1 * under + 5 * int(rec.get("thought") or 0)
    return (pings + 1) * 0.1 * context < remake


def cache_read(who, part, row, parent):
    result = subprocess.run([str(HERE / "session_fork_check.py"), row["sid"], parent["sessionId"]],
                            cwd=PROJECT, capture_output=True, text=True)
    verdict = (result.stdout or result.stderr).splitlines()
    verdict = verdict[0] if verdict else "UNKNOWN no cache report"
    say(f"warm {who} {part[5:]}: {verdict}" if part.startswith("warm ") else f"{part} {who}: {verdict}")
    if verdict.startswith("OK"):
        touch(who, parent.get("part", "stable"), parent["sessionId"])
        if not part.startswith("warm "):
            used(parent["sessionId"])  # a build read it: its use, which a ping is not (worth_keeping)
    elif verdict.startswith("MISS"):
        mark(who, parent.get("part", "stable"), "miss").write_text(parent["sessionId"])
        (STATE / "entry-hits").mkdir(exist_ok=True)
        (STATE / "entry-hits" / (parent["sessionId"] + ".miss")).touch()


def snapshot_union(parent_path, own_path, sid):
    parent, own = read(parent_path), read(own_path)
    own.update(files={**parent.get("files", {}), **own.get("files", {})}, stable=True)
    path = STATE / f"layer-{sid}-manifest.json"
    write(path, own)
    return str(path)


def carried_reasoning(who, parent, row, started, prompt):
    """Whether the reasoning's thinking is in the context of what forks it: what the first request of the part above
    it read beyond the reasoning's own input, less that part's first message, against what the reasoning produced. Its
    thinking is the whole of its value (it writes nothing), and whether a fork carries a resumed session's thinking is
    the model API's behaviour, not the harness's: it is measured, not assumed."""
    first = next(iter(requests(row["sid"], started)), None)
    if not first or not parent.get("thought"):
        return None
    message = int(len(prompt.encode()) / base_pack.PACKED_RATIO[".md"])
    carried = max(0, first[0] - int(parent["context"]) - message)
    seen = dict(thought=parent["thought"], carried=carried, first_context=first[0])
    # the half is the estimate's tolerance (the message's size is estimated, and a carried block may be counted
    # differently from its output): a block carried whole reads about all of it, a dropped one about none
    if carried * 2 < parent["thought"]:
        text = (f"ATTENTION the {who} reference reasoning thought {parent['thought']:,} tokens, and the part forked "
                f"over it read {carried:,} of them: its thinking is not carried into its forks, so it costs a build "
                "and gives them nothing")
        say(text)
        v2.say_once(f"reasoning-carried-{who}", text, every=86400)
    else:
        say(f"reasoning {who}: carried into its forks ({carried:,} of {parent['thought']:,} tokens)")
    return seen


def load_part(who, description, parent, parent_snapshot):
    part = description["part"]
    packed = STATE / f"base-pack-{time.time_ns()}-{who}-{part}"
    env = dict(os.environ, ORCH_BASE_PART=part, ORCH_LOAD_LIST=str(list_path(who)))
    checked(sys.executable, "-B", HERE / "base_pack.py", "build", "--output", packed, env=env)
    checked(sys.executable, "-B", HERE / "base_pack.py", "verify", packed, env=env)
    prompt = checked(sys.executable, "-B", HERE / "base_pack.py", "bootstrap", packed, env=env)
    name = f"{who}-{part}-{time.time_ns()}"
    row, started = fork(parent, name, prompt)
    try:
        path = Path(v2.transcript(row["sid"]))
        checked(sys.executable, "-B", HERE / "base_pack.py", "check-load", packed, path, env=env)
        frozen = base_pack.sources_from_pack(packed)[0]
        expected = [(e["tier"], e["path"], e["level"]) for e in description["entries"]]
        if [(e["tier"], e["path"], e["level"]) for e in frozen] != expected:
            raise RuntimeError("The required material list changed while its part was loading.")
        actual_inputs = fingerprint([(e["tier"], e["path"], e["level"], e["text"]) for e in frozen])
        snap = STATE / f"{who}-{part}-{row['sid']}-snapshot.json"
        checked(sys.executable, "-B", HERE / "base_pack.py", "snapshot", packed, snap, env=env)
        snapshot = snapshot_union(parent_snapshot, snap, row["sid"])
        snap.unlink()  # the cumulative snapshot and the frozen pack retain this source boundary
        context = v2.context_of(row["sid"])
        if context <= 0:
            raise RuntimeError("The loaded context size is unavailable; its room cannot be checked.")
        cache_read(who, part, row, parent)
        touch(who, part, row["sid"])
        used(row["sid"])
        node = dict(part=part, kind="material", purposes=description["purposes"], sessionId=row["sid"], name=name,
                    model=parent["model"], effort=parent["effort"], flags=parent["flags"], parent=parent["sessionId"],
                    context=context, pack=str(packed), snapshot=snapshot, inputs=actual_inputs,
                    layout=description["layout"], sealed=time.strftime("%Y-%m-%dT%H:%M:%S"))
        if parent.get("kind") == "reasoning":
            node["over_reasoning"] = carried_reasoning(who, parent, row, started, prompt)
        return node
    finally:
        v2.claude("stop", row["id"])


def reasoning_prompt(who):
    return (HERE / "protocols/base-reasoning.md").read_text().replace("{WHO}", who) \
        .replace("{NAME}", f"{who}-reasoning").replace("{DONE}", DONE)


def reasoning_failed(who, parent, key, error):
    """Record a failed reasoning build; the same parent and prompt failing again counts on."""
    old = read(STATE / f"{who}-reasoning-failed.json")
    again = old.get("parent") == parent["sessionId"] and old.get("inputs") == key
    count = (old.get("count") or 1) + 1 if again else 1
    write(STATE / f"{who}-reasoning-failed.json",
          dict(parent=parent["sessionId"], inputs=key, at=time.time(), error=str(error), count=count))
    say(f"reasoning {who}: FAILED {error}; material parent retained")


def build_reasoning(who, parent, parent_snapshot):
    prompt = reasoning_prompt(who)
    key = fingerprint(prompt)
    old = read(record_path(who, "reasoning"))
    if old.get("parent") == parent["sessionId"] and old.get("inputs") == key and warm(who, "reasoning", old):
        return old
    row = None
    try:
        row, started = fork(parent, f"{who}-reasoning-{time.time_ns()}", prompt)
        import role_evidence
        records = list(role_evidence.own(v2.transcript(row["sid"]), started))
        calls = [b for r in records for b in (r.get("message", {}).get("content") or [])
                 if isinstance(b, dict) and b.get("type") == "tool_use"]
        import watchdog
        _, reply, replied = watchdog.last_reply(row["sid"])
        if calls or replied < started or reply.strip() != DONE:
            raise RuntimeError("Reasoning used a tool or did not return its own completion line.")
        context = v2.context_of(row["sid"])
        if context <= 0:
            raise RuntimeError("The reasoning context size is unavailable.")
        # its own requests' output is its thinking and its one line: what every fork of it carries, and what the
        # measured input of its own last request does not include
        thought = sum(out for _, out in requests(row["sid"], started))
        rec = dict(part="reasoning", kind="reasoning", purposes=["steering"], sessionId=row["sid"], name=row["name"],
                   model=parent["model"], effort=parent["effort"], flags=parent["flags"], parent=parent["sessionId"],
                   base=parent["sessionId"], context=context, thought=thought, snapshot=parent_snapshot, inputs=key,
                   sealed=time.strftime("%Y-%m-%dT%H:%M:%S"))
        cache_read(who, "reasoning", row, parent)
        write(record_path(who, "reasoning"), rec)
        touch(who, "reasoning", row["sid"])
        used(row["sid"])
        (STATE / f"{who}-reasoning-failed.json").unlink(missing_ok=True)
        return rec
    except (RuntimeError, OSError, ValueError, KeyError) as error:
        reasoning_failed(who, parent, key, error)
        return None
    finally:
        if row:
            v2.claude("stop", row["id"])
            # Once sealed this is a base entry, held by the base daemon rather than the task-session watchdog.
            with v2.state() as state:
                if (state["sessions"].get(row["name"]) or {}).get("role") == "base-reasoning":
                    state["sessions"].pop(row["name"])


def same_layout(rec, stable_layout):
    if rec.get("stable_layout") == stable_layout:
        return True
    try:
        return layout(base_pack.load(Path(rec["pack"]))["sources"]) == stable_layout
    except (OSError, ValueError, KeyError):
        return False


def reference(who, parts, force=False):
    """The stable reference the chain stands on, loaded again first when its entry is cold, its layout, prompt or model
    changed, or the list names another reference: (its record as the chain's root, the root before). Every fork takes
    its origin's model, so a reference built on another model than base-model would carry it to every session."""
    stable = next(p for p in parts if p["part"] == "stable")
    current = read(STATE / f"{who}-base.json")
    if not current:
        raise RuntimeError(f"Build and seal the {who} stable base first.")
    listed = subprocess.run([sys.executable, "-B", str(HERE / "manifest.py"), "stable-listed", who],
                            capture_output=True, text=True)
    prompt = hashlib.sha256(Path(os.environ.get("BASE_PROMPT_FILE") or HERE / "library-prompt.md").read_bytes()).hexdigest()
    model = os.environ.get("BASE_MODEL") or v2.base_model()  # what base.sh builds with
    pending_path = STATE / f"{who}-base-next.json"
    pending = read(pending_path)
    root = current
    if pending and same_layout(pending, stable["layout"]) and pending.get("prompt_sha256") == prompt \
            and pending.get("model") == model and time.time() - pending_path.stat().st_mtime < v2.WARM_MAX:
        root = pending
    elif force or listed.returncode or not same_layout(current, stable["layout"]) \
            or current.get("prompt_sha256") != prompt or current.get("model") != model or not warm(who, "stable", current):
        # `force`: a refresh from the stable part (watchdog.refresh_plan), its account having paid for the reload
        checked("sh", HERE / "base.sh", who, "restable", env=dict(os.environ, BASE_STACK_LOCKED="1"))
        root = read(pending_path)
        if not root:
            raise RuntimeError("Stable reload left no checked base.")
    return dict(root, part="stable", kind="material", purposes=["steering", "reading"],
                stable_layout=stable["layout"]), current


def acquire(who):
    """The lock of one build over a base's chain at a time — a refresh of its parts, or its delta's session — held by
    this process: a lock whose process is gone is stale. Raises when another holds it."""
    STATE.mkdir(parents=True, exist_ok=True)
    lock = STATE / f"{who}-layer.building"
    if lock.exists():
        with contextlib.suppress(ValueError, OSError):
            try:
                os.kill(int(lock.read_text()), 0)
            except ProcessLookupError:
                lock.unlink()
    try:
        fd = os.open(lock, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError:
        raise RuntimeError(f"A {who} base build already owns {lock}") from None
    os.write(fd, str(os.getpid()).encode())
    os.close(fd)
    return lock


def build(who, start=None):
    """Build the chain, or refresh it from the part `start` (the watchdog's refresh_plan): the parts under that part are
    kept as they loaded while they stand warm on the same parent, whatever changed in their sources since — the delta
    carries those changes until they have cost what loading them again costs."""
    if not v2.control():
        raise RuntimeError(v2.UNCONTROLLED)
    if (STATE / "no-launch").exists():
        raise RuntimeError("The launch hold is on; no base is built.")
    lock = acquire(who)
    published = list_path(who)
    candidate = STATE / f"{who}-load-next.txt"
    saved = {k: os.environ.get(k) for k in ("BASE_LOAD_LIST", "ORCH_LOAD_LIST")}
    try:
        write_text(candidate, published.read_text())
        os.environ["BASE_LOAD_LIST"] = os.environ["ORCH_LOAD_LIST"] = str(candidate)
        final = build_chain(who, start)
        # the chain is published: the list that describes it becomes the base's list
        write_text(published, candidate.read_text())
        return final
    finally:
        for k, v in saved.items():
            if v is None:
                os.environ.pop(k, None)
            else:
                os.environ[k] = v
        candidate.unlink(missing_ok=True)
        lock.unlink(missing_ok=True)


def build_chain(who, start=None):
    import select_base_load as select
    select.frontier(who)
    select.refresh_indexes(who)
    parts = spec(who)
    projection = select.projection(who)
    if projection["room_before_reasoning"] <= 0:
        raise RuntimeError("Required material leaves no working room. Revise its responsibilities; no tier was dropped.")
    root, current = reference(who, parts, force=start == "stable")
    root_snapshot = str(STATE / (f"{who}-manifest-next.json" if root["sessionId"] != current["sessionId"]
                                 else f"{who}-manifest.json"))
    persistent_root = STATE / f"layer-{root['sessionId']}-manifest.json"
    write(persistent_root, read(root_snapshot))
    root["snapshot"] = str(persistent_root)
    chain = [root]
    reason = build_reasoning(who, root, root["snapshot"])
    if reason:
        chain.append(reason)
    parent, snapshot = chain[-1], root["snapshot"]
    names = [p["part"] for p in parts if p["part"] != "stable"]
    under = names.index(start) if start in names else 0  # the parts under the one a refresh starts from
    for i, description in enumerate(p for p in parts if p["part"] != "stable"):
        old = read(record_path(who, description["part"]))
        if old.get("parent") == parent["sessionId"] and (i < under or old.get("inputs") == description["inputs"]) \
                and warm(who, description["part"], old) and Path(old.get("snapshot", "missing")).is_file() \
                and Path(old.get("pack", "missing"), "pack.json").is_file():
            node = old
        else:
            node = load_part(who, description, parent, snapshot)
            write(record_path(who, description["part"]), node)
        chain.append(node)
        parent, snapshot = node, node["snapshot"]
    if len([x for x in chain if x["kind"] == "material"]) < 2:
        raise RuntimeError("The list contains no material layer.")
    if parent.get("context", 0) >= v2.SOFT - v2.PROTOCOL_ROOM:
        raise RuntimeError("The measured prefix leaves no room for a task. It has not replaced the published chain.")
    # A single final record publishes the complete chain. Intermediate records are reusable build results only.
    above = next((p for p in chain if p.get("over_reasoning")), {})
    final = dict(parent, base=root["sessionId"], parts=chain,
                 reasoning_status="complete" if reason else "failed: parent fallback",
                 reasoning_carried=(above.get("over_reasoning") or {}).get("carried"))
    if root["sessionId"] != current["sessionId"]:
        write(STATE / f"{who}-base.json", {k: v for k, v in root.items() if k not in ("part", "kind", "purposes")})
        write(STATE / f"{who}-manifest.json", read(root_snapshot))
        (STATE / f"{who}-base-next.json").unlink(missing_ok=True)
        (STATE / f"{who}-manifest-next.json").unlink(missing_ok=True)
    aggregate = read(snapshot)
    held = {e["path"] for part in parts if part["part"] != "stable" for e in part["entries"]}
    aggregate["files"] = {k: v for k, v in aggregate.get("files", {}).items() if k in held}
    write(STATE / f"{who}-layer-manifest.json", aggregate)
    root_record = read(STATE / f"{who}-base.json")
    if root_record.get("sessionId") == root["sessionId"]:
        write(STATE / f"{who}-base.json", dict(root_record, stable_layout=root["stable_layout"]))
    write(STATE / f"{who}-layer.json", final)
    touch(who, "layer", parent["sessionId"])
    touch(who, "base", parent["sessionId"])
    mark(who, "base", "used").touch()
    say(f"stack {who}: sealed {len(chain)} parts at {parent.get('context')} tokens; {final['reasoning_status']}")
    with contextlib.suppress(Exception):  # what Claude Code put into the reference every fork holds (window_watch)
        import window_watch
        window_watch.audit_openings()
    # The caller of the real build ensures the daemon; isolated tests call build() without live supervision.
    return final


def held_layout(node):
    """A published part's layout: recorded at its load, or read back from its frozen pack."""
    if node.get("layout"):
        return node["layout"]
    try:
        return layout(base_pack.sources_from_pack(Path(node["pack"]))[0])
    except (OSError, ValueError, KeyError, TypeError):
        return None


def refresh_reason(who):
    """Why the chain must be built again now, or None: only a change of its structure — the list's parts or what they
    hold differ from the chain (an edit of the list, or a list and a chain that disagree), or the reference reasoning
    is absent or its prompt changed. A change of the held sources is the delta's, and a refresh for it is the
    watchdog's rule of what the delta has cost against what a refresh costs; nothing the task queue does is a reason."""
    chain = (v2.layer_record(who) or {}).get("parts")
    if not chain:
        return "the named material boundaries and reference reasoning have not been built"
    try:
        desired = [p for p in spec(who) if p["part"] != "stable"]
    except (OSError, ValueError) as error:
        # a required source of the list is gone, or the list's parts are malformed: a build would fail the same way,
        # every minute; the list is the owner's to mend
        v2.say_once(f"list-unreadable-{who}", f"ATTENTION the {who} load list cannot be built as it stands ({error}); "
                    "its chain stands as built", every=3600)
        return None
    built = [p for p in chain if p["kind"] == "material" and p["part"] != "stable"]
    if [p["part"] for p in desired] != [p["part"] for p in built]:
        return "the material boundaries changed"
    for want, have in zip(desired, built):
        if held_layout(have) not in (None, want["layout"]):
            return f"the list's {want['part']} part holds other entries than the chain loaded"
    key = fingerprint(reasoning_prompt(who))
    if any(p.get("part") == "reasoning" and p.get("inputs") == key for p in chain):
        return None
    failed = read(STATE / f"{who}-reasoning-failed.json")
    if failed.get("parent") == chain[0].get("sessionId") and failed.get("inputs") == key:
        if (failed.get("count") or 1) >= 2:
            # one automatic retry covers a passing cause (a start not confirmed, a timeout); a second failure over the
            # same reference and prompt has a cause a third attempt would meet again: it is the owner's to look at
            v2.say_once(f"reasoning-failed-{who}", f"ATTENTION the {who} reference reasoning failed twice over the same "
                        f"reference ({failed.get('error')}); its forks stand on the reference without it. base.sh {who} "
                        "layer tries it again", every=86400)
            return None
        if time.time() - failed.get("at", 0) < v2.RETRY:
            return None  # only automatic retries wait; the owner's build command may retry immediately
    return "the reference reasoning is absent or its prompt changed"


def suffix_costs(who):
    """[(part, written, read)] in tokens for each part a refresh may start from, lowest first — the stable part, then each
    named part —, or None with no chain recorded: a refresh from a part loads it and every part over it anew (written)
    over one read from cache of what stands under it (read). What stands under it keeps what it loaded, and the delta
    carries its changes: each part is consolidated on its own schedule, the parts ordered so that those modified least
    per token stand lowest (notes/plan-bases-two-purposes.md, "Dependency order and churn order made one")."""
    chain = (v2.layer_record(who) or {}).get("parts")
    if not chain:
        return None
    top = int(chain[-1].get("context") or 0)
    out = [("stable", top, 0)]
    for i, node in enumerate(chain):
        if i and node.get("kind") == "material" and node.get("part") != "stable":
            below = int(chain[i - 1].get("context") or 0)
            out.append((node["part"], top - below, below))
    return out


def ping(who, part):
    rec = record(who, part)
    if not rec or not warm(who, part, rec) or not worth_keeping(who, part, rec):
        return
    hit = STATE / "entry-hits" / rec["sessionId"]
    if not hit.exists():
        hit = mark(who, part)
    if time.time() - hit.stat().st_mtime < int(os.environ.get("ORCH_WARM_EVERY", 2400)):
        return
    row = None
    try:
        row, _ = fork(rec, f"warm-{who}-{part}-{time.time_ns()}", f"Keep-warm ping {time.time_ns()}. Use no tools. Reply WARM.")
        cache_read(who, "warm " + part, row, rec)
    finally:
        if row:
            v2.claude("stop", row["id"])
            v2.claude("rm", row["id"])


def drift(who):
    """Changes in each actual held projection, independently of what a newer list would select."""
    result = {}
    for node in (v2.layer_record(who) or {}).get("parts", []):
        if not node.get("pack"):
            continue
        try:
            sources = base_pack.sources_from_pack(Path(node["pack"]))[0]
            moved = total = 0
            missing = []
            for source in sources:
                path = source["path"]
                manifest.LEVELS[path] = source["level"]
                if not Path(path).is_file():
                    missing.append(path)
                    continue
                total += manifest.tokens(path)
                moved += manifest.moved_tokens(path, {path: source["source_sha1"]}, {path: source["text"]})
            result[node["part"]] = dict(moved=moved, tokens=total, missing=missing)
        except (OSError, ValueError, KeyError) as error:
            result[node["part"]] = dict(unknown=str(error))
    return result


# ---------------------------------------------------------------- the delta: texts, and sessions made on demand
# The owner, 2026-09-24 00:10, "yes do this": the delta's text is written on every change, as before, but a session
# holding it is made only when something is about to start from it — every message whose session nobody forked cost
# its 50-60K (the simulation of 09-21/22: 8 of 15). A text node is a file, its counts and a snapshot of what the base
# held when it was cut; the chain of them is what the churns, the judging roles' layers and the knowledge base take in,
# each in a message of its own. A session is made for the sessions that fork the base itself (v2.base_file), once what
# they lacked has paid for it (watchdog.deltas). Then, 00:15: "In general everything should be done lazy when its
# better", and "being eger on deterministic computation is fine": a cut is local and deterministic, and is made when a
# consumer takes the chain — fewer cuts leave fewer superseded forms for every holder to carry.

DELTA_ARG = int(os.environ.get("DELTA_ARG", 120_000))  # the most one message carries (Linux's argument is 128K)


def building(who):
    """Whether a build over the base's chain holds its lock now (acquire): its parts' refresh, or its delta's session."""
    lock = STATE / f"{who}-layer.building"
    try:
        os.kill(int(lock.read_text()), 0)
    except (OSError, ValueError):
        return False
    return True


@contextlib.contextmanager
def delta_lock(who):
    """The delta's record is read, changed and written by one process at a time: a cut beside a session's making."""
    import fcntl
    STATE.mkdir(parents=True, exist_ok=True)
    with open(STATE / f"{who}-delta.lock", "a") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        try:
            yield
        finally:
            fcntl.flock(f, fcntl.LOCK_UN)


def fail(text):
    """What a delta build refuses or fails at, said where the run is read (warm.log, timestamped) and to stderr, unless
    stderr is warm.log already (the watchdog's `2>> warm.log`), which would say it twice."""
    say(text)
    with contextlib.suppress(OSError):
        if os.path.realpath("/proc/self/fd/2") == os.path.realpath(STATE / "warm.log"):
            return
    print(text, file=sys.stderr)


def delta_log(who, **entry):
    """Every text cut and every session made, with the parts' changes it wrote (watchdog.carried_parts): a session over
    the layer writes every part's changes again, which loading the part again would spare."""
    with (STATE / f"{who}-delta-builds.jsonl").open("a") as log:
        log.write(json.dumps(dict(at=time.strftime("%Y-%m-%dT%H:%M:%S"), **entry)) + "\n")


def cut(who, whole=False, locked=False):
    """Cut what changed since the chain's last text into a text node of its own — an increment over the chain while
    the texts its nodes give each file are recorded (manifest.stack_held), else a whole text over the parts that begins
    a chain anew (`whole`: the chain consolidated, its superseded forms gone). No session: the node is its text, its
    counts and a snapshot of every held file as it holds them (layer-<node id>-manifest.json, what a holder of the
    chain to this node is told changed after). Returns the node, or None when nothing changed, no layer stands, or a
    build over the chain holds it (`locked`: the caller is that build)."""
    layer = v2.layer_record(who)
    if not layer or (not locked and building(who)):
        return None
    with delta_lock(who):
        d = v2.delta_record(who)
        held_path = STATE / f"{who}-delta-held.json"
        increment = bool(not whole and d and (d.get("stack") or d.get("sessionId"))
                         and read(held_path).get("top") == v2.chain_top(d))
        stamp, n = time.strftime("%Y%m%dT%H%M%S"), 1
        text = STATE / f"{who}-delta-{stamp}.md"
        while text.exists():
            n += 1
            text = STATE / f"{who}-delta-{stamp}-{n}.md"
        counts, held = text.with_suffix(".json"), text.with_name(text.stem + "-held.json")
        env = {k: v for k, v in os.environ.items() if k != "ORCH_BASE_PART"}
        env["ORCH_LOAD_LIST"] = str(list_path(who))
        try:
            if os.environ.get("BASE_DELTA_TEXT"):  # a text given (the tests; by hand): counted by its size
                text.write_text(Path(os.environ["BASE_DELTA_TEXT"]).read_text())
                size = int(len(text.read_text()) / 2.9)
                write(counts, {"layer_tokens": size, "stable_tokens": 0, "tokens": size})
                write(held, {"files": {}})
            else:
                with text.open("w") as out:
                    done = subprocess.run([sys.executable, "-B", str(HERE / "manifest.py"),
                                           "delta-increment" if increment else "delta", who, "--counts", str(counts),
                                           "--held", str(held)], stdout=out, stderr=subprocess.PIPE, text=True,
                                          env=env, cwd=PROJECT)
                if done.returncode:
                    raise RuntimeError(done.stderr.strip() or "manifest.py failed")
            if not text.read_text().strip():
                text.unlink()
                return None
            node_id = f"{who}-text-{text.stem[len(who) + 7:]}"
            snapshot = STATE / f"layer-{node_id}-manifest.json"
            checked(sys.executable, "-B", HERE / "manifest.py", "snapshot-delta", who, snapshot, env=env)
            own = read(counts)
            node = dict(id=node_id, text=str(text), digest=hashlib.sha256(text.read_bytes()).hexdigest()[:12],
                        tokens=int(own.get("tokens") or 0), superseded=int(own.get("superseded") or 0),
                        parts=own.get("parts") or {}, kind="increment" if increment else "delta",
                        sealed=time.strftime("%Y-%m-%dT%H:%M:%S"))
            if increment:
                # a record from before the texts has no stack: its one message is the chain's first node
                first = [dict(id=v2.chain_top(d), sessionId=d.get("sessionId"), text=d.get("text"),
                              digest=d.get("digest"), tokens=int(d.get("tokens") or 0), superseded=0, kind="delta",
                              sealed=d.get("sealed"))]
                rec = dict(d, stack=list(d.get("stack") or first) + [node])
                for key in ("tokens", "layer_tokens", "stable_tokens", "superseded"):
                    rec[key] = int(d.get(key) or 0) + int(own.get(key) or 0)
                parts = dict(d.get("parts") or {})
                for part, k in (own.get("parts") or {}).items():
                    parts[part] = parts.get(part, 0) + k
                rec["parts"] = parts
            else:
                # a chain begun anew holds no session: its first is made when a fork of the base has paid for it
                rec = dict(layer=layer["sessionId"], base=layer.get("base"), model=layer.get("model"),
                           effort=layer.get("effort"), flags=layer.get("flags"), stack=[node], superseded=0,
                           parts=own.get("parts") or {}, **{k: int(own.get(k) or 0)
                                                            for k in ("tokens", "layer_tokens", "stable_tokens")})
            head = subprocess.run(["git", "-C", str(PROJECT), "log", "-1", "--format=%h"], capture_output=True,
                                  text=True).stdout.strip()
            rec.update(top=node_id, digest=node["digest"], text=node["text"], head=head,
                       old_forms=own.get("old_forms") or rec.get("old_forms") or {})
            write(STATE / f"{who}-delta.json", rec)
            write(held_path, {"top": node_id, "files": read(held).get("files") or {}})  # the next text is measured here
            # and kept with the text: what a holder of the chain to it holds of each file it changed (v2.py read changes)
            write(STATE / f"layer-{node_id}-held.json", read(held_path))
            write(STATE / f"{who}-delta-pending.json", {"top": node_id, "tokens": 0, "at": time.time()})
            delta_log(who, kind="text-" + node["kind"], id=node_id, tokens=node["tokens"], parts=node["parts"])
            say(f"delta {who}: cut {'an increment' if increment else 'a whole text'} {node_id} of {node['tokens']:,} "
                "tokens")
            return node
        finally:
            counts.unlink(missing_ok=True)
            held.unlink(missing_ok=True)


def materialize(who, whole=False, over_layer=False):
    """Make the session the base's roles fork (v2.base_file): what changed is cut first (`whole`: the chain anew), then
    a fork of the session standing, when it holds a beginning of this chain and is warm (only the texts after it), else
    of the layer (the whole chain; `over_layer`: its entry was missed), holds the texts as its one message — HELD with
    the top text's digest, or loaded by chunks past DELTA_ARG. Recorded on the chain: its session, the nodes it holds
    (session_len) and what they carry. Returns the exit code base.sh's `delta` gave."""
    if not v2.control():
        fail(v2.UNCONTROLLED)
        return 3
    if (STATE / "no-launch").exists():
        fail(f"refused: the {who} delta's session is not made while the hold is on (state/no-launch)")
        return 3
    layer = v2.layer_record(who)
    if not layer:
        fail(f"no sealed {who} base with a layer to hold a delta over")
        return 1
    if v2.other_tools(dict(layer, sid=layer.get("sessionId"))):
        fail(f"refused: the {who} layer was started with other tools than session-flags gives now, so a delta over "
             "it would write its whole prefix again")
        return 3
    try:
        lock = acquire(who)
    except RuntimeError:
        print(f"a {who} layer or delta is being built", file=sys.stderr)
        return 3
    try:
        cut(who, whole=whole, locked=True)
        d = v2.delta_record(who)
        stack = (d or {}).get("stack") or ([d] if d and d.get("sessionId") else [])
        if not stack:
            print(f"nothing the {who} base holds has changed since its loads or its delta's last text: no delta")
            return 0
        held = v2.session_len(d) if v2.chain_session(who) else 0
        if held >= len(stack):
            print(f"the {who} delta's session holds its chain to its top")
            return 0
        if held and not over_layer and v2.warm(who):
            parent = dict(sessionId=d["sessionId"], model=d.get("model"), effort=d.get("effort"),
                          flags=d.get("flags"), context=d.get("context"), part="delta")
            kind = "session"
        else:
            parent, held, kind = dict(layer, part=layer.get("part") or "layer"), 0, "session-whole"
        nodes, top = stack[held:], stack[-1]
        text = "\n".join(Path(node["text"]).read_text(errors="ignore") for node in nodes)
        digest, name = top.get("digest"), f"{who}-delta-{time.strftime('%H%M%S')}"
        packed = None
        if len(text.encode()) <= DELTA_ARG:
            prompt = ("Hold the changes below to what you hold; do no work and run nothing. Reply with exactly HELD "
                      f"{digest} and end your turn.\n\n{text}")
        else:
            # above Linux's 128K argument it is packed and loaded by chunks, as a part is (check-load verifies it)
            stamp = time.strftime("%Y%m%dT%H%M%S")
            source, listed = STATE / f"{who}-delta-{stamp}-load.md", STATE / f"{who}-delta-{stamp}-load.list"
            source.write_text(text)
            listed.write_text(f"# === layer ===\n# the delta\n{source}\n")
            packed = STATE / f"base-pack-{stamp}-delta-{os.getpid()}"
            env = dict(os.environ, ORCH_LOAD_LIST=str(listed), ORCH_BASE_PART="layer")
            checked(sys.executable, "-B", HERE / "base_pack.py", "build", "--output", packed, env=env)
            prompt = checked(sys.executable, "-B", HERE / "base_pack.py", "bootstrap", packed, env=env)
        old = d.get("name") if d.get("sessionId") else None
        row, _ = fork(parent, name, prompt)
        try:
            path = v2.transcript(row["sid"])
            args = ("check-load", packed, path) if packed else ("held", path, digest)
            verdict = subprocess.run([sys.executable, "-B", str(HERE / "base_pack.py"), *map(str, args)], cwd=PROJECT,
                                     capture_output=True, text=True)
            if verdict.returncode:
                why = ((verdict.stderr or verdict.stdout).strip().splitlines() or ["no verdict"])[-1]
                say(f"delta {who}: not recorded, {why}")
                fail(f"the {who} delta was not held: {why}")
                return 3
            ctx = v2.context_of(row["sid"])
            cache_read(who, "delta", row, parent)
        finally:
            v2.claude("stop", row["id"])
        with contextlib.suppress(OSError):  # it holds the chain to its top: told what changed after that text
            write(STATE / f"layer-{row['sid']}-manifest.json", read(STATE / f"layer-{top['id']}-manifest.json"))
        with delta_lock(who):
            now = v2.delta_record(who) or {}
            chain = now.get("stack") or []
            ids = [v2.node_id(n) for n in chain]
            if not chain or ids[0] != v2.node_id(stack[0]) or v2.node_id(top) not in ids:
                fail(f"the {who} delta's chain was begun anew while its session was made; it is not recorded")
                return 3
            i = ids.index(v2.node_id(top))
            chain[i] = dict(chain[i], sessionId=row["sid"])
            holds = chain[:i + 1]
            parts = {}
            for node in holds:
                for part, k in (node.get("parts") or {}).items():
                    parts[part] = parts.get(part, 0) + k
            now.update(stack=chain, sessionId=row["sid"], name=name, context=ctx, session_len=i + 1,
                       session_base=ids[0], session_digest=digest, sealed=time.strftime("%Y-%m-%dT%H:%M:%S"),
                       session_tokens=sum(int(n.get("tokens") or 0) for n in holds),
                       session_superseded=sum(int(n.get("superseded") or 0) for n in holds), session_parts=parts,
                       session_old_forms=now.get("old_forms") or {})
            write(STATE / f"{who}-delta.json", now)
        written = {}
        for node in nodes:
            for part, k in (node.get("parts") or {}).items():
                written[part] = written.get(part, 0) + k
        delta_log(who, kind=kind, sessionId=row["sid"], tokens=sum(int(n.get("tokens") or 0) for n in nodes),
                  parts=written)
        if old:  # the session this replaces is stopped, never removed: a fork launched from it meanwhile finds it
            was = v2.row(old)
            if was:
                v2.claude("stop", was["id"])
        for mark_name in ("base.hit", "base.used", "layer.hit"):
            path = STATE / f"{who}-{mark_name}"
            path.touch()
            os.utime(path)
        (STATE / f"{who}-base.miss").unlink(missing_ok=True)
        touch(who, "delta", row["sid"])
        used(row["sid"])
        print(f"sealed the {who} delta {row['sid']} at {ctx} tokens, holding {i + 1} text(s) of its chain")
        return 0
    finally:
        lock.unlink(missing_ok=True)
        for leftover in STATE.glob(f"{who}-delta-*-load.*"):
            leftover.unlink(missing_ok=True)


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("command", choices=("build", "warm", "parts", "due", "worth", "delta"))
    parser.add_argument("who", choices=tuple(v2.BASES))
    parser.add_argument("part", nargs="?")
    parser.add_argument("--from", dest="start", help="build: refresh from this part, the parts under it kept")
    parser.add_argument("--text", action="store_true", help="delta: cut what changed into a text, no session")
    parser.add_argument("--whole", action="store_true", help="delta: the chain begun anew as one whole text")
    parser.add_argument("--over-layer", action="store_true", help="delta: the session made over the layer")
    parser.add_argument("--increment", action="store_true", help=argparse.SUPPRESS)  # what base.sh took: the default
    args = parser.parse_args()
    if args.command == "delta":
        try:
            if args.text:
                node = cut(args.who, whole=args.whole)
                print(f"cut {node['id']} ({node['tokens']:,} tokens)" if node else
                      f"nothing the {args.who} base holds has changed since its delta's last text, or a build holds it")
                return 0
            return materialize(args.who, whole=args.whole, over_layer=args.over_layer)
        except (OSError, ValueError, RuntimeError, KeyError) as error:
            fail(f"delta {args.who}: FAILED {error}")
            return 3
    try:
        if args.command == "build":
            print(json.dumps(build(args.who, args.start)))
            checked("sh", HERE / "warm_daemon.sh", "--ensure")
        elif args.command == "warm":
            ping(args.who, args.part)
        elif args.command == "worth":  # base.sh's pings of the stable reference: exit 0 while it is worth keeping
            node = (v2.layer_record(args.who) or {}).get("parts", [{}])[0] if args.part == "stable" \
                else record(args.who, args.part)
            return 0 if worth_keeping(args.who, args.part, node or {}) else 1
        elif args.command == "due":
            print(refresh_reason(args.who) or "")
        else:
            print(" ".join(p["part"] for p in (v2.layer_record(args.who) or {}).get("parts", []) if p["part"] != "stable"))
    except (OSError, ValueError, RuntimeError, KeyError) as error:
        say(f"stack {args.who}: FAILED {error}")
        print(str(error), file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
