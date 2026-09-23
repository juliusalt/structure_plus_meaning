#!/usr/bin/env python3
"""A fake `claude` CLI for the simulation: sessions, forks, resumes and the prompt cache, with token counts computed
from the real text each session is given. Not the harness: the world it answers is the simulation's (FAKE_ROOT).

The cache model (documented behaviour of the API, as the harness itself describes it): each request writes an entry for
its whole prefix, which lives one TTL (3600 s, the harness writes 1-hour entries) past its last write or read. A request
reads the longest prefix whose entry is alive, looking back at most LOOKBACK content blocks from its own end; what it
does not read it writes. A fork's prefix is its origin's transcript, so its first request can read the origin's entry,
or, when that one is gone, an ancestor's within the lookback.

Every request of every session is logged to FAKE_ROOT/requests.jsonl (the pings' transcripts are deleted by base.sh).
"""
import json
import os
import re
import subprocess
import sys
import time

ROOT = os.environ["FAKE_ROOT"]
TTL = float(os.environ.get("SIM_TTL", 3600))
LOOKBACK = int(os.environ.get("SIM_LOOKBACK", 20))
CHARS = float(os.environ.get("SIM_CHARS_PER_TOKEN", 2.9))  # base.sh counts a delta text the same way
FRESH = int(os.environ.get("SIM_FRESH_TOKENS", 15_000))   # a new session's system prompt and tools
THINK_LAYER = int(os.environ.get("SIM_THINK_ROLE_LAYER", 15_000))  # assumed: no role layer has been built live
THINK_REFERENCE = int(os.environ.get("SIM_THINK_REFERENCE", 20_000))  # assumed: nor a reference reasoning
REPLY_AFTER = float(os.environ.get("SIM_REPLY_AFTER", 2.0))  # seconds from a call to each of its session's replies


def now():
    return time.time()  # the simulation's clock (sitecustomize)


def iso(t):
    return time.strftime("%Y-%m-%dT%H:%M:%S", time.gmtime(t)) + f".{int(t * 1000) % 1000:03d}Z"


def load(name, default):
    try:
        return json.load(open(os.path.join(ROOT, name)))
    except (OSError, ValueError):
        return default


def save(name, value):
    path = os.path.join(ROOT, name)
    tmp = path + f".tmp{os.getpid()}"
    json.dump(value, open(tmp, "w"))
    os.replace(tmp, path)


def tokens(text):
    return int(len(text) / CHARS) + 1


def transcripts():
    project = os.environ["ORCH_PROJECT"]
    return os.path.expanduser("~/.claude/projects/" + re.sub(r"[^A-Za-z0-9]", "-", project))


def transcript(sid):
    return os.path.join(transcripts(), f"{sid}.jsonl")


class World:
    """The fake's registry: sessions by sid ({name, parent, context, blocks, model, kind, head}), the cache entries
    ({sid: last touch}), the listing's rows."""

    def __init__(self):
        self.sessions = load("sessions.json", {})
        self.cache = load("cache.json", {})
        self.rows = load("agents.json", [])
        self.counter = load("counter.json", {"n": 0})

    def save(self):
        save("sessions.json", self.sessions)
        save("cache.json", self.cache)
        save("agents.json", self.rows)
        save("counter.json", self.counter)

    def new_sid(self):
        self.counter["n"] += 1
        n = self.counter["n"]
        return f"s{n:06d}-0000-4000-8000-{n:012d}", f"id{n}"

    def warm(self, sid, t):
        return sid in self.cache and t - self.cache[sid] < TTL

    def lookup(self, sid, t, extra_blocks=0):
        """(the context read from cache, the entry read) for a request whose prefix ends where session `sid` ends:
        its own entry if alive, else the nearest ancestor's within the lookback, else nothing."""
        blocks = extra_blocks
        s = sid
        while s:
            rec = self.sessions.get(s) or {}
            if self.warm(s, t) and blocks <= LOOKBACK:
                return rec.get("context", 0), s
            blocks += rec.get("own_blocks", 0)
            if blocks > LOOKBACK:
                return 0, None
            s = rec.get("parent")
        return 0, None

    def request(self, sid, context, t, output, prefix_sid=None, blocks=1):
        """One request of `sid` whose prefix (all but its last `blocks` blocks) is `prefix_sid`'s: the usage it has."""
        read, entry = self.lookup(prefix_sid or sid, t, extra_blocks=blocks)
        read = min(read, context)
        if entry:
            self.cache[entry] = t   # a read keeps the entry it read alive
        self.cache[sid] = t          # and the request writes its own
        return {"input_tokens": 1, "cache_read_input_tokens": read,
                "cache_creation_input_tokens": max(0, context - read - 1), "output_tokens": output}


def record_request(sid, name, kind, t, usage):
    with open(os.path.join(ROOT, "requests.jsonl"), "a") as f:
        f.write(json.dumps(dict(sid=sid, name=name, kind=kind, t=t, **usage)) + "\n")


def append(sid, records):
    with open(transcript(sid), "a") as f:
        for r in records:
            f.write(json.dumps(r) + "\n")


def copy_prefix(src, dst):
    """A fork's transcript begins with a copy of its origin's conversation, ids and timestamps kept. Tool results
    longer than 2,000 characters are copied cut: only the session that loaded them reads them back (base_pack's
    check-load), and a whole base in every fork's copy would be hundreds of megabytes a run."""
    with open(src) as f, open(dst, "w") as out:
        for line in f:
            if len(line) > 4000 and '"tool_result"' in line:
                d = json.loads(line)
                for block in (d.get("message") or {}).get("content") or []:
                    if isinstance(block, dict) and block.get("type") == "tool_result" \
                            and isinstance(block.get("content"), str) and len(block["content"]) > 2000:
                        block["content"] = block["content"][:200] + f" [... {len(block['content'])} characters]"
                line = json.dumps(d) + "\n"
            out.write(line)


def user(sid, t, content):
    return {"type": "user", "timestamp": iso(t), "sessionId": sid, "message": {"role": "user", "content": content}}


def assistant(sid, t, msg_id, model, content, usage):
    return {"type": "assistant", "timestamp": iso(t), "sessionId": sid,
            "message": {"id": msg_id, "model": model, "role": "assistant", "content": content, "usage": usage}}


def api_model(model):
    return re.sub(r"\[[^\]]*\]$", "", model or "claude-opus-5-5")


def kind_of(prompt):
    if prompt.startswith("Load the reference library"):
        return "load"
    if "Keep-warm ping" in prompt:
        return "ping"
    if "ROLE-LAYER READY" in prompt:
        return "role-layer"
    if "REFERENCE UNDERSTOOD" in prompt:
        return "reference"
    if "Answer from what you hold, briefly" in prompt:
        return "ask"
    if re.search(r"Reply with exactly HELD [0-9a-f]+", prompt):
        return "held"
    if "the knowledge base of the development" in prompt:
        return "kb"
    if re.sub(r"^\[harness\] ", "", prompt).startswith("Integrate "):  # notes, the delta's texts, or both (kb_care)
        return "kb"
    return "work"


def run_session(world, sid, name, prompt, t, model, parent):
    """Write a new session's own records after its (copied) prefix and answer as its kind answers. Returns the kind."""
    kind = kind_of(prompt)
    rec = world.sessions[sid]
    ctx = rec["context"]
    msg = 0
    out = []

    def req(content, add_tokens, output, blocks):
        nonlocal ctx, msg
        msg += 1
        ctx += add_tokens
        # a reply comes after the call that asked for it: the harness reads a reply as the session's only when it is
        # later than the start it recorded once the call returned (a reasoning's, a churn's, the knowledge base's)
        at = t + REPLY_AFTER * msg
        usage = world.request(sid, ctx, at, output, prefix_sid=parent if msg == 1 else sid, blocks=blocks)
        ctx += output
        record_request(sid, name, kind, at, usage)
        world.counter["msgs"] = world.counter.get("msgs", 0) + 1  # unique across resumes: a request is its id
        out.append(assistant(sid, at, f"msg_{sid[:7]}_{world.counter['msgs']}", model, content, usage))

    out.append(user(sid, t, prompt))
    path = transcript(sid)
    rec["own_from"] = os.path.getsize(path) if os.path.exists(path) else 0
    if kind == "load":
        m = re.search(r"For PART=1 through (\d+)", prompt)
        parts = int(m.group(1)) if m else 1
        command = prompt.strip().splitlines()[-1]
        pack_id = re.search(r"reply with exactly LOADED (\S+)", prompt).group(1)
        first = tokens(prompt)
        results = []
        for i in range(1, parts + 1):
            cmd = command.replace(" PART", f" {i}")
            text = subprocess.run(cmd, shell=True, capture_output=True, text=True).stdout
            results.append((f"toolu_{sid[:8]}_{i}", cmd, text))
        # the pack's own estimate of what it loads, by its measured ratios (base_pack): a load is counted as the
        # harness counts it, the rest of the world at CHARS
        ratio = None
        try:
            meta = json.load(open(os.path.join(command.split()[-2], "pack.json")))
            payload = meta.get("selected_loaded_token_estimate") or meta["variants"][-1]["loaded_token_estimate"]
            size = sum(c["bytes"] for c in meta["chunks"])
            ratio = max(1.0, size / max(1, payload - int(os.environ.get("SIM_PACK_OVERHEAD", 0))))
        except (OSError, ValueError, KeyError, IndexError, TypeError):
            pass
        count = (lambda x: int(len(x.encode()) / ratio) + 1) if ratio else tokens
        # one request calls every part (independent calls together), the next reads them all and says LOADED
        req([{"type": "tool_use", "id": tid, "name": "Bash", "input": {"command": cmd}} for tid, cmd, _ in results],
            first, 60 * parts, 1)
        out.append(user(sid, t, [{"type": "tool_result", "tool_use_id": tid, "content": text.rstrip("\n")}
                                 for tid, _, text in results]))
        req([{"type": "text", "text": f"LOADED {pack_id}"}], sum(count(x) for _, _, x in results), 40, 2)
        blocks = 4
    elif kind == "held":
        digest = re.search(r"Reply with exactly HELD ([0-9a-f]+)", prompt).group(1)
        req([{"type": "text", "text": f"HELD {digest}"}], tokens(prompt), 30, 1)
        blocks = 2
    elif kind == "role-layer":
        req([{"type": "text", "text": "ROLE-LAYER READY"}], tokens(prompt), THINK_LAYER, 1)
        blocks = 2
    elif kind == "reference":
        req([{"type": "text", "text": "REFERENCE UNDERSTOOD"}], tokens(prompt), THINK_REFERENCE, 1)
        blocks = 2
    elif kind == "ping":
        req([{"type": "text", "text": "WARM"}], tokens(prompt), 5, 1)
        blocks = 2
    elif kind == "ask":
        req([{"type": "text", "text": "Nothing to add."}], tokens(prompt), 50, 1)
        blocks = 2
    elif kind == "kb":
        project = os.environ["ORCH_PROJECT"]
        files = [os.path.join(project, "HANDOFF.md"), os.environ.get("ORCH_LEDGER") or "",
                 os.path.join(os.environ["ORCH_STATE_DIR"], "owner-directions-new.md")]
        texts = [open(p, errors="ignore").read() for p in files if p and os.path.exists(p)] \
            if not re.sub(r"^\[harness\] ", "", prompt).startswith("Integrate ") else []
        req([{"type": "tool_use", "id": f"toolu_{sid[:8]}_r", "name": "Bash", "input": {"command": "v2.py read"}}]
            if texts else [{"type": "text", "text": "INTEGRATED"}], tokens(prompt), 200, 1)
        if texts:
            out.append(user(sid, t, [{"type": "tool_result", "tool_use_id": f"toolu_{sid[:8]}_r",
                                      "content": "\n".join(texts)}]))
            req([{"type": "text", "text": "INTEGRATED"}], sum(tokens(x) for x in texts), 300, 2)
        blocks = 4 if texts else 2
    else:  # a work session: its first request; the simulation's driver writes the ones after it
        req([{"type": "text", "text": "Working."}], tokens(prompt), 200, 1)
        blocks = 2
    append(sid, out)
    rec.update(context=ctx, own_blocks=blocks, kind=kind, last=t + REPLY_AFTER * msg)
    return kind


def restamp(world, sid, t):
    """A session's own records stamped from `t` on (its replies REPLY_AFTER apart): its start is confirmed at `t`, and a
    reply stamped at its call could fall before the start its caller recorded once other sessions' ends had moved the
    clock meanwhile. Returns its last reply's time."""
    rec = world.sessions.get(sid) or {}
    path = transcript(sid)
    try:
        with open(path) as f:
            head = f.read(rec.get("own_from", 0))
            own = f.read().splitlines()
    except OSError:
        return rec.get("last") or t
    out, n, last = [], 0, t
    for line in own:
        d = json.loads(line)
        if d.get("type") == "assistant":
            n += 1
            last = t + REPLY_AFTER * n
            d["timestamp"] = iso(last)
        else:
            d["timestamp"] = iso(t + REPLY_AFTER * n)
        out.append(json.dumps(d))
    with open(path + ".tmp", "w") as f:
        f.write(head + "".join(line + "\n" for line in out))
    os.replace(path + ".tmp", path)
    rec["last"] = last
    return last


def moved_past(t):
    """The session took its time, and whoever waited for it sees it finished only after its last reply: the world's clock
    moves past that reply, beyond the five seconds a reader of a fork's own records allows before its start
    (role_evidence.own), so that whatever starts next is later than it."""
    path = os.environ.get("SIM_CLOCK")
    try:
        now = float(open(path).read().split()[0])
    except (OSError, ValueError, IndexError, TypeError):
        return
    if t + 6 > now:
        with open(path + ".tmp", "w") as f:
            f.write(repr(t + 6))
        os.replace(path + ".tmp", path)


def main():
    args = sys.argv[1:]
    world = World()
    with open(os.path.join(ROOT, "calls.jsonl"), "a") as f:
        f.write(json.dumps({"t": now(), "args": args[:-1] if "--bg" in args else args}) + "\n")
    if args[:2] == ["agents", "--json"]:
        # a session is seen started at once and finished only later: one started as a session of the harness's
        # (v2.launch: its settings are a worker's) is listed busy at the poll that confirms its start, so that the
        # start recorded is before its replies; the first poll that lists it finished moves the clock past them
        confirming = [r for r in world.rows if r.get("busy_polls", 0) > 0]  # a work session too, which stays busy
        finished = [r for r in world.rows if r.get("sim_kind", "work") != "work" and r.get("busy_polls", 0) <= 0]
        for r in finished + confirming:
            if r in confirming:
                # its start is confirmed now, and recorded by its caller just after: its replies come after that
                r["busy_polls"] -= 1
                r["status"], r["state"] = "busy", "working"
                r["last"] = restamp(world, r["sessionId"], now())
            else:
                r["status"], r["state"] = "idle", "done"
                if not r.get("seen_done"):
                    r["seen_done"] = True
                    moved_past(r.get("last") or 0)
        world.save()
        print(json.dumps([{k: v for k, v in r.items() if k not in ("busy_polls", "seen_done", "last", "sim_kind")}
                          for r in world.rows]))
        return 0
    if args[:1] == ["stop"]:
        world.rows = [r for r in world.rows if r["id"] != args[1]]
        world.save()
        return 0
    if args[:1] in (["rm"], ["attach"]):
        return 0
    if "--bg" not in args:
        print("unexpected: " + " ".join(args), file=sys.stderr)
        return 1
    t = now()
    prompt = args[-1]
    resume = args[args.index("--resume") + 1] if "--resume" in args else None
    model = api_model(args[args.index("--model") + 1]) if "--model" in args else \
        (world.sessions.get(resume) or {}).get("model") or "claude-opus-5-5"
    fork = "--fork-session" in args
    if resume and resume not in world.sessions:
        print(f"No conversation found with session ID: {resume}", file=sys.stderr)
        return 1
    os.makedirs(transcripts(), exist_ok=True)
    if resume and not fork:  # the session itself, continued
        sid = resume
        rec = world.sessions[sid]
        name = rec["name"]
        run_session(world, sid, name, prompt, t, model, parent=sid)
    else:
        sid, rid = world.new_sid()
        name = args[args.index("-n") + 1] if "-n" in args else sid
        parent = resume if fork else None
        head = subprocess.run(["git", "-C", os.environ["ORCH_PROJECT"], "rev-parse", "HEAD"], capture_output=True,
                              text=True).stdout.strip()
        world.sessions[sid] = dict(name=name, id=rid, parent=parent, model=model, started=t, head=head,
                                   context=world.sessions[parent]["context"] if parent else FRESH)
        if parent:
            copy_prefix(transcript(parent), transcript(sid))
        run_session(world, sid, name, prompt, t, model, parent=parent)
    kind = world.sessions[sid]["kind"]
    rid = world.sessions[sid]["id"]
    busy = kind == "work"
    settings = args[args.index("--settings") + 1] if "--settings" in args else ""
    launched = settings.endswith(("worker-settings.json", "planner-settings.json"))
    world.rows = [r for r in world.rows if r["name"] != name] + [
        dict(name=name, id=rid, sessionId=sid, kind="background", status="busy" if busy else "idle",
             state="working" if busy else "done", cwd=os.getcwd(), sim_kind=kind,
             busy_polls=1 if launched else 0, last=world.sessions[sid]["last"])]
    world.save()
    return 0


if __name__ == "__main__":
    sys.exit(main())
