#!/usr/bin/env python3
"""What the run has shown of a role's sessions, for the role's reasoning layer (v2.role_layer_care).

    python3 -B role_evidence.py ROLE        writes state/role-evidence/ROLE.md and prints its path

Read from the transcripts, each session's own part (a fork's transcript begins with a copy of its origin's, which is
not its own): the last ROLE_EVIDENCE_SESSIONS sessions of the role that have ended — their requests, how many came
before their first change, their cost, the notes the harness gave them and what it refused them, most often first —
and the blocking findings of the last reviews that rejected the role's work (a reviewer's are the rejections it made
and what became of each). Everything here is a copy or a count of what the transcripts and the task records hold;
nothing is judged. The layer reasons over it (protocols/role-layer.md).
"""
import calendar
import collections
import json
import os
import re
import statistics
import sys
import time

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import v2  # noqa: E402

SESSIONS = int(os.environ.get("ORCH_ROLE_EVIDENCE_SESSIONS", 12))  # the role's last sessions measured
REVIEWS = int(os.environ.get("ORCH_ROLE_EVIDENCE_REVIEWS", 60))  # the last reviewer sessions read for rejections
FINDINGS = int(os.environ.get("ORCH_ROLE_EVIDENCE_FINDINGS", 10))  # the rejections given, latest first
FINDING_MAX = 1800  # characters of one rejection's findings
AHEAD = int(os.environ.get("ORCH_ROLE_EVIDENCE_AHEAD", 8))  # the tasks ahead named, with what their briefs name
AHEAD_MAX = 900  # characters of one task ahead
LATELY = 8  # the tasks its last sessions worked on, named
TOP = 8  # notes and refusals named
READ, WRITE, OUTPUT = 0.1, 2.0, 5.0
STAMP = re.compile(r'"timestamp":\s*"(\d{4}-\d\d-\d\dT\d\d:\d\d:\d\d)')
VERDICT = re.compile(r"v2\.py verdict\s+(\S+)\s+(accept|reject)\b(?:.*?--file\s+(\S+))?")
BLOCK = re.compile(r"^=== write (\S*(?:review|verdict)\S*\.md)\n(.*?)(?=^=== |^EOF\s*$|\Z)", re.M | re.S)


def all_sessions():
    """Every session the harness has recorded: the archive, then the state (which is newer)."""
    out = {}
    try:
        for line in open(os.path.join(v2.STATE, "v2-archive.jsonl"), errors="ignore"):
            try:
                s = json.loads(line).get("session")
            except ValueError:
                continue
            if s and s.get("name"):
                out[s["name"]] = s
    except OSError:
        pass
    out.update(v2.peek()["sessions"])
    return out


def transcripts():
    out = {}
    for d in v2.transcript_dirs():
        try:
            out.update({f[:-6]: os.path.join(d, f) for f in os.listdir(d) if f.endswith(".jsonl")})
        except OSError:
            pass
    return out


def own(path, started):
    """The session's own records of its transcript, in order."""
    try:
        lines = open(path, errors="ignore")
    except OSError:
        return
    for line in lines:
        m = STAMP.search(line)
        if not m or calendar.timegm(time.strptime(m.group(1), "%Y-%m-%dT%H:%M:%S")) < started - 5:
            continue
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if not r.get("isSidechain"):
            yield r


ROUTINE = re.compile(r"^(?:Since your last production|Production recorded|Message from |\[?Your reserve)")
# the counters every read and production is answered with, and mail: what the harness says every time, or what another
# session wrote, is not what it had to tell the role


HEREDOC_BODY = re.compile(r"<<-?\s*'?(\w+)'?\n.*?\n\1\b", re.S)
TOLD = re.compile(r"\[the sources, as this change leaves them|too: the same notion or fact|states, word for word|"
                  r"defines, its arguments aside|which this change took out of")  # what a change's reply tells


def call_ops(command):
    """The operations one call makes: its commands — split at `;`, `&&`, `||` and new lines, a heredoc's body aside, a
    pipe one command — and each block of a change. "Calls per request" read a call of four chained reads as one:
    the fixers of 09-22 made 1.03 calls a request and 4.2 operations."""
    command = str(command or "")
    blocks = len(re.findall(r"^=== (?:write|append|replace|replace-all|row|root) ", command, re.M))
    segs = [x for x in re.split(r";|&&|\|\||\n", HEREDOC_BODY.sub(" ", command))
            if x.strip() and not re.match(r"^\s*(set -u|cd \S+|[A-Za-z_]\w*=\S*|true)\s*$", x)]
    return max(1, len(segs) + max(0, blocks - 1))


def joinable(prev_calls, prev_result, next_calls):
    """Whether a request began where the protocol puts it in the one before: that one's only call a change whose reply
    said nothing to act on (not refused, no source check, no restatement), and this one's first call another change,
    the probe that tests it, or the hand-over — one call by the rule, a whole context read again each time they are
    two (95 of the fixers' 103 such requests on 09-22 had nothing in the first reply to wait for)."""
    if len(prev_calls) != 1 or not next_calls or not re.search(r"v2\.py change\b", prev_calls[0]):
        return False
    if str(prev_result or "").lstrip().startswith("refused") or TOLD.search(str(prev_result or "")):
        return False
    return bool(re.search(r"v2\.py change\b|probe_theories|v2\.py (result|finalize)\b", next_calls[0]))


def said(text):
    """A note or a refusal as a kind: its first sentence (a refusal's first reason where it opens with a list), numbers
    and quoted names made general."""
    text = str(text).strip()
    text = re.sub(r"^,?\s*and nothing (?:was|is) (?:changed|written):?\s*(?:-\s*)?", "", text)
    first = re.split(r"(?<=[.;])\s", " ".join(text.split()), maxsplit=1)[0][:240]
    return re.sub(r"`[^`]*`", "`…`", re.sub(r"\d[\d,.]*", "N", first))


def session_facts(s, path):
    """(requests, requests before the first change or None, cost, [notes], [refusals], [commands]) of a session."""
    reqs, order, first_change, notes, refused, commands = {}, [], None, [], [], []
    per, results = collections.OrderedDict(), {}
    for r in own(path, s.get("started") or 0):
        m = r.get("message") or {}
        content = m.get("content")
        if r.get("type") == "assistant" and isinstance(content, list):
            if m.get("model") == "<synthetic>":
                continue  # what Claude Code writes after a turn the harness ended: no request was made
            mid = m.get("id")
            if mid not in reqs:
                reqs[mid] = m.get("usage") or {}
                order.append(mid)
                per[mid] = []
            for b in content:
                if isinstance(b, dict) and b.get("type") == "tool_use":
                    cmd = str((b.get("input") or {}).get("command") or "")
                    commands.append(cmd)
                    per[mid].append((b.get("id"), cmd))
                    if first_change is None and re.search(r"v2\.py change\b", cmd):
                        first_change = order.index(mid)
        elif r.get("type") == "user" and isinstance(content, list):
            for b in content:
                if isinstance(b, dict) and b.get("type") == "tool_result":
                    body = b.get("content")
                    body = "\n".join(x.get("text", "") for x in body if isinstance(x, dict)) \
                        if isinstance(body, list) else str(body or "")
                    results[b.get("tool_use_id")] = body[:4000]
                    if body.lstrip().startswith("refused"):
                        refused.append(said(body.lstrip()[len("refused"):].lstrip(":, ") or body))
        elif r.get("type") == "attachment":
            a = r.get("attachment") or {}
            if a.get("type") == "hook_additional_context":
                notes += [said(c) for c in (a.get("content") or []) if str(c).strip() and not ROUTINE.match(str(c).strip())]
            elif a.get("type") == "hook_success" and '"deny"' in str(a.get("stdout") or ""):
                try:
                    out = json.loads(a["stdout"])["hookSpecificOutput"]
                    if out.get("permissionDecision") == "deny":
                        refused.append(said(out.get("permissionDecisionReason") or ""))
                except (ValueError, KeyError, TypeError):
                    pass
    cost = sum(u.get("cache_read_input_tokens", 0) * READ + u.get("cache_creation_input_tokens", 0) * WRITE
               + u.get("input_tokens", 0) + u.get("output_tokens", 0) * OUTPUT for u in reqs.values())
    batches = list(per.values())
    ops = sum(call_ops(c) for calls in batches for _, c in calls)
    joined = sum(1 for a, b in zip(batches, batches[1:])
                 if a and joinable([c for _, c in a], results.get(a[0][0]), [c for _, c in b]))
    return len(order), first_change, cost, notes, refused, commands, ops, joined


def producer_role(st, tid):
    t = st["tasks"].get(tid) or {}
    kind = t.get("kind") or ((v2.read_task(tid) or {}).get("metadata") or {}).get("kind") or "build"
    return v2.PRODUCER.get(kind)


def rejections(st, sessions, paths):
    """The rejections the last reviews made, latest first: (when, reviewer, task, the producing role, findings)."""
    reviewers = sorted((s for s in sessions.values() if s.get("role") == "reviewer" and s.get("sid") in paths),
                       key=lambda s: s.get("started") or 0)[-REVIEWS:]
    out = []
    for s in reviewers:
        commands = session_facts(s, paths[s["sid"]])[5]
        for cmd in commands:
            m = VERDICT.search(cmd)
            if not m or m.group(2) != "reject":
                continue
            rid, path = m.group(1), m.group(3)
            text = next((b.group(2) for b in BLOCK.finditer(cmd) if not path or b.group(1).endswith(path.split("/")[-1])),
                        None)
            source = "as it was given"
            if text is None and path:
                try:
                    text, source = open(os.path.join(v2.PROJECT, path), errors="ignore").read(), "as its file stands now"
                except OSError:
                    continue
                if not re.search(r"^\W*Verdict:\W*reject", text, re.M | re.I):
                    continue  # the file holds a later verdict now (its re-review's), not these findings
            findings = v2.part(text or "", "Findings")
            if not findings:
                continue
            tid = (st["tasks"].get(rid) or {}).get("reviews") or s.get("reviews") or rid
            out.append(dict(at=s.get("started") or 0, reviewer=s["name"], task=str(tid), role=producer_role(st, str(tid)),
                            findings=findings, source=source))
    return sorted(out, key=lambda x: -x["at"])


def task_kind(st, tid):
    t = st["tasks"].get(tid) or {}
    return t.get("kind") or v2.brief_kind((v2.read_task(tid) or {}).get("description") or "")


OPEN = (None, "ready", "running", "parked", "checking", "reviewing", "fixing", "committing")


def for_role(role, kind, stage):
    """Whether a task of this kind in this stage is, or soon will be, work of the role's sessions."""
    if stage not in OPEN:
        return False
    if role == "reviewer":
        return kind in ("build", "fix") and stage in (None, "ready", "running", "parked", "checking", "reviewing")
    if role == "fixer" and stage == "fixing":
        return True
    if role == "task-designer":
        return kind == "brief" and stage in (None, "ready", "running")
    return kind == {r: k for k, r in v2.PRODUCER.items()}.get(role) and stage in (None, "ready", "running", "parked")


def work_ahead(role, st):
    """(the text of the tasks the role's sessions will take next — the queue's order first, then those under way — each
    with what its brief says it delivers and the names it gives; their ids)."""
    order = list(dict.fromkeys(list(st.get("queue") or []) + sorted(st["tasks"], key=lambda x: int(x) if x.isdigit()
                                                                      else 0, reverse=True)))
    picked = []
    for tid in order:
        t = st["tasks"].get(tid) or {}
        task = v2.read_task(tid) or {}
        if not task or task.get("status") == "completed" or t.get("stage") in ("done", "deleted", "planner"):
            continue
        if for_role(role, task_kind(st, tid), t.get("stage")):
            picked.append((tid, t, task))
        if len(picked) >= AHEAD:
            break
    items = []
    for tid, t, task in picked:
        brief = task.get("description") or ""
        names = v2.names_in(v2.section(brief, "Inputs") + " " + v2.section(brief, "Decided"))
        text = (f"- task {tid} ({task_kind(st, tid)}, {t.get('stage') or 'queued'}): {task.get('subject', '')}\n"
                f"  Deliverable: {' '.join(v2.section(brief, 'Deliverable').split())}\n"
                + (f"  It names: {', '.join(f'`{n}`' for n in names)}" if names else ""))
        items.append(text if len(text) <= AHEAD_MAX else text[:AHEAD_MAX].rsplit(" ", 1)[0] + " …")
    return "\n".join(items), [tid for tid, _, _ in picked]


def lately(role, mine, st):
    """The tasks the role's last sessions worked on: their subjects and what they delivered."""
    out, seen = [], set()
    for s in reversed(mine):
        tid = str(s.get("task") or "")
        if not tid or tid in seen:
            continue
        seen.add(tid)
        task = v2.read_task(tid) or {}
        files = v2.deliverables(task.get("description") or "")
        out.append(f"- task {tid}: {task.get('subject', '(gone from the graph)')}"
                   + (f" — {', '.join(files[:6])}" if files else ""))
        if len(out) >= LATELY:
            break
    return "\n".join(out)


def median(xs):
    return statistics.median(xs) if xs else 0


def evidence(role):
    return evidence_and_ahead(role)[0]


def evidence_and_ahead(role):
    """(the evidence's text, the ids of the tasks ahead it names)."""
    st, sessions, paths = v2.peek(), all_sessions(), transcripts()
    # How the role's sessions worked — what they cost, what the harness noted and refused them — is evidence of the
    # harness and model they ran under: sessions of another base model than base-model's ran under the harness before
    # the run's fresh start, whose rules and costs have changed. The reviews' findings are of the library's content,
    # and hold whatever produced them.
    mine = sorted((s for s in sessions.values() if s.get("role") == role and s.get("sid") in paths
                   and (s.get("ended") or s.get("state") in ("done", "lost") or s.get("released"))
                   and s.get("model") == v2.base_model()),
                  key=lambda s: s.get("started") or 0)[-SESSIONS:]
    parts = []
    if mine:
        facts = [session_facts(s, paths[s["sid"]]) for s in mine]
        reqs = [f[0] for f in facts if f[0]]
        ops, joined = sum(f[6] for f in facts), sum(f[7] for f in facts)
        before = [f[1] for f in facts if f[1] is not None]
        costs = [f[2] for f in facts if f[0]]
        tasks = {str(s.get("task")) for s in mine if s.get("task")}
        rejected = sum(1 for t in tasks if (st["tasks"].get(t) or {}).get("rejections"))
        span = " – ".join(time.strftime("%m-%d %H:%M", time.localtime(mine[i].get("started") or 0)) for i in (0, -1))
        parts.append(
            f"### Measured: the last {len(mine)} sessions of the {role} ({span})\n"
            f"- requests: median {median(reqs):.0f} (from {min(reqs, default=0)} to {max(reqs, default=0)})"
            + (f"; before the first change: median {median(before):.0f} ({len(before)} of {len(mine)} made one)"
               if role != "reviewer" else "") + "\n"
            f"- cost: median {median(costs) / 1000:,.0f}K input-equivalent tokens (cache read 0.1, write 2, output 5)\n"
            f"- batching: {ops / max(sum(reqs), 1):.1f} operations a request; {joined} of {sum(reqs)} requests began where the "
            "protocol puts them in the request before (a change on a clean reply, then another change, its probe or the "
            "hand-over), each a whole context read again\n"
            + (f"- their tasks: {rejected} of {len(tasks)} rejected at least once by their review\n" if tasks and role
               in v2.PRODUCING else ""))
        for title, i in (("The harness's notes they were given most often", 3),
                         ("What the harness refused them most often", 4)):
            count, where = collections.Counter(), collections.defaultdict(set)
            for s, f in zip(mine, facts):
                for x in f[i]:
                    count[x] += 1
                    where[x].add(s["name"])
            if count:
                parts.append(f"### {title}\n" + "\n".join(
                    f"- {n} times in {len(where[x])} sessions ({', '.join(sorted(where[x])[:3])}"
                    f"{', …' if len(where[x]) > 3 else ''}): {x}" for x, n in count.most_common(TOP)))
            else:
                parts.append(f"### {title}\n(none)")
    else:
        parts.append(f"### Measured\nNo session of the {role} on {v2.api_model(v2.base_model())} has ended yet with a "
                     "transcript to read (the sessions before the run's fresh start ran under another model and harness).")
    found = rejections(st, sessions, paths)
    ours = [r for r in found if role == "reviewer" or r["role"] == role][:FINDINGS]
    title = ("The rejections reviews made lately, latest first, and what became of each task" if role == "reviewer"
             else f"The blocking findings of the reviews that rejected the {role}'s work lately, latest first")
    items = []
    for r in ours:
        t = st["tasks"].get(r["task"]) or {}
        fate = (f" — now {t.get('stage') or 'unrecorded'}, rejected {t.get('rejections', 0)} time(s)"
                if role == "reviewer" else "")
        text = r["findings"] if len(r["findings"]) <= FINDING_MAX else r["findings"][:FINDING_MAX].rsplit("\n", 1)[0] + " …"
        items.append(f"- task {r['task']} ({r['role'] or 'unknown role'}), by {r['reviewer']}, "
                     f"{time.strftime('%m-%d %H:%M', time.localtime(r['at']))}{fate}, {r['source']}:\n"
                     + "\n".join("  " + line for line in text.split("\n")))
    parts.append(f"### {title}\n" + ("\n".join(items) or "(none among the last reviews)"))
    ahead, ids = work_ahead(role, st)
    parts.append(f"### The work ahead: the tasks the {role}'s sessions will take next, as the graph holds them\n"
                 + (ahead or "(none in the graph now)"))
    done = lately(role, mine, st)
    if done:
        parts.append(f"### What the {role}'s last sessions worked on\n{done}")
    return "\n\n".join(parts), ids


def path_of(role):
    return os.path.join(v2.STATE, "role-evidence", f"{role}.md")


def main():
    if len(sys.argv) != 2 or sys.argv[1] not in v2.LAYERABLE:
        print(f"usage: role_evidence.py ROLE  (one of {', '.join(sorted(v2.LAYERABLE))})", file=sys.stderr)
        return 2
    role, began = sys.argv[1], time.time()
    try:
        text, ahead = evidence_and_ahead(role)
    except Exception as e:  # noqa: BLE001  said where the layer's build reads it, never a layer built on nothing
        v2.log(f"ATTENTION the {role}'s evidence could not be read ({e!r}); its reasoning layer is not built")
        return 1
    path = path_of(role)
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path + ".tmp", "w") as f:
        f.write(text + "\n")
    with open(path[:-3] + ".json.tmp", "w") as f:  # what the layer is built for, to know when it has moved on
        json.dump({"ahead": ahead}, f)
    os.replace(path[:-3] + ".json.tmp", path[:-3] + ".json")
    os.replace(path + ".tmp", path)
    v2.log(f"the {role}'s evidence is read ({len(text):,} characters, {time.time() - began:.0f} s)")
    print(path)
    return 0


if __name__ == "__main__":
    sys.exit(main())
