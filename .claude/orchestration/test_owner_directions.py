"""The owner's directions given since the curated ones: what is collected and what is left out."""
import json
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch

sys.path.insert(0, str(Path(__file__).resolve().parent))
import extract_owner_directions as e


def claude_user(ts, text):
    return {"type": "user", "timestamp": ts, "message": {"role": "user", "content": text}}


def claude_queued(ts, text, kind="human"):
    """What the owner types while a session is working: Claude Code records it as a queued command."""
    return {"type": "attachment", "timestamp": ts, "attachment": {
        "type": "queued_command", "prompt": text, "commandMode": "prompt", "origin": {"kind": kind}}}


def claude_tool(command):
    return {"type": "assistant", "message": {"content": [{"type": "tool_use", "input": {"command": command}}]}}


def claude_read(path):
    return {"type": "assistant", "message": {"content": [{"type": "tool_use", "input": {"file_path": path}}]}}


def fork(name, load, *own):
    """A fork's transcript: its base's load, copied, then its own start and work."""
    return [claude_user("2026-09-18T21:59:00Z", load), *base_reads(load),
            claude_user("2026-09-19T08:00:00Z", f"You are {name}, a working copy forked from the loaded base."), *own]


def base_reads(load):
    if load.startswith("Load the reference library;"):
        return [claude_tool("/usr/bin/python3 .claude/orchestration/base_pack.py emit /pack 1")]
    return [claude_read("/project/.claude/orchestration/state/held/theory-names.md")]


PACKED = "Load the reference library; do no development work. For PART=1 through 76, run the command below."
FILES = "You are being loaded as the base from which live sessions are forked; you yourself never work."


def write(path, records):
    path.write_text("".join(json.dumps(r, separators=(",", ":")) + "\n" for r in records))


class NewDirectionsTests(unittest.TestCase):
    def run_collector(self, claude_sessions, codex_sessions):
        with tempfile.TemporaryDirectory() as temp:
            root = Path(temp)
            (root / "here").mkdir()
            (root / "here/owner-directions-selection.json").write_text(
                json.dumps({"reviewed_through": "2026-09-18T20:00:00Z"}))
            claude, codex = root / "claude", root / "codex/2026/09/19"
            claude.mkdir()
            codex.mkdir(parents=True)
            for name, records in claude_sessions.items():
                write(claude / (name + ".jsonl"), records)
            for name, (source, records) in codex_sessions.items():
                meta = {"type": "session_meta", "payload": {"id": name, "cwd": "/project", "source": source}}
                write(codex / f"rollout-2026-09-19T10-00-00-{name}.jsonl", [meta] + records)
            with patch.object(e, "HERE", str(root / "here")), patch.object(e, "SESSIONS", str(claude)), \
                    patch.object(e, "CODEX_SESSIONS", str(root / "codex")), patch.object(e, "STATE", str(root / "state")), \
                    patch.object(e, "PROJECT", "/project"):
                e.uncurated()
            return (root / "state/owner-directions-new.md").read_text()

    def test_collects_new_words_and_leaves_out_old_launch_and_orchestration(self):
        text = self.run_collector(
            {"aaaa1111-dev": fork("impl-9", PACKED,
                                  claude_tool("cat .claude/orchestration/owner-ledger.md"),
                                  claude_user("2026-09-19T08:01:00Z", "Keep admission and selection apart."),
                                  claude_user("2026-09-19T08:01:30Z", "ls"),   # a shell word typed in the wrong
                                  claude_user("2026-09-19T08:01:40Z", "a"),    # window, and a stray keystroke
                                  claude_tool("cat .claude/orchestration/state/v2.json"),
                                  claude_queued("2026-09-19T08:02:00Z", "A locus is not a payload."),
                                  claude_queued("2026-09-19T08:03:00Z", "a notification", kind="task")),
             "abab1212-old": [claude_user("2026-09-18T19:00:00Z", "an old direction, already curated")],
             "acac1313-planner": fork("plan-1", PACKED,
                                      claude_user("2026-09-19T08:40:00Z", "Order the selection before its uses."),
                                      claude_user("2026-09-19T08:41:00Z", "Message from implement-3 (2026-09-19T08:41:00):\n"
                                                  "Question on task 3"),
                                      claude_user("2026-09-19T08:42:00Z", "Stop hook feedback:\nMessage from the finalizer"),
                                      claude_tool("cat .claude/orchestration/state/v2.json")),
             "adad1414-worker": fork("implement-3", PACKED,
                                     claude_user("2026-09-19T08:50:00Z", "Stop hook feedback:\nYour turn ends only with your "
                                                 "result recorded"),
                                     claude_user("2026-09-19T08:51:00Z", "Your turn ended without a result recorded and "
                                                 "without a question pending."),
                                     claude_user("2026-09-19T08:52:00Z", "You were stopped by the account's usage limit, "
                                                 "which has now reset.")),
             "aeae1515-plan": fork("plan-3", PACKED,
                                   claude_user("2026-09-19T08:55:00Z", "Keep the graph small."),
                                   claude_user("2026-09-19T08:56:00Z", "[harness] Message from ask-q1: the answer")),
             "bbbb2222-orch": [claude_user("2026-09-19T09:00:00Z", "Make the base smaller."),
                               claude_tool("cat .claude/orchestration/base.sh"),
                               claude_queued("2026-09-19T09:01:00Z", "And leave this out of the ledger.")]},
            {"cccc3333": ("cli", [codex_user("2026-09-19T10:00:00Z", "Reuse the existing index notion.")]),
             "dddd4444": ("exec", [codex_user("2026-09-19T11:00:00Z", "You are the sole agent in one segment")]),
             "eeee5555": ("cli", [codex_user("2026-09-19T12:00:00Z", "Shave the loaded library."),
                                  {"type": "response_item", "payload": {"type": "custom_tool_call",
                                   "input": "exec_command({cmd:'cd .claude/orchestration && ls'})"}}])})
        for present in ("Keep admission and selection apart.", "A locus is not a payload.",
                        "Order the selection before its uses.", "Keep the graph small.",
                        "Reuse the existing index notion."):
            self.assertIn("> " + present, text)
        self.assertLess(text.index("admission and selection"), text.index("not a payload"))
        self.assertLess(text.index("not a payload"), text.index("existing index notion"))
        self.assertNotIn("> ls", text)      # not a direction: out of its session it decides nothing
        self.assertNotIn("> a\n", text)
        for absent in ("already curated", "You are impl-9", "Load the reference library", "a notification", "implement-3",
                       "plan-1", "Stop hook", "Your turn", "usage limit", "[harness]", "the answer", "Make the base smaller", "out of the ledger",
                       "sole agent", "Shave the loaded"):
            self.assertNotIn(absent, text)

    def test_nothing_new_says_so(self):
        self.assertIn("None.", self.run_collector({}, {}))


class SessionKindTests(unittest.TestCase):
    def kind(self, records):
        with tempfile.TemporaryDirectory() as temp:
            path = Path(temp) / "s.jsonl"
            write(path, records)
            return e.claude_session(str(path))[1]

    def test_a_forks_copied_load_is_not_its_own_work(self):
        for load in (PACKED, FILES):
            self.assertFalse(self.kind(fork("impl-4", load, claude_tool("cat HANDOFF.md"))))
            self.assertFalse(self.kind([claude_user("2026-09-18T21:59:00Z", load), *base_reads(load)]))  # a base

    def test_the_library_roles_work_on_the_library_whatever_they_look_up(self):
        for name in ("impl-24", "kb-1", "plan-3", "brief-4", "implement-5", "review-6",
                     "ask-q7", "design-8", "investigate-9", "fix-10"):
            self.assertFalse(self.kind(fork(name, PACKED, claude_tool("cat .claude/orchestration/state/v2.json"))))

    def test_a_session_that_works_on_the_orchestration_is_one(self):
        self.assertTrue(self.kind([claude_user("2026-09-19T09:00:00Z", "Review the orchestrator."),
                                   claude_tool("ls .claude/orchestration/")]))
        # a fork of the base that is not an implementer, set to orchestration work
        self.assertTrue(self.kind([claude_user("2026-09-18T21:59:00Z", PACKED), *base_reads(PACKED),
                                   claude_user("2026-09-19T09:00:00Z", "Measure what the base costs."),
                                   claude_tool("python3 .claude/orchestration/base_pack.py count /pack")]))

    def test_the_packed_bootstrap_is_a_base_load(self):
        import base_pack
        self.assertTrue(base_pack.BOOTSTRAP_PREFIX.startswith(e.BASE_LOADS))
        self.assertTrue(PACKED.startswith(base_pack.BOOTSTRAP_PREFIX))


def codex_user(ts, text):
    return {"type": "response_item", "timestamp": ts,
            "payload": {"type": "message", "role": "user", "content": [{"type": "input_text", "text": text}]}}


if __name__ == "__main__":
    unittest.main()
