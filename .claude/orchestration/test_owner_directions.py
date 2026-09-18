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


def claude_tool(command):
    return {"type": "assistant", "message": {"content": [{"type": "tool_use", "input": {"command": command}}]}}


def codex_user(ts, text):
    return {"type": "response_item", "timestamp": ts,
            "payload": {"type": "message", "role": "user", "content": [{"type": "input_text", "text": text}]}}


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
                (claude / (name + ".jsonl")).write_text("".join(json.dumps(r, separators=(",", ":")) + "\n" for r in records))
            for name, (source, records) in codex_sessions.items():
                meta = {"type": "session_meta", "payload": {"id": name, "cwd": "/project", "source": source}}
                (codex / f"rollout-2026-09-19T10-00-00-{name}.jsonl").write_text(
                    "".join(json.dumps(r, separators=(",", ":")) + "\n" for r in [meta] + records))
            with patch.object(e, "HERE", str(root / "here")), patch.object(e, "SESSIONS", str(claude)), \
                    patch.object(e, "CODEX_SESSIONS", str(root / "codex")), patch.object(e, "STATE", str(root / "state")), \
                    patch.object(e, "PROJECT", "/project"):
                e.uncurated()
            return (root / "state/owner-directions-new.md").read_text()

    def test_collects_new_words_and_leaves_out_old_launch_and_orchestration(self):
        text = self.run_collector(
            {"aaaa1111-dev": [claude_user("2026-09-18T19:00:00Z", "an old direction, already curated"),
                              claude_user("2026-09-19T08:00:00Z", "Keep admission and selection apart."),
                              claude_user("2026-09-19T08:01:00Z", "You are impl-9, a working copy forked from the base"),
                              claude_tool("python3 .claude/orchestration/base_pack.py emit /x 3"),
                              claude_tool("cat .claude/orchestration/owner-ledger.md")],
             "bbbb2222-orch": [claude_user("2026-09-19T09:00:00Z", "Make the base smaller."),
                               claude_tool("cat .claude/orchestration/base.sh")]},
            {"cccc3333": ("cli", [codex_user("2026-09-19T10:00:00Z", "Reuse the existing index notion.")]),
             "dddd4444": ("exec", [codex_user("2026-09-19T11:00:00Z", "You are the sole agent in one segment")]),
             "eeee5555": ("cli", [codex_user("2026-09-19T12:00:00Z", "Shave the loaded library."),
                                  {"type": "response_item", "payload": {"type": "custom_tool_call",
                                   "input": "exec_command({cmd:'cd .claude/orchestration && ls'})"}}])})
        self.assertIn("> Keep admission and selection apart.", text)
        self.assertIn("> Reuse the existing index notion.", text)
        self.assertLess(text.index("admission and selection"), text.index("existing index notion"))
        for absent in ("already curated", "You are impl-9", "Make the base smaller", "sole agent", "Shave the loaded"):
            self.assertNotIn(absent, text)

    def test_nothing_new_says_so(self):
        self.assertIn("None.", self.run_collector({}, {}))


if __name__ == "__main__":
    unittest.main()
