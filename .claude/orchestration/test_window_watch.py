"""The window as the gauge assumes it (the owner, 2026-09-23 evening): Claude Opus 5.5, auto-compact off, a ceiling of
977K and 30K to wrap up — and window_watch, which says when any of it stops holding."""
import datetime
import json
import os
from pathlib import Path
import re
import sys
import tempfile
import time
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import v2  # noqa: E402
import window_watch as ww  # noqa: E402


def iso(t):
    return datetime.datetime.fromtimestamp(t, datetime.timezone.utc).isoformat().replace("+00:00", "Z")


class SettingsTests(unittest.TestCase):
    def test_every_session_runs_without_auto_compact_on_the_base_model_to_the_owners_window(self):
        for name in ("base-settings.json", "worker-settings.json", "planner-settings.json"):
            settings = json.loads((HERE / name).read_text())
            self.assertIs(settings["autoCompactEnabled"], False, name)
            self.assertEqual(settings["env"]["DISABLE_AUTO_COMPACT"], "1", name)
        self.assertEqual(v2.base_model(), "claude-opus-5-5[1m]")
        self.assertEqual(v2.api_model(v2.base_model()), "claude-opus-5-5")
        self.assertIn('$(cat "$HERE/base-model")', (HERE / "base.sh").read_text())  # base.sh builds on the same one
        self.assertEqual((v2.CEILING, v2.SOFT, v2.HARD), (977_000, 947_000, 967_000))
        self.assertTrue(v2.SOFT < v2.HARD < v2.CEILING)


class WatchTests(unittest.TestCase):
    def setUp(self):
        self.temp = tempfile.TemporaryDirectory()
        self.root = Path(self.temp.name)
        self.state = self.root / "state"
        self.state.mkdir()
        self.now = time.time()
        self.sessions = {}
        self.said = []
        self.patches = [patch.object(v2, "STATE", str(self.state)),
                        patch.object(v2, "transcript", lambda sid: str(self.root / f"{sid}.jsonl")),
                        patch.object(v2, "peek", lambda: {"sessions": self.sessions}),
                        patch.object(v2, "log", lambda text: self.said.append(text))]
        for p in self.patches:
            p.start()
        ww.save({"since": self.now - 3600, "files": {}, "sessions": {}, "growths": [], "findings": []})

    def tearDown(self):
        for p in reversed(self.patches):
            p.stop()
        self.temp.cleanup()

    def session(self, name, sid, started=None):
        self.sessions[name] = dict(name=name, sid=sid, started=started or self.now - 600)

    def write(self, sid, *records):
        with open(self.root / f"{sid}.jsonl", "a") as f:
            for r in records:
                f.write(json.dumps(r, separators=(",", ":")) + "\n")  # as Claude Code writes them

    def request(self, context, at=None, stop="tool_use", model="claude-opus-5-5", version=v2.CLAUDE_CODE_LIMITS, out=500):
        at = at if at is not None else self.now - 60
        return {"type": "assistant", "timestamp": iso(at), "version": version,
                "message": {"id": f"m{context}-{at}", "model": model, "stop_reason": stop,
                            "usage": {"input_tokens": 10, "cache_read_input_tokens": context - 10,
                                      "cache_creation_input_tokens": 0, "output_tokens": out}}}

    def kinds(self):
        return sorted(f["kind"] for f in ww.load()["findings"])

    def test_a_session_within_its_window_says_nothing_and_its_figures_are_kept(self):
        self.session("implement-1", "s1")
        self.write("s1", self.request(900_000), self.request(920_000), self.request(940_000))
        ww.check()
        self.assertEqual(self.kinds(), [])
        self.assertEqual(self.said, [])
        mine = ww.load()["sessions"]["s1"]
        self.assertEqual((mine["peak"], mine["growth"], mine["past_notice"]), (940_000, 20_000, False))
        self.assertIn("largest request 940K", ww.summary()[0])

    def test_every_sign_that_the_window_no_longer_holds_is_said_once(self):
        self.session("implement-2", "s2")
        at = iso(self.now - 30)
        self.write("s2",
                   {"type": "system", "subtype": "compact_boundary", "timestamp": at, "content": "Conversation compacted"},
                   {"type": "assistant", "timestamp": at, "isApiErrorMessage": True,
                    "message": {"model": "<synthetic>", "content": [{"type": "text", "text": "Prompt is too long"}]}},
                   self.request(500_000, stop="model_context_window_exceeded"),
                   self.request(510_000, stop="refusal"),
                   self.request(950_000, stop="max_tokens"),
                   self.request(980_000),
                   self.request(600_000, model="claude-opus-5", version="2.1.290"),
                   self.request(640_000))
        ww.check()
        self.assertEqual(self.kinds(), sorted(["compacted", "refused", "window stop", "declined", "cut short",
                                               "over the ceiling", "margin outgrown", "another model",
                                               "another version", "step outgrown"]))
        said = len(self.said)
        self.assertTrue(all(text.startswith("ATTENTION window: implement-2 ") for text in self.said))
        self.write("s2", self.request(985_000), self.request(990_000, stop="refusal"))
        ww.check()
        self.assertEqual(len(self.said), said)  # once for each kind and session
        self.assertTrue(any("over the 977K ceiling" in line for line in ww.summary()))

    def test_a_wrap_up_that_nears_the_ceiling_is_said(self):
        self.session("review-3", "s3")
        self.write("s3", self.request(930_000), self.request(950_000))
        ww.check()
        self.assertEqual(self.kinds(), [])
        self.assertEqual(ww.load()["sessions"]["s3"]["after_notice"], 950_000)
        self.assertIn("the most any used of its margin 3K of 30K", ww.summary()[0])
        self.write("s3", self.request(968_000))
        ww.check()
        self.assertEqual(self.kinds(), ["margin outgrown"])

    def test_a_forks_copied_history_and_what_came_before_the_watch_are_not_its_own(self):
        self.session("design-4", "s4", started=self.now - 300)
        self.write("s4", self.request(990_000, at=self.now - 900, model="claude-opus-5"),  # its origin's, copied
                   self.request(995_000, at=self.now - 7200),                              # before the watch
                   self.request(620_000, at=self.now - 200))
        ww.check()
        self.assertEqual(self.kinds(), [])
        self.assertEqual(ww.load()["sessions"]["s4"]["peak"], 620_000)

    def test_a_base_load_grows_by_whole_chunks_and_that_is_no_step(self):
        (self.state / "high-layer.json").write_text(json.dumps(
            {"sessionId": "part-sid", "parts": [{"part": "stable", "sessionId": "stable-sid"},
                                                {"part": "catalogue", "sessionId": "part-sid", "kind": "material"}]}))
        self.write("part-sid", self.request(300_000), self.request(352_000), self.request(404_000))
        ww.check()
        self.assertEqual(self.kinds(), [])
        self.assertEqual(ww.load()["sessions"]["part-sid"]["peak"], 404_000)
        self.write("part-sid", self.request(990_000))
        ww.check()
        self.assertEqual(self.kinds(), ["over the ceiling"])  # what matters to any session still counts

    def test_only_what_was_added_since_is_read(self):
        self.session("fix-5", "s5")
        self.write("s5", self.request(700_000))
        ww.check()
        offset = ww.load()["files"][str(self.root / "s5.jsonl")]
        self.assertEqual(offset, os.path.getsize(self.root / "s5.jsonl"))
        with open(self.root / "s5.jsonl", "a") as f:
            f.write(json.dumps(self.request(720_000)) + "\n" + '{"type": "assistant", "timest')  # a line being written
        ww.check()
        mine = ww.load()["sessions"]["s5"]
        self.assertEqual((mine["peak"], mine["growth"]), (720_000, 20_000))
        self.assertLess(ww.load()["files"][str(self.root / "s5.jsonl")], os.path.getsize(self.root / "s5.jsonl"))

    def test_the_health_report_names_each_finding_of_the_day(self):
        self.session("implement-6", "s6")
        self.write("s6", self.request(600_000, model="claude-opus-5"))
        ww.check()
        lines = ww.summary()
        self.assertTrue(lines[0].startswith("window: Claude Code 2.1.280 on claude-opus-5-5, ceiling 977K"))
        self.assertTrue(re.search(r"ATTENTION window: implement-6 ran on claude-opus-5, not claude-opus-5-5", lines[1]))



class OpeningTests(WatchTests):
    """What Claude Code put into a stable base's opening context: read once for each, and said when it should not be."""

    def base(self, who, sid, *attachments):
        (self.state / f"{who}-base.json").write_text(json.dumps({"sessionId": sid, "name": f"{who}-base"}))
        at = iso(self.now - 60)
        self.write(sid, {"type": "user", "timestamp": at, "message": {"content": "Load the reference library"}},
                   *({"type": "attachment", "timestamp": at, "attachment": a} for a in attachments),
                   {"type": "assistant", "timestamp": at, "message": {"content": [{"type": "text", "text": "ok"}]}})

    def test_what_should_not_reach_a_base_is_said_and_a_clean_opening_is_not(self):
        snapshot = lambda *parts: {"type": "prompt_snapshot", "systemPrompt": list(parts)}
        self.base("high", "dirty",
                  {"type": "instructions", "files": [{"type": "AutoMem", "path": "/h/.claude/projects/p/memory/MEMORY.md"},
                                                     {"type": "Project", "path": "/repo/sub/CLAUDE.md"}]},
                  {"type": "session_context", "context": {"gitStatus": "Status:\n M .claude/orchestration/v2.py"}},
                  snapshot("# Harness", "# Memory\n\nYou have a persistent file-based memory",
                           "The following skills are available for use with the Skill tool"))
        self.base("max", "clean", {"type": "session_context", "context": {"userEmail": "e"}}, snapshot("# Harness"))
        # the memory's section of the system prompt alone, without its index as an instruction file
        self.base("xhigh", "section", snapshot("# Harness", "# Memory\n\nYou have a persistent file-based memory"))
        opened = []
        real = ww.opening
        with patch.object(ww, "opening", side_effect=lambda path: (opened.append(path), real(path))[1]):
            ww.audit_openings()
            self.assertEqual(len(opened), 3)
            ww.audit_openings()
            self.assertEqual(len(opened), 3)  # each base is read once
        self.assertEqual(self.kinds(), ["git status reached", "instructions reached", "memory reached", "memory reached",
                                        "skills reached"])
        self.assertTrue(any("/repo/sub/CLAUDE.md" in text for text in self.said))
        self.assertTrue(any(text.startswith("ATTENTION window: xhigh-base opened with Claude Code's memory (the memory "
                                            "section") for text in self.said))
        self.assertEqual(sorted(ww.load()["audited"]), ["clean", "dirty", "section"])

    def test_a_base_still_loading_is_read_again_once_its_opening_is_written(self):
        (self.state / "xhigh-base.json").write_text(json.dumps({"sessionId": "loading", "name": "xhigh-base"}))
        self.write("loading", {"type": "user", "timestamp": iso(self.now - 5), "message": {"content": "Load"}})
        ww.audit_openings()
        self.assertEqual(ww.load().get("audited"), [])
        self.write("loading", {"type": "attachment", "timestamp": iso(self.now - 4),
                               "attachment": {"type": "prompt_snapshot", "systemPrompt": ["# Harness"]}})
        ww.check()  # the watchdog's minute reads the openings too
        self.assertEqual(ww.load()["audited"], ["loading"])


class WiringTests(unittest.TestCase):
    def test_the_watchdog_reads_the_window_each_minute_and_the_health_report_shows_it(self):
        import contextlib
        import io
        import health
        import watchdog
        with tempfile.TemporaryDirectory() as temp:
            with patch.object(v2, "STATE", temp), patch.object(watchdog, "STATE", temp), \
                    patch.object(v2, "keep_pointer_links"), patch.object(v2, "peek", return_value={"active": True}), \
                    patch.object(v2, "dispatch"), patch.object(v2, "sample_occupancy"), \
                    patch.object(v2, "control", return_value=False), patch.object(ww, "check") as check:
                watchdog.main()
            check.assert_called_once()
            Path(temp, "stopped").write_text("2026-09-23T20:00:00")
            out = io.StringIO()
            with patch.object(v2, "STATE", temp), patch.object(health, "S", temp), \
                    patch.object(health, "bases_and_trees"), patch.object(health, "standing"), \
                    patch.object(v2, "peek", return_value={"active": True}), contextlib.redirect_stdout(out):
                health.main()
            self.assertIn("window: Claude Code 2.1.280 on claude-opus-5-5, ceiling 977K", out.getvalue())


if __name__ == "__main__":
    unittest.main()
