"""The guards (work_meter.py guard, a PreToolUse hook) and what a worker reads and produces (recorded by the gauge's
PostToolUse call), run as the hooks run, in a throwaway world (fakes.py)."""
import inspect
import json
import os
import re
from pathlib import Path
import sys
import time
import unittest
from unittest.mock import patch

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fakes  # noqa: E402
from fakes import assistant  # noqa: E402
import work_meter  # noqa: E402

THEORY = "theory Ready imports Main begin\n\ndefinition ready :: bool where \"ready = True\"\n\nend\n"
LEMMA = "lemma ready_holds: \"ready\"\n  by (simp add: ready_def)\n\n"


class Guarded(unittest.TestCase):
    def setUp(self):
        self.w = fakes.World()
        self.transcript = str(self.w.transcripts / "s1.jsonl")
        self.records = []
        self.n = 0

    def tearDown(self):
        self.w.close()

    def hook(self, tool, inp, response=None, tool_use="t0"):
        return {"session_id": "s1", "tool_name": tool, "tool_input": inp, "tool_response": response,
                "cwd": str(self.w.project), "transcript_path": self.transcript, "tool_use_id": tool_use,
                "hook_event_name": "PostToolUse" if response is not None else "PreToolUse"}

    def guard(self, tool, inp, tool_use="t0"):
        """The guard's refusal reason, or None when the call may run."""
        _, out, err = self.w.hook("work_meter.py", "guard", self.hook(tool, inp, tool_use=tool_use))
        self.assertEqual(err, "")
        return out["hookSpecificOutput"]["permissionDecisionReason"] if out else None

    def requests(self, k, after=0.0):
        """k more requests in the transcript, after now plus `after` seconds."""
        base = time.time() + after
        for i in range(k):
            self.n += 1
            self.records.append(assistant(f"m{self.n}", fakes.iso(base + i * 0.01),
                                          [{"type": "tool_use", "id": f"t{self.n}", "name": "Bash", "input": {}}]))
        self.w.transcript("s1", self.records)


class PlannerGuardTests(Guarded):
    def setUp(self):
        super().setUp()
        self.w.session("plan-1", "planner", "s1", settings="planner-settings.json")

    def test_bodies_are_refused_and_statements_documents_and_listings_pass(self):
        refused = [("Read", {"file_path": str(self.w.project / "theories/Ready.thy")}),
                   ("Read", {"file_path": "tools/build.py"}),
                   ("Read", {"file_path": ".build/probe.log"}),
                   ("Read", {"file_path": ".build/tasks/3/Draft.thy"}),
                   ("Bash", {"command": "sed -n 1,80p theories/Ready.thy"}),
                   ("Bash", {"command": "cd theories && cat Ready.thy | head"}),
                   ("Bash", {"command": "grep -rn ready theories/"}),
                   ("Bash", {"command": "grep -rn ready"}),
                   ("Bash", {"command": "rg ready_def"}),
                   ("Bash", {"command": "git show HEAD"}),
                   ("Bash", {"command": "git diff HEAD~1 -- theories/Ready.thy"}),
                   ("Bash", {"command": "git log -p -3"}),
                   ("Bash", {"command": ".claude/orchestration/show.py ready_holds"}),
                   ("Bash", {"command": "tail -50 .build/tasks/3/finalize.log"}),
                   ("Grep", {"pattern": "ready"}),
                   ("Grep", {"pattern": "ready", "path": "theories"}),
                   ("Agent", {"prompt": "look"}), ("TaskOutput", {"task_id": "x"})]
        passed = [("Read", {"file_path": "HANDOFF.md"}),
                  ("Read", {"file_path": str(self.w.project / ".build/tasks/3/result.md")}),
                  ("Read", {"file_path": ".claude/orchestration/owner-ledger.md"}),
                  ("Bash", {"command": "cat .build/tasks/3/result.md"}),
                  ("Bash", {"command": "ls .build/tasks/ theories/ | grep -c Ready"}),
                  ("Bash", {"command": "find theories -name 'Native*.thy' | wc -l"}),
                  ("Bash", {"command": "git log --oneline -5 -- theories/Ready.thy"}),
                  ("Bash", {"command": "git show --stat HEAD"}),
                  ("Bash", {"command": "grep -n Readiness native_control_plan.md DECISIONS.md"}),
                  ("Bash", {"command": ".claude/orchestration/show.py --statement ready_holds"}),
                  ("Bash", {"command": ".claude/orchestration/show.py --statements Ready"}),
                  ("Bash", {"command": ".claude/orchestration/v2.py next 3"}),
                  ("Grep", {"pattern": "ready", "glob": "*.md"}),
                  ("Grep", {"pattern": "ready", "path": "HANDOFF.md"}),
                  ("Glob", {"pattern": "theories/*.thy"}),
                  ("TaskCreate", {"subject": "x"})]
        self.w.write("HANDOFF.md", "state\n")
        for tool, inp in refused:
            self.assertIsNotNone(self.guard(tool, inp), (tool, inp))
        for tool, inp in passed:
            self.assertIsNone(self.guard(tool, inp), (tool, inp))
        self.assertIn("reads statements, not details", self.guard("Read", {"file_path": "theories/Ready.thy"}))


class WorkerGuardTests(Guarded):
    def setUp(self):
        super().setUp()
        self.w.session("implement-1", "implementer", "s1", task="1")
        self.w.write(".build/tasks/1/brief.json", json.dumps(
            {"task": "1", "deliverables": ["theories/Ready.thy", "NOTES.md", "tool.py"], "drafts": ".build/tasks/1/",
             "inputs": ["theories/Base.thy", "Base.base_def"]}))
        self.thy = self.w.write("theories/Ready.thy", THEORY)
        self.w.write("NOTES.md", "notes\n")
        self.w.write("theories/Base.thy", "".join(f"line {i}\n" for i in range(1, 101)))
        self.w.write("theories/Other.thy", "".join(f"other {i}\n" for i in range(1, 2001)))
        self.record("Bash", {"command": "true"}, {"stdout": ""})  # the first call takes the baseline

    def record(self, tool, inp, response):
        code, out, err = self.w.hook("ctx_gauge.py", "gauge", self.hook(tool, inp, response))
        self.assertEqual((code, err), (0, ""))
        return out

    def meter(self):
        return json.loads((self.w.state / "work-s1.json").read_text())

    def sed(self, a, b, path="theories/Base.thy"):
        lines = (self.w.project / path).read_text().splitlines()[a - 1:b]
        return {"command": f"sed -n '{a},{b}p' {path}"}, {"stdout": "\n".join(lines) + "\n", "stderr": "", "interrupted": False}

    def produce(self, text=LEMMA):
        self.thy.write_text(THEORY.replace("\nend\n", "\n" + text + "end\n"))
        self.record("Edit", {"file_path": str(self.thy)}, {"filePath": str(self.thy)})

    def test_a_worker_may_not_wait_start_subagents_or_read_a_running_jobs_output(self):
        self.assertIn("starts no subagents", self.guard("Agent", {"prompt": "x"}))
        self.assertIn("Waiting is refused", self.guard("TaskOutput", {"task_id": "b1"}))
        self.assertIn("Waiting is refused", self.guard("Bash", {"command": "sleep 30"}))
        self.assertIn("Waiting is refused", self.guard("Bash", {"command": "tail -f .build/probe.log"}))
        self.assertIn("Waiting is refused", self.guard("Bash", {"command": "until [ -e x ]; do sleep 5; done"}))
        self.assertIsNone(self.guard("Bash", {"command": "sleep 1"}))
        job = "/tmp/claude-1000/x/tasks/b7x.output"
        self.w.transcript("s1", self.records)
        self.assertIn("still running", self.guard("Read", {"file_path": job}))
        self.records.append({"type": "user", "timestamp": fakes.iso(time.time()), "message": {"content":
                             "<task-notification><task-id>b7x</task-id><status>completed</status></task-notification>"}})
        self.w.transcript("s1", self.records)
        self.assertIsNone(self.guard("Read", {"file_path": job}))

    def test_rounds_since_production_are_limited_and_production_resets_them(self):
        self.requests(work_meter.ROUNDS - 1)
        self.assertIsNone(self.guard("Bash", {"command": "ls theories"}, tool_use="t-new"))  # this request makes ROUNDS
        self.requests(1)
        reason = self.guard("Bash", {"command": "ls theories"}, tool_use="t-new")
        self.assertIn(f"{work_meter.ROUNDS} requests and about 0K tokens of reading since your last production", reason)
        self.assertIsNone(self.guard("Bash", {"command": "ls"}, tool_use=f"t{self.n}"))  # recorded already: not twice
        self.assertIsNone(self.guard("Edit", {"file_path": str(self.thy)}, tool_use="t-new"))  # writing is never refused
        self.assertIsNone(self.guard("Bash", {"command": ".claude/orchestration/v2.py ask 1 x"}, tool_use="t-new"))
        self.assertIsNotNone(self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready"}, tool_use="t-new"))
        time.sleep(0.01)
        self.produce()
        self.assertIsNone(self.guard("Bash", {"command": "ls theories"}, tool_use="t-new"))

    def test_every_read_is_told_what_is_left_and_production_restarts_the_count(self):
        n = work_meter.ROUNDS
        self.requests(1)
        note = self.record("Bash", *self.sed(1, 10, "theories/Other.thy"))["hookSpecificOutput"]["additionalContext"]
        self.assertIn(f"Since your last production: 2 of {n} requests", note)
        self.assertIn(f"{n - 2} more request may read", note)
        self.requests(1)
        note = self.record("Bash", *self.sed(11, 20, "theories/Other.thy"))["hookSpecificOutput"]["additionalContext"]
        self.assertIn(f"{n} of {n} requests", note)
        self.assertIn("That was the last request that may read, search or check", note)
        time.sleep(0.01)
        self.thy.write_text(THEORY.replace("\nend\n", "\n" + LEMMA + "end\n"))
        note = self.record("Edit", {"file_path": str(self.thy)}, {})["hookSpecificOutput"]["additionalContext"]
        self.assertIn("Production recorded: the count restarts", note)

    def test_reading_is_limited_but_the_briefs_inputs_are_free_on_their_first_read(self):
        self.record("Bash", *self.sed(1, 100))  # an input
        self.assertEqual((self.meter()["read_tokens"], self.meter()["inputs_read"]), (0, ["theories/Base.thy"]))
        self.record("Bash", {"command": "sed -n '1,2000p' theories/Other.thy"}, {"stdout": "x" * 29_000})
        self.assertIsNone(self.guard("Bash", {"command": "ls"}, tool_use="t-new"))
        self.record("Bash", {"command": "sed -n '1,2000p' theories/Other.thy | cat"}, {"stdout": "x" * 29_000})
        self.assertGreater(self.meter()["read_tokens"], work_meter.READ_TOKENS)
        self.assertIn("tokens of reading since your last production", self.guard("Bash", {"command": "ls"}, tool_use="t-new"))
        self.produce()
        self.assertEqual(self.meter()["read_tokens"], 0)

    def test_production_is_content_in_a_deliverable(self):
        at = self.meter()["production_at"]
        self.thy.write_text(THEORY.replace("\n\nend", "\n(* a comment *)\n\nend"))  # a comment is no production
        self.record("Edit", {"file_path": str(self.thy)}, {})
        self.assertEqual(self.meter()["production_at"], at)
        self.w.write("Scratch.thy", THEORY + LEMMA)  # not a deliverable
        self.record("Write", {"file_path": "Scratch.thy"}, {})
        self.assertEqual(self.meter()["production_at"], at)
        self.w.write("NOTES.md", "notes\n" + "word " * 25)  # 25 words: not yet
        self.record("Edit", {"file_path": "NOTES.md"}, {})
        self.assertEqual(self.meter()["production_at"], at)
        self.w.write("NOTES.md", "notes\n" + "word " * 25 + " ".join(f"new{i}" for i in range(20)))  # 45 since
        self.record("Edit", {"file_path": "NOTES.md"}, {})
        at2 = self.meter()["production_at"]
        self.assertGreater(at2, at)
        self.w.write("tool.py", "# a comment\n\n" + "".join(f"x{i} = {i}\n" for i in range(5)))
        self.record("Write", {"file_path": "tool.py"}, {})
        at3 = self.meter()["production_at"]
        self.assertGreater(at3, at2)
        self.w.write(".build/tasks/1/Draft.thy", THEORY)  # a draft counts
        self.record("Write", {"file_path": ".build/tasks/1/Draft.thy"}, {})
        self.assertGreater(self.meter()["production_at"], at3)

    def test_a_read_of_lines_in_context_is_refused_until_the_file_changes(self):
        self.record("Bash", *self.sed(1, 60))
        self.assertIsNone(self.guard("Bash", self.sed(61, 80)[0]))
        self.assertIn("Lines 10-50 of theories/Base.thy are already in your context",
                      self.guard("Bash", self.sed(10, 50)[0]))
        self.assertIsNone(self.guard("Read", {"file_path": str(self.w.project / "theories/Base.thy"), "limit": 20}))
        with open(self.w.project / "theories/Base.thy", "a") as f:
            f.write("line 101\n")
        self.assertIsNone(self.guard("Bash", self.sed(10, 50)[0]))

    def test_the_same_failure_after_fixes_stops_checks_until_the_planner_answers(self):
        def check(failure):
            self.assertIsNone(self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready"}, tool_use=f"c{time.time()}"))
            self.record("Bash", {"command": "python3 tools/probe_theories.py Ready"},
                        {"stdout": f'*** {failure}\n*** At command "by" (line 7 of "{self.thy}")\n'})
        check("Failed to finish proof")
        for i in range(work_meter.CIRCLING):
            self.produce(LEMMA.replace("simp", f"auto{i}"))  # a fix
            check("Failed to finish proof")
        reason = self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready"}, tool_use="t-new")
        self.assertIn(f"came back {work_meter.CIRCLING} times after fixes", reason)
        time.sleep(0.01)
        self.w.set_st(asks={"q1": {"from": "implement-1", "text": "q", "asked": time.time(), "answered": time.time(),
                                   "state": "answered"}})
        self.assertIsNone(self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready"}, tool_use="t-new"))

    def test_failures_that_move_are_progress(self):
        for i in range(work_meter.CIRCLING + 2):
            self.produce(LEMMA.replace("simp", f"auto{i}"))
            self.record("Bash", {"command": "python3 tools/probe_theories.py Ready"},
                        {"stdout": f'*** Failed {i}\n*** At command "by" (line {7 + i} of "{self.thy}")\n'})
        self.assertIsNone(self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready"}, tool_use="t-new"))

    def test_a_quick_fix_has_its_own_budget(self):
        self.fix(time.time())
        self.requests(work_meter.ROUNDS + 1, after=0.01)
        self.assertIsNone(self.guard("Bash", {"command": "ls"}, tool_use="t-new"))  # the production limits do not apply
        self.requests(work_meter.FIX_ROUNDS - work_meter.ROUNDS - 1, after=0.02)
        self.assertIn(f"{work_meter.FIX_ROUNDS} rounds) is spent", self.guard("Bash", {"command": "ls"}, tool_use="t-new"))
        self.records = []
        self.requests(1, after=0.03)
        self.fix(time.time() - work_meter.FIX_MINUTES * 60 - 1)
        self.assertIn("budget", self.guard("Bash", {"command": "ls"}, tool_use="t-new"))
        self.assertIsNone(self.guard("Bash", {"command": ".claude/orchestration/v2.py result 1"}, tool_use="t-new"))
        self.assertIsNone(self.guard("Write", {"file_path": str(self.w.project / ".build/tasks/1/result.md")}, tool_use="t-new"))
        self.assertIsNotNone(self.guard("Edit", {"file_path": str(self.thy)}, tool_use="t-new"))

    def fix(self, since):
        st = self.w.st()
        st["sessions"]["implement-1"]["fix"] = {"since": since}
        (self.w.state / "v2.json").write_text(json.dumps(st))

    def test_a_session_without_a_role_is_not_guarded(self):
        self.w.set_st(sessions={})
        self.assertIsNone(self.guard("Agent", {"prompt": "x"}))


class RoleTests(Guarded):
    def test_the_graph_is_edited_only_by_the_planner(self):
        # the task designer held graph rights and wrote straight into the task list, which IS the graph. It proposes
        # now and the planner places (the owner, 2026-09-20), so it is refused here like every other role.
        self.w.session("design-2", "designer", "s1", task="2", settings="planner-settings.json")
        self.assertIn("The task graph is the planner's", self.guard("TaskCreate", {"subject": "x"}))
        self.w.set_st(sessions={})
        self.w.session("brief-2", "task-designer", "s1", task="2", settings="planner-settings.json")
        self.assertIn("propose", self.guard("TaskUpdate", {"taskId": "2"}))
        self.w.set_st(sessions={})
        self.w.session("implement-2", "implementer", "s1", task="2")  # its own session task list
        self.assertIsNone(self.guard("TaskCreate", {"subject": "step 1"}))

    def test_a_task_designer_and_a_consultation_of_the_knowledge_base_read_statements(self):
        self.w.session("brief-2", "task-designer", "s1", task="2", settings="planner-settings.json")
        self.assertIn("reads statements, not details", self.guard("Read", {"file_path": "theories/Ready.thy"}))
        self.w.set_st(sessions={})
        self.w.session("kb-1", "kb", "k1", state="done", live=False)
        self.w.session("ask-q1", "consultant", "s1", origin="kb-1", qid="q1")
        self.assertIn("reads statements, not details", self.guard("Bash", {"command": "cat theories/Ready.thy"}))
        self.w.set_st(sessions={})
        self.w.session("implement-5", "implementer", "i5", task="5", state="done", live=False)
        self.w.session("ask-q2", "consultant", "s1", origin="implement-5", qid="q2")
        self.assertIsNone(self.guard("Bash", {"command": "cat theories/Ready.thy"}))

    def test_what_counts_as_production_for_the_task_designer_the_reviewer_and_the_planner(self):
        def record(tool, inp):
            return self.w.hook("ctx_gauge.py", "gauge", self.hook(tool, inp, {"stdout": ""}))[1]
        meter = lambda: json.loads((self.w.state / "work-s1.json").read_text())
        self.w.session("brief-2", "task-designer", "s1", task="2", settings="planner-settings.json")
        record("Bash", {"command": "true"})
        record("TaskUpdate", {"taskId": "2", "description": "..."})
        self.assertEqual(meter()["productions"], 1)
        (self.w.state / "work-s1.json").unlink()
        self.w.set_st(sessions={})
        self.w.session("review-2", "reviewer", "s1", task="2")
        record("Bash", {"command": "true"})
        self.w.write(".build/tasks/2/review.md", "Verdict: accept\n## Summary\n" + "word " * 45)
        record("Write", {"file_path": ".build/tasks/2/review.md"})
        self.assertEqual(meter()["productions"], 1)
        (self.w.state / "work-s1.json").unlink()
        self.w.set_st(sessions={})
        self.w.session("plan-4", "planner", "s1", settings="planner-settings.json")
        record("Bash", {"command": "true"})
        self.w.write(".build/plans/plan-4/notes.md", " ".join(f"note{i}" for i in range(45)))
        record("Write", {"file_path": ".build/plans/plan-4/notes.md"})
        self.assertEqual(meter()["productions"], 1)

    def test_the_knowledge_base_is_not_metered(self):
        self.w.session("kb-1", "kb", "s1")
        self.assertIsNone(self.guard("Read", {"file_path": "HANDOFF.md"}))
        self.assertIsNotNone(self.guard("Read", {"file_path": "theories/Ready.thy"}))


class ProductionFilesTests(Guarded):
    """What a session's production is measured over: what it wrote, not what its runs left beside it."""

    def test_a_run_s_output_under_the_drafts_is_not_production(self):
        # one session's snapshot held 68,706 files and 6.0 GB, walked and copied again on every tool call
        for path in (".build/tasks/1/entry.md", ".build/tasks/1/Theory.thy", ".build/tasks/1/install.py",
                     ".build/tasks/1/probe3/probe.log", ".build/tasks/1/probe3/theories/P.thy",
                     ".build/tasks/1/replay/run/summary.json", ".build/tasks/1/check-a/recipes/x/receipt.json",
                     ".build/tasks/1/result.md"):
            self.w.write(path, "x")
        with patch.object(work_meter.v2, "PROJECT", str(self.w.project)):
            files = [os.path.relpath(f, str(self.w.project))
                     for f in work_meter.deliverable_files({"deliverables": [], "drafts": ".build/tasks/1/"})]
        self.assertEqual(sorted(files), [".build/tasks/1/Theory.thy", ".build/tasks/1/entry.md",
                                         ".build/tasks/1/install.py"])


class WriteTargetTests(Guarded):
    """What a command is taken to write: the record of who owns a working-tree change rests on it."""

    def targets(self, command):
        import work_meter
        return [os.path.relpath(p, str(self.w.project))
                for p in work_meter.write_targets("Bash", {"command": command}, command, str(self.w.project))]

    def test_a_quoted_pattern_and_a_heredoc_are_data_and_not_shell_syntax(self):
        # a read-only grep for conflict markers was refused as a write to the tree, and a draft under a task's own
        # directory was refused because its prose named ROOT (2026-09-20, reported by a session)
        markers = """grep -c '^<<<<<<<\\|^>>>>>>>\\|^=======$' DECISIONS.md && grep -n '^## ' DECISIONS.md"""
        self.assertEqual(work_meter.kind("Bash", {"command": markers}), "read")
        self.assertEqual(self.targets(markers), [])
        draft = ("mkdir -p .build/tasks/46 && cat > .build/tasks/46/X.thy <<'EOF'\n"
                 "text \\<open>its ROOT entry names the session\\<close>\nEOF")
        self.assertEqual(work_meter.kind("Bash", {"command": draft}), "write")
        self.assertEqual(self.targets(draft), [".build/tasks/46/X.thy", ".build/tasks/46"])

    def test_an_isabelle_cartouche_is_not_a_redirection(self):
        # every `\<open>` was read as a redirection and the word after it recorded as a file: 116 of the 123 entries
        # the tree's ownership held on 2026-09-20 were words of theory text that reached the parser this way
        theory = ("python3 - <<PY\nprint('x')\nPY\n"
                  "text \\<open>a row \\<exists>q. fBall A\\<close>")
        self.assertEqual(self.targets(theory), [])
        self.assertEqual(work_meter.redirections("lemma x: \\<open>The reading\\<close>"), [])
        # and a redirection beside one is still a redirection
        self.assertIn("theories/X.thy", self.targets("echo '\\<open>k\\<close>' > theories/X.thy"))

    def test_a_redirection_to_a_quoted_name_is_still_a_write(self):
        self.assertEqual(work_meter.kind("Bash", {"command": 'echo x > "a file.md"'}), "write")
        self.assertIn("a file.md", self.targets('echo x > "a file.md"'))

    def test_a_heredoc_s_prose_is_not_a_set_of_filenames(self):
        # the record held 319 entries, five of them paths, because every word ending a sentence has a dot in it
        self.w.write("DECISIONS.md", "# Decisions\n")
        command = ("python3 - <<'PY'\nfrom pathlib import Path\n"
                   "# a row of the library. a notion. the reading. those. it.\n"
                   "Path('DECISIONS.md').write_text('x')\nPY")
        self.assertEqual(self.targets(command), ["DECISIONS.md"])

    def test_a_redirection_and_a_file_command_name_paths_whatever_they_are_called(self):
        self.assertIn("ROOT", self.targets("echo x >> ROOT"))
        self.assertIn(".build/new.out", self.targets("true > .build/new.out"))
        self.assertIn("theories/Gone.thy", self.targets("rm theories/Gone.thy"))

    def test_a_new_file_of_a_known_kind_in_a_directory_that_exists_counts(self):
        self.assertIn(".build/tasks/1/result.md", self.targets("cp x .build/tasks/1/result.md"))
        self.assertEqual(self.targets("sed -i 's/^Recorded 2026-09-20\\.$/Recorded/' nowhere/at/all"), [])


class SharingTests(Guarded):
    def setUp(self):
        super().setUp()
        self.w.session("implement-2", "implementer", "s1", task="2")
        self.w.write(".build/tasks/1/finalize.json", json.dumps(
            {"check": "true", "files": ["theories/Ready.thy", "ROOT"], "message": "m"}))

    def test_a_finalization_in_flight_holds_the_working_tree_and_the_tree_is_given_back(self):
        # a review reads what was checked and writes nothing, so its files are free meanwhile: an append to a shared
        # record waited behind a whole check, review and commit until 2026-09-20
        self.w.set_st(tasks={"1": {"stage": "reviewing"}, "2": {"stage": "running", "session": "implement-2"}})
        self.assertIsNone(self.guard("Edit", {"file_path": str(self.w.project / "ROOT")}))
        # they are its own while it checks, while a quick fix repairs them, and while it commits
        for stage in ("committing", "fixing"):
            self.w.set_st(tasks={"1": {"stage": stage}, "2": {"stage": "running", "session": "implement-2"}})
            self.assertIn(f"ROOT belongs to task 1's finalization, which is {stage}",
                          self.guard("Edit", {"file_path": str(self.w.project / "ROOT")}))
        self.assertIsNone(self.guard("Edit", {"file_path": str(self.w.project / "theories/Elsewhere.thy")}))
        self.w.set_st(tasks={"1": {"stage": "checking"}, "2": {"stage": "running", "session": "implement-2"}})
        reason = self.guard("Edit", {"file_path": str(self.w.project / "theories/Other.thy")})
        self.assertIn("Task 1 holds the working tree (its finalization, checking", reason)
        self.assertIn("drafts under .build/tasks/2/", reason)
        self.assertIsNotNone(self.guard("Bash", {"command": "echo x >> ROOT"}))  # a shell write, any file
        self.assertIsNotNone(self.guard("Bash", {"command": "rm theories/Old.thy"}))
        self.assertIsNone(self.guard("Write", {"file_path": str(self.w.project / ".build/tasks/2/Other.thy")}))
        self.assertIsNone(self.guard("Read", {"file_path": str(self.w.project / "theories/Other.thy")}))  # reads are free
        self.assertEqual(self.w.st()["sessions"]["implement-2"]["tree_wait"], "1")
        self.w.set_st(tasks={"1": {"stage": "done"}, "2": {"stage": "running", "session": "implement-2"}})
        self.w.v2("dispatch")
        self.assertIn("it is yours", json.dumps(self.w.mail("implement-2")))  # busy: its hooks deliver it
        self.assertNotIn("tree_wait", self.w.st()["sessions"]["implement-2"])
        self.assertIsNone(self.guard("Edit", {"file_path": str(self.w.project / "theories/Other.thy")}))

    def test_a_session_with_nothing_left_but_the_tree_parks_and_the_slot_is_free(self):
        self.w.set_st(tasks={"1": {"stage": "checking"}, "2": {"stage": "running", "session": "implement-2"}})
        out = self.w.v2("park", "tree", env=self.w.as_session("s1"))
        self.assertIn("resumed here, your context intact, when task 1 has let the working tree go", out)
        self.assertEqual(self.w.st()["sessions"]["implement-2"]["state"], "parked")
        self.assertIsNone(self.w.hook("ctx_gauge.py", "stop", {"session_id": "s1", "hook_event_name": "Stop"})[1])
        self.assertIn("You are parked", self.guard("Read", {"file_path": str(self.w.project / "ROOT")}))

    def test_no_session_changes_the_index_or_the_history(self):
        for c in ("git add theories/X.thy", "git commit -m x", "git stash", "git checkout -- ROOT", "git -C . reset --hard",
                  "cd theories && git restore X.thy", "git push origin HEAD"):
            self.assertIn("only by the finalizer", self.guard("Bash", {"command": c}), c)
        for c in ("git status", "git diff HEAD -- ROOT", "git log --stat -3"):
            self.assertIsNone(self.guard("Bash", {"command": c}), c)

    def test_writes_to_the_working_tree_are_attributed_to_the_task(self):
        self.assertIsNone(self.guard("Edit", {"file_path": str(self.w.project / "theories/Other.thy")}))
        self.assertIsNone(self.guard("Write", {"file_path": str(self.w.project / ".build/tasks/2/draft.thy")}))
        owners = json.loads((self.w.state / "tree-owners.json").read_text())
        self.assertEqual(owners, {"theories/Other.thy": "2"})  # .build drafts are nobody's change of the tree

    def test_handoff_is_the_planners(self):
        self.assertIn("HANDOFF.md is the planner's state", self.guard("Write", {"file_path": "HANDOFF.md"}))

    def test_no_check_beside_a_measurement_either(self):
        # a run whose result is a timing holds the machine the same way a base-advancing check does
        (self.w.state / "isabelle-exclusive").write_text(json.dumps(
            {"task": "1", "why": "a measurement of the machinery's evaluation", "session": "implement-1",
             "at": time.time()}))
        reason = self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready"})
        self.assertIn("Task 1 holds the machine (a measurement of the machinery's evaluation)", reason)
        self.assertIn("Continue with what needs no check", reason)

    def test_no_check_beside_a_final_check_that_advances_the_base(self):
        (self.w.state / "isabelle-exclusive").write_text(f"1 {os.getpid()}")  # its check is running
        reason = self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready"})
        self.assertIn("Task 1 holds the machine (its final check advances the base heap)", reason)
        (self.w.state / "isabelle-exclusive").unlink()
        self.assertIsNone(self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready"}))


class RoundsTests(unittest.TestCase):
    def test_requests_are_counted_by_message_after_the_moment(self):
        with _World() as w:
            t = time.time()
            path = w.transcript("s", [assistant("a", fakes.iso(t - 5)), assistant("b", fakes.iso(t + 1)),
                                      assistant("b", fakes.iso(t + 1.1)), assistant("c", fakes.iso(t + 2),
                                      [{"type": "tool_use", "id": "tu-c", "name": "Read", "input": {}}])])
            since = fakes.iso(t)
            self.assertEqual(work_meter.rounds_since(path, since, "tu-c"), 2)  # b and c; c makes the call
            self.assertEqual(work_meter.rounds_since(path, since, "tu-d"), 3)  # the calling request not yet written
            self.assertEqual(work_meter.rounds_since(path, None), 0)


class HookWiringTests(unittest.TestCase):
    """Whether the guard runs at all. Every other test in this file calls it directly, which is past the matcher in
    the settings files that decides which tools reach it — so on 2026-09-20 Write, Edit, MultiEdit and NotebookEdit
    stood outside that matcher for the whole first live run, no write was guarded, the tree's ownership was built
    from the words of Bash commands alone, and every test here still passed."""

    def matcher(self, settings):
        hooks = json.load(open(HERE / settings))["hooks"]["PreToolUse"]
        wired = [h["matcher"] for h in hooks
                 if any("work_meter.py guard" in x.get("command", "") for x in h["hooks"])]
        self.assertEqual(len(wired), 1, f"{settings} wires work_meter.py guard {len(wired)} times, not once")
        return wired[0]

    def test_the_settings_let_every_guarded_tool_reach_the_guard(self):
        for settings in ("planner-settings.json", "worker-settings.json"):
            matcher = self.matcher(settings)
            for tool in work_meter.GUARDED_TOOLS:
                self.assertTrue(re.search(matcher, tool),
                                f"{tool} never reaches the guard in {settings}: the matcher is {matcher!r}, so the "
                                f"guard's refusals and records for it simply do not happen")

    def test_the_guarded_tools_are_the_ones_the_guard_itself_names(self):
        # a tool given a branch in kind() or in session_guard() and left out of GUARDED_TOOLS would be left out of
        # the matcher too, and nothing above would notice
        source = inspect.getsource(work_meter.kind) + inspect.getsource(work_meter.session_guard)
        named = {n for n in re.findall(r"""['"]([A-Z][A-Za-z]+)['"]""", source)}
        self.assertEqual(named, set(work_meter.GUARDED_TOOLS) | set(work_meter.UNGUARDED_TOOLS),
                         "the tools the guard names and the tools it declares it guards have drifted apart")


class _World:
    def __enter__(self):
        self.w = fakes.World()
        return self.w

    def __exit__(self, *exc):
        self.w.close()


if __name__ == "__main__":
    unittest.main()
