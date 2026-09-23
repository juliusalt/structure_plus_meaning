"""The guards (work_meter.py guard, a PreToolUse hook) and what a worker reads and produces (recorded by the gauge's
PostToolUse call), run as the hooks run, in a throwaway world (fakes.py)."""
import inspect
import json
import os
import re
from pathlib import Path
import shlex
import shutil
import subprocess
import sys
import time
import unittest
from unittest.mock import patch
import tempfile

HERE = Path(__file__).resolve().parent
sys.path.insert(0, str(HERE))
import fakes  # noqa: E402
from fakes import assistant  # noqa: E402
import work_meter  # noqa: E402

THEORY = "theory Ready imports Main begin\n\ndefinition ready :: bool where \"ready = True\"\n\nend\n"
LEMMA = "lemma ready_holds: \"ready\"\n  by (simp add: ready_def)\n\n"


# what the guard tells a session each removed tool's work goes to, as the hook prints it (JSON has no non-ASCII)
REMOVED_SAID = {tool: said.split(" — ")[0][:60] for tool, said in work_meter.REMOVED_TOOLS.items()}


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
        """The guard's refusal reason, or None when the call may run (as it is, or rewritten: `rewritten`)."""
        _, out, err = self.w.hook("work_meter.py", "guard", self.hook(tool, inp, tool_use=tool_use))
        self.assertEqual(err, "")
        self.asked = inp
        self.last = (out or {}).get("hookSpecificOutput") or {}
        return self.last.get("permissionDecisionReason") if self.last.get("permissionDecision") == "deny" else None

    def rewritten(self):
        """The input the last guarded call runs with, when the guard rewrote it — beyond the zsh option every command
        is run with (work_meter.globbing), which is not a rewrite of what the call does."""
        inp = self.last.get("updatedInput")
        if not inp or not str(inp.get("command", "")).startswith(work_meter.NONOMATCH):
            return inp
        inp = dict(inp, command=inp["command"][len(work_meter.NONOMATCH):])
        return None if inp["command"] == self.asked.get("command") else inp

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

    def test_what_a_change_writes_is_no_reading(self):
        # brief-141's draft said "show.py finds none" and its change was refused as a reading of details (2026-09-22)
        draft = fakes.change((".build/plans/plan-1/notes.md", "The entry names a function show.py finds none of.\n"))
        self.assertIsNone(self.guard("Bash", {"command": draft}))
        self.assertIn("reads statements, not details", self.guard("Bash", {"command": draft + "\n.claude/orchestration/show.py Base"}))

    def test_bodies_are_refused_and_statements_documents_and_listings_pass(self):
        refused = [("Bash", {"command": "cat " + str(self.w.project / "theories/Ready.thy")}),
                   ("Bash", {"command": "cat tools/build.py"}),
                   ("Bash", {"command": "cat .build/probe.log"}),
                   ("Bash", {"command": "cat .build/tasks/3/Draft.thy"}),
                   ("Read", {"file_path": "HANDOFF.md"}),  # no session's tool at all now
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
                   ("Grep", {"pattern": "ready", "glob": "*.md"}),  # no session's tool at all now
                   ("Glob", {"pattern": "theories/*.thy"}),
                   ("Agent", {"prompt": "look"}), ("TaskOutput", {"task_id": "x"})]
        passed = [("Bash", {"command": "cat HANDOFF.md"}),
                  ("Bash", {"command": "cat " + str(self.w.project / ".build/tasks/3/result.md")}),
                  ("Bash", {"command": "cat .claude/orchestration/owner-ledger.md"}),
                  ("Bash", {"command": "cat .build/tasks/3/result.md"}),
                  ("Bash", {"command": "ls .build/tasks/ theories/ | grep -c Ready"}),
                  ("Bash", {"command": "find theories -name 'Native*.thy' | wc -l"}),
                  ("Bash", {"command": "git log --oneline -5 -- theories/Ready.thy"}),
                  ("Bash", {"command": "git show --stat HEAD"}),
                  ("Bash", {"command": "grep -n Readiness native_control_plan.md DECISIONS.md"}),
                  ("Bash", {"command": ".claude/orchestration/show.py --statement ready_holds"}),
                  ("Bash", {"command": ".claude/orchestration/show.py --statements Ready"}),
                  ("Bash", {"command": ".claude/orchestration/v2.py next 3"}),
                  ("TaskCreate", {"subject": "x"})]
        self.w.write("HANDOFF.md", "state\n")
        for tool, inp in refused:
            self.assertIsNotNone(self.guard(tool, inp), (tool, inp))
        for tool, inp in passed:
            self.assertIsNone(self.guard(tool, inp), (tool, inp))
        self.assertIn("reads statements, not details", self.guard("Bash", {"command": "cat theories/Ready.thy"}))

    def test_a_statements_reader_reads_its_own_drafts_and_outputs_and_not_another_s(self):
        # a proposal or a graph edit it wrote and must correct, and what the harness kept of its own calls
        for path in (".build/plans/plan-1/edit.json", ".build/outputs/plan-1/commands/3.sh", ".build/outputs/plan-1/1.txt"):
            self.w.write(path, "x\n")
            self.assertIsNone(self.guard("Bash", {"command": f"cat {path}"}), path)
        self.w.write(".build/plans/plan-0/edit.json", "x\n")
        self.assertIn("reads statements, not details", self.guard("Bash", {"command": "cat .build/plans/plan-0/edit.json"}))
        # a planner's notes are statements, as everything it writes: brief-230 was refused the note plan-45 sent it
        self.w.write(".build/plans/plan-0/t230.md", "x\n")
        self.assertIsNone(self.guard("Bash", {"command": "cat .build/plans/plan-0/t230.md"}))
        # and so are a task's records and the base's pointer (plan-43, plan-44 were refused them, 2026-09-22)
        for path in (".build/tasks/7/finalized.json", ".build/tasks/7/finalize.json", ".build/tasks/7/brief.json",
                     ".build/tasks/base-lasting/active-context.json"):
            self.w.write(path, "{}\n")
            self.assertIsNone(self.guard("Bash", {"command": f"cat {path}"}), path)
        self.w.write(".build/tasks/7/check/incremental.json", "{}\n")                  # a check's own output is not one
        self.assertIn("reads statements, not details", self.guard("Bash", {"command": "cat .build/tasks/7/check/incremental.json"}))
        self.w.set_st(sessions={})
        self.w.session("brief-2", "task-designer", "s1", task="2", settings="planner-settings.json")
        self.w.write(".build/tasks/2/brief/proposal.json", "[]\n")
        self.assertIsNone(self.guard("Bash", {"command": "cat .build/tasks/2/brief/proposal.json"}))


class ReadTiersTests(Guarded):
    """Reading in two tiers, counted by the batch (the owner, 2026-09-21): a batch — one request, or one step's gather
    — is one read however many reads it holds; it reads at most BATCH bytes, and each read in it at most READ_BYTES,
    so that a large chunk is read deliberately, in pieces. ROUNDS reads a production allows, then a reserve of RESERVE
    that each production gives one back to. What the owner asked of it above all is that it counts right — a session
    starved of reading works blind — so every request here is made as a session makes it: written to the transcript,
    guarded, and recorded."""

    def setUp(self):
        super().setUp()
        # the tiers are measured against a read's bound: these fixtures are sized for 5,000 bytes, the bound until
        # 2026-09-22 15:17 (10,000 since), and what they test is the mechanism, not its value
        self.w.env["ORCH_READ_BYTES"] = "5000"
        for module in (work_meter, work_meter.v2):
            bound = patch.object(module, "READ_BYTES", 5000)
            bound.start()
            self.addCleanup(bound.stop)
        self.w.session("implement-1", "implementer", "s1", task="1")
        self.w.write(".build/tasks/1/brief.json", json.dumps(
            {"task": "1", "deliverables": ["theories/Ready.thy"], "drafts": ".build/tasks/1/",
             "inputs": ["theories/Base.thy:1-40"]}))
        self.thy = self.w.write("theories/Ready.thy", THEORY)
        self.w.write("theories/Base.thy", "".join(f"line {i}\n" for i in range(1, 101)))
        self.w.write("theories/Other.thy", "".join(f"other {i}\n" for i in range(1, 5001)))  # about 55K bytes
        self.lemmas, self.at = 0, 0
        self.call("Bash", {"command": "true"}, {"stdout": ""})  # the first call takes the baseline

    def call(self, tool, inp, response=None, *parallel):
        """One request as a session makes it: its calls written to the transcript, each guarded, each allowed one
        recorded. [(refusal or None, the note it was told)] — or the one pair of a request of one call."""
        self.n += 1
        calls = [(tool, inp, response)] + list(parallel)
        self.records.append(assistant(f"m{self.n}", fakes.iso(time.time()), [
            {"type": "tool_use", "id": f"m{self.n}-{i}", "name": t, "input": x} for i, (t, x, _) in enumerate(calls)]))
        self.w.transcript("s1", self.records)
        out = []
        for i, (t, x, r) in enumerate(calls):
            refused, note = self.guard(t, x, tool_use=f"m{self.n}-{i}"), None
            if refused is None:
                code, o, err = self.w.hook("ctx_gauge.py", "gauge", self.hook(
                    t, x, {"stdout": "ok"} if r is None else r, tool_use=f"m{self.n}-{i}"))
                self.assertEqual((code, err), (0, ""))
                note = ((o or {}).get("hookSpecificOutput") or {}).get("additionalContext")
            out.append((refused, note))
        time.sleep(0.005)
        return out[0] if len(out) == 1 else out

    def sed(self, lines=10):
        """A read of lines of Other.thy not yet read, as a call: (tool, input, response)."""
        a, self.at = self.at + 1, self.at + lines
        shown = "".join(f"other {i}\n" for i in range(a, self.at + 1))
        return ("Bash", {"command": f"sed -n '{a},{self.at}p' theories/Other.thy"},
                {"stdout": shown, "stderr": "", "interrupted": False})

    def read(self, lines=10):
        return self.call(*self.sed(lines))

    def produce(self):
        self.lemmas += 1
        self.thy.write_text(THEORY.replace("\nend\n", "\n" + LEMMA.replace("ready_holds", f"ready_{self.lemmas}")
                                           + "end\n"))
        return self.call("Bash", {"command": fakes.change(str(self.thy))}, {"filePath": str(self.thy)})[1]

    def meter(self):
        return json.loads((self.w.state / "work-s1.json").read_text())

    # the two tiers

    def test_the_first_tier_then_the_reserve_then_nothing(self):
        r, n = work_meter.ROUNDS, work_meter.RESERVE
        for i in range(1, r + 1):
            refused, note = self.read()
            self.assertIsNone(refused)
            self.assertIn(f"{i} of {r} reads", note)
        self.assertIn(f"The next {n} reads come from the reserve", note)
        for i in range(1, n + 1):
            refused, note = self.read()
            self.assertIsNone(refused, f"reserve read {i}")
            self.assertIn(f"{i} drawn from your reserve, which has {n - i} left of {n}", note)
        self.assertIn("That was your last read", note)
        refused, _ = self.read()
        self.assertIn(f"the {r} a production allows", refused)
        self.assertIn(f"the {n} your reserve held", refused)

    def test_a_slow_hook_says_where_its_time_went(self):
        # theory changes took a median 7.7 s with one heavy run going and 0.8 s with none (09-21/22); the parts timed
        # apart were fast on the repository, so the hooks and the session's commands say it when they are slow
        env = {"ORCH_SLOW": "0"}
        self.w.write("theories/Ready.thy", THEORY + LEMMA)
        self.records.append(assistant("mslow", fakes.iso(time.time()), [
            {"type": "tool_use", "id": "slow-1", "name": "Bash", "input": {"command": "true"}}]))
        self.w.transcript("s1", self.records)
        h = self.hook("Bash", {"command": "true"}, tool_use="slow-1")
        self.w.hook("work_meter.py", "guard", h, env=env)
        self.w.hook("ctx_gauge.py", "gauge", dict(h, tool_response={"stdout": ""}, hook_event_name="PostToolUse"), env=env)
        log = (self.w.state / "v2.log").read_text()
        self.assertRegex(log, r"slow: the guard of a Bash call of implement-1 took [\d.]+ s")
        self.assertRegex(log, r"slow: the gauge of a Bash call of implement-1 took [\d.]+ s")
        self.w.v2("status", env=dict(self.w.as_session("s1"), ORCH_SLOW="0"))
        self.assertRegex((self.w.state / "v2.log").read_text(), r"slow: `v2.py status` of implement-1 took [\d.]+ s")
        # and nothing is said of what is quick
        before = (self.w.state / "v2.log").read_text()
        self.w.hook("work_meter.py", "guard", h)
        self.w.v2("status", env=self.w.as_session("s1"))
        self.assertEqual((self.w.state / "v2.log").read_text().count("slow:"), before.count("slow:"))

    def test_a_read_s_guard_counts_whether_it_found_its_call(self):
        # a read's guard took a median 0.64 s against 0.10-0.16 s for any other call (09-22): the wait for its call's
        # line in the transcript, whose outcome nothing recorded
        before = self.meter().get("batch_lookups") or {"found": 0, "missed": 0}
        self.read()
        looked = self.meter()["batch_lookups"]
        self.assertEqual(looked["found"] + looked["missed"], before["found"] + before["missed"] + 1)
        self.assertGreaterEqual(looked["seconds"], 0)

    def test_a_production_restarts_the_first_tier_and_gives_one_back(self):
        for _ in range(work_meter.ROUNDS + 5):
            self.assertIsNone(self.read()[0])
        self.assertIn(f"your reserve holds {work_meter.RESERVE - 5 + 1} of {work_meter.RESERVE}", self.produce())
        self.assertEqual(self.meter()["reserve"], work_meter.RESERVE - 4)
        for i in range(1, work_meter.ROUNDS + 1):
            self.assertIn(f"{i} of {work_meter.ROUNDS} reads", self.read()[1])  # the first tier, whole again
        self.assertIn(f"1 drawn from your reserve, which has {work_meter.RESERVE - 5} left", self.read()[1])

    def test_the_reserve_never_grows_past_its_size(self):
        self.assertIn(f"holds {work_meter.RESERVE} of {work_meter.RESERVE}", self.produce())
        self.assertIn(f"holds {work_meter.RESERVE} of {work_meter.RESERVE}", self.produce())
        for _ in range(work_meter.ROUNDS + 1):
            self.read()
        self.assertIn(f"holds {work_meter.RESERVE} of {work_meter.RESERVE}", self.produce())  # 10 - 1 + 1

    def test_an_empty_reserve_comes_back_one_production_at_a_time(self):
        for _ in range(work_meter.ROUNDS + work_meter.RESERVE):
            self.assertIsNone(self.read()[0])
        self.assertIsNotNone(self.read()[0])
        self.assertIn(f"holds 1 of {work_meter.RESERVE}", self.produce())
        for _ in range(work_meter.ROUNDS + 1):
            self.assertIsNone(self.read()[0])
        self.assertIsNotNone(self.read()[0])

    def test_a_meter_written_under_a_larger_reserve_holds_no_more_than_the_setting(self):
        self.w.env["ORCH_READ_RESERVE"] = "2"
        for _ in range(work_meter.ROUNDS):
            self.read()
        self.assertIn("1 drawn from your reserve, which has 1 left of 2", self.read()[1])

    def check_script(self, sleep=0):
        """A fake probe: a failure early and another at its end, each with its location, a long output between, and
        a failing status."""
        failure = ('print("*** Failed to finish proof\\n*** At command \\"by\\" (line {n} of \\"/p/Ready.thy\\")", '
                   'flush=True)')
        lines = 'print("\\n".join(str(i) for i in range(1, 3001)), flush=True)'
        self.w.write("tools/probe_theories.py", "import sys, time\n" + failure.format(n=7) + f"\ntime.sleep({sleep})\n"
                     + lines + "\n" + failure.format(n=40) + "\nprint('the end')\nsys.exit(1)\n")

    def run_check(self, tool_use):
        check = {"command": "python3 tools/probe_theories.py Ready --timeout 60"}
        self.n += 1
        self.records.append(assistant(f"m{self.n}", fakes.iso(time.time()),
                                      [{"type": "tool_use", "id": tool_use, "name": "Bash", "input": check}]))
        self.w.transcript("s1", self.records)
        self.assertIsNone(self.guard("Bash", check, tool_use=tool_use))
        cmd = self.rewritten()["command"]
        self.assertEqual(work_meter.unwrapped(cmd), check["command"])
        run = subprocess.run(["bash", "-c", cmd], cwd=self.w.project, capture_output=True, text=True, timeout=60)
        return cmd, run

    def test_a_check_runs_to_its_end_and_ends_by_listing_every_error(self):
        # the owner, 2026-09-21: all the errors at once, dealt with at once, rather than one run for each
        self.check_script(sleep=1)
        cmd, run = self.run_check("c0")
        self.assertIn("check_errors.py", cmd)
        self.assertEqual(run.returncode, 1)                                    # its own status
        self.assertIn("the end", run.stdout)                                   # it went to its end
        self.assertIn("[this check reported 2 errors, listed here with where each stands. Fix them all", run.stdout)
        self.assertIn("- Ready.thy:7: Failed to finish proof\n- Ready.thy:40: Failed to finish proof\n", run.stdout)

    def test_a_check_shows_its_end_keeps_the_whole_and_is_judged_on_the_whole(self):
        # every output is bounded, a check's too (the owner, 2026-09-21): it shows its end, where its errors are
        # listed, and its whole is kept to be read on by its lines — reading on was running the check again
        self.check_script()
        cmd, run = self.run_check("c1")
        self.assertIn(f"cut.py {work_meter.READ_BYTES} tail", cmd)
        self.assertEqual(run.returncode, 1)                                    # still failing
        self.assertLessEqual(len(run.stdout.encode()), work_meter.READ_BYTES + 800)
        self.assertIn("- Ready.thy:7: Failed to finish proof", run.stdout)     # the first error, far before its end
        kept = work_meter.KEPT.search(run.stdout).group(1)
        self.assertTrue(kept.startswith(str(self.w.project / ".build/outputs/implement-1/")))
        whole = open(kept).read()
        self.assertIn("\n1\n2\n", "\n" + whole)                            # and the whole, kept
        _, out, _ = self.w.hook("ctx_gauge.py", "gauge", self.hook(
            "Bash", self.rewritten(), {"stdout": run.stdout, "stderr": ""}, tool_use="c1"))
        self.assertIn(f"1 of {work_meter.ROUNDS} reads", out["hookSpecificOutput"]["additionalContext"])
        self.assertEqual(self.meter()["last_check"]["path"], kept)             # judged on the whole
        st = dict(self.meter())
        work_meter.settle_check(st)
        self.assertEqual(st["prev_sig"], ["Ready.thy", "7", "Failed to finish proof"])
        # and read on by its lines, as a read of a file
        self.assertIsNone(self.call("Bash", {"command": f"sed -n '1,2p' {kept}"}, {"stdout": "x\n"})[0])

    def test_how_reads_are_counted_is_said_where_it_starts_to_bite(self):
        # said after every read, it was 2,850 notes in sixteen hours, 200 characters of each the same sentence the
        # protocol holds (2026-09-22)
        st, first = {"reserve": work_meter.RESERVE}, work_meter.ROUNDS
        why = "A read is one batch"
        self.assertNotIn(why, work_meter.countdown(st, 1))
        self.assertIn(f"1 of {first} reads", work_meter.countdown(st, 1))
        self.assertIn(why, work_meter.countdown(st, first + 1))              # the first read from the reserve
        self.assertNotIn(why, work_meter.countdown(st, first + 2))
        self.assertIn(why, work_meter.countdown(st, first + work_meter.RESERVE))  # and the last

    def test_every_command_runs_with_unmatched_globs_left_as_they_are(self):
        # zsh ended a whole command at a glob that matched nothing, however its errors were redirected: 65 calls of
        # 2026-09-22 in 41 sessions (design-218's `ls -d .build/*150712* … 2>/dev/null`)
        self.assertIsNone(self.guard("Bash", {"command": "ls -d .build/*nothing* 2>/dev/null; echo after"}))
        run = self.last["updatedInput"]["command"]
        self.assertTrue(run.startswith("setopt nonomatch 2>/dev/null; "))
        out = subprocess.run(["zsh", "-c", run], capture_output=True, text=True, cwd=self.w.project) \
            if shutil.which("zsh") else None
        if out is not None:
            self.assertIn("after", out.stdout)                                     # the rest of the command ran
        self.assertEqual(work_meter.unwrapped(run), "ls -d .build/*nothing* 2>/dev/null; echo after")

    def test_a_call_may_declare_how_much_it_wants_shown(self):
        # the owner, 2026-09-22: let the model declare the maximum it wants from each read — design-171 spent 6 of its 46
        # requests reading on outputs cut at 5K
        wide = {"command": "SHOW=20K sed -n '1,1000p' theories/Other.thy"}
        self.assertIsNone(self.guard("Bash", wide))
        self.assertIsNone(self.rewritten())                                         # shown whole: it fits its bound
        run = subprocess.run(["bash", "-c", "sed -n '1,1000p' theories/Other.thy"], cwd=self.w.project,
                             capture_output=True, text=True)
        self.assertGreater(len(run.stdout.encode()), work_meter.READ_BYTES)           # which the default would cut
        self.assertIsNone(self.guard("Bash", {"command": "sed -n '1,1000p' theories/Other.thy"}))
        self.assertIn(f"this read shows at most {work_meter.READ_BYTES:,} bytes", self.rewritten()["command"])
        self.assertIn("`SHOW=20K`", self.rewritten()["command"])                      # and says how to have more
        self.assertIsNone(self.guard("Bash", {"command": "SHOW=12K grep -n other theories/Other.thy"}))
        self.assertIn("cut.py 12000 head", self.rewritten()["command"])               # a command's output as well
        # declared at the head of a later command of the call: implement-130's `sed …; SHOW=12K sed …` was cut at the
        # default (2026-09-22 14:54)
        self.assertIsNone(self.guard("Bash", {"command": "grep -c other theories/Other.thy; SHOW=12K sed -n '1,1000p' "
                                                         "theories/Other.thy"}))
        self.assertIn("cut.py 12000 head", self.rewritten()["command"])
        self.assertIsNone(self.guard("Bash", {"command": "SHOW=90K grep -n other theories/Other.thy"}))
        self.assertIn(f"cut.py {work_meter.BATCH} head", self.rewritten()["command"])  # at most the batch's

    def test_a_batch_is_one_read_however_many_reads_it_holds(self):
        out = self.call(*self.sed(), self.sed(), ("Bash", {"command": "grep -c other theories/Other.thy"},
                                                  {"stdout": "x"}))
        self.assertTrue(all(refused is None for refused, _ in out))
        self.assertIn(f"1 of {work_meter.ROUNDS} reads", out[-1][1])
        self.read()
        self.assertIn(f"3 of {work_meter.ROUNDS} reads", self.read()[1])

    def test_a_read_of_any_source_is_a_read_like_any_other(self):
        # the gather was never refused and opened only after a production; a production restarts the tiers, so the
        # first read after one is always allowed, which is all the gather's rule gave (the owner, 2026-09-21)
        source = ("Bash", {"command": ".claude/orchestration/v2.py read theories/Base.thy Base.base"}, {"stdout": "g"})
        self.assertEqual(work_meter.kind("Bash", source[1]), "read")
        self.assertIsNone(self.guard("Bash", source[1], tool_use="v0"))
        self.assertIsNone(self.rewritten())  # it bounds itself: not sent through cut.py
        self.call(*source)
        self.assertIn(f"2 of {work_meter.ROUNDS} reads", self.read()[1])
        for _ in range(work_meter.ROUNDS - 2 + work_meter.RESERVE):
            self.read()
        self.assertIn("reads since your last production", self.call(*source)[0])  # both tiers spent: refused
        self.produce()
        self.assertIsNone(self.call(*source)[0])                                   # the first read after a production

    def test_the_harness_s_reading_commands_are_reads(self):
        # `v2.py proposal` printed every brief it was asked for at once and counted as nothing
        for c in ("v2.py proposal 2 a b", ".claude/orchestration/v2.py graph", "v2.py status"):
            self.assertEqual(work_meter.kind("Bash", {"command": c}), "read", c)
        self.assertEqual(work_meter.kind("Bash", {"command": "v2.py step 1 1 x"}), "own")  # a gather: its own batch
        self.assertIn(f"1 of {work_meter.ROUNDS} reads",
                      self.call("Bash", {"command": "v2.py graph"}, {"stdout": "the graph"})[1])
        self.guard("Bash", {"command": "v2.py proposal 2 a b"}, tool_use="p1")
        self.assertIn("cut.py", self.rewritten()["command"])

    def test_a_quick_fix_reads_by_its_own_budget_and_by_the_same_bounds(self):
        self.w.session("implement-1", "implementer", "s1", task="1", fix={"since": time.time()})
        self.w.env["ORCH_READ_RESERVE"] = "0"
        for _ in range(work_meter.ROUNDS + 2):  # past the tiers, within its own budget (FIX_ROUNDS): not refused
            self.assertIsNone(self.read()[0])
        self.assertIsNone(self.call("Bash", {"command": "sed -n '1,2000p' theories/Other.thy"})[0])
        self.assertIn("are not shown: this read shows at most", self.rewritten()["command"])  # cut where a read ends

    def test_what_does_not_read_is_not_counted(self):
        self.call("Bash", {"command": ".claude/orchestration/v2.py ask --to planner 'which?'"}, {"stdout": "asked"})
        self.call("Bash", {"command": "mkdir -p .build/tasks/1/drafts"}, {"stdout": ""})
        self.call("Bash", {"command": "cp theories/Base.thy .build/tasks/1/Base.thy"}, {"stdout": ""})
        self.call("Bash", {"command": fakes.change(str(self.w.project / ".build/tasks/1/note.md"))}, {})
        self.assertIn(f"1 of {work_meter.ROUNDS} reads", self.read()[1])

    def test_a_refused_read_takes_nothing_from_either_tier(self):
        self.read()
        again = {"command": "sed -n '1,10p' theories/Other.thy"}
        for _ in range(3):  # "already in your context", three times
            self.assertIn("already in your context", self.call("Bash", again)[0])
        self.assertIn(f"2 of {work_meter.ROUNDS} reads", self.read()[1])  # the refusals were not reads
        self.read()
        self.read()                      # one from the reserve
        self.read()                      # two
        for _ in range(4):
            self.assertIn("already in your context", self.call("Bash", again)[0])
        self.assertIn(f"holds {work_meter.RESERVE - 2 + 1} of", self.produce())  # two drawn, not six

    def test_an_again_call_counts_as_the_command_it_runs(self):
        self.read()                                                            # a read of lines 1-10
        self.assertIn("nothing else to show", self.call("Bash", {"command": ".claude/orchestration/v2.py again <<'EOF'"
                                                                            "\nEOF"})[0])  # as it was: all in context
        refused, note = self.call("Bash", {"command": ".claude/orchestration/v2.py again <<'EOF'\n<<<<<<< SEARCH\n"
                                                      "'1,10p'\n=======\n'11,20p'\n>>>>>>> REPLACE\nEOF"},
                                  {"stdout": "other 11\n"})
        self.assertIsNone(refused)
        self.assertIn(f"2 of {work_meter.ROUNDS} reads", note)                 # a read, though the call is the harness's
        self.at = 20
        self.assertIn(f"3 of {work_meter.ROUNDS} reads", self.read()[1])

    def test_a_filtered_read_is_one_read_and_one_wholly_in_context_is_none(self):
        self.read(20)                                                         # lines 1-20: the first read
        self.n += 1
        call = {"command": "sed -n '11,30p' theories/Other.thy"}
        self.records.append(assistant(f"m{self.n}", fakes.iso(time.time()),
                                      [{"type": "tool_use", "id": "f1", "name": "Bash", "input": call}]))
        self.w.transcript("s1", self.records)
        self.assertIsNone(self.guard("Bash", call, tool_use="f1"))
        run = subprocess.run(["bash", "-c", self.rewritten()["command"]], cwd=self.w.project, capture_output=True,
                             text=True).stdout
        self.assertIn("other 21\n", run)
        self.assertNotIn("other 20\n", run)
        # recorded as the rewritten call it ran as: still a read, and its lines are in context
        _, out, _ = self.w.hook("ctx_gauge.py", "gauge", self.hook(
            "Bash", self.rewritten(), {"stdout": run, "stderr": "", "interrupted": False}, tool_use="f1"))
        self.assertIn(f"2 of {work_meter.ROUNDS} reads", out["hookSpecificOutput"]["additionalContext"])
        self.assertIn("already in your context", self.call("Bash", {"command": "sed -n '5,25p' theories/Other.thy"})[0])
        self.at = 30
        self.assertIn(f"3 of {work_meter.ROUNDS} reads", self.read()[1])  # the read wholly in context was none

    def test_a_read_the_planner_is_refused_is_not_charged_either(self):
        # the statements-only guard refuses the planner a body before the limits are asked; that is a read not made
        self.w.session("plan-1", "planner", "s1", settings="planner-settings.json")
        self.w.set_st(sessions={"plan-1": self.w.st()["sessions"]["plan-1"]})  # s1 is the planner's alone now
        self.w.write("NOTES.md", "a document\n" * 30)
        self.assertIsNotNone(self.call("Bash", {"command": "cat " + str(self.thy)})[0])  # a proof body
        self.assertIn(f"1 of {work_meter.ROUNDS} reads",
                      self.call("Bash", {"command": "cat NOTES.md"}, {"stdout": "a document\n"})[1])

    # the bytes of a read and of a batch

    def test_a_read_of_a_file_longer_than_a_read_shows_shows_the_lines_that_fit_and_names_the_rest(self):
        # it was refused: of the ten refused on the night of 2026-09-21 six were within 12% of the bound, a request
        # spent each (implement-32's 5,013 bytes the least)
        other = str(self.w.project / "theories/Other.thy")
        fits = work_meter.fitting(other, 1)
        self.assertLessEqual(work_meter.read_size(other, 1, fits), work_meter.READ_BYTES)
        self.assertGreater(work_meter.read_size(other, 1, fits + 1), work_meter.READ_BYTES)
        refused, _ = self.call("Bash", {"command": "sed -n '1,1000p' theories/Other.thy"})
        self.assertIsNone(refused)
        run = subprocess.run(["bash", "-c", self.rewritten()["command"]], cwd=self.w.project, capture_output=True,
                             text=True).stdout
        self.assertIn(f"other {fits}\n", run)
        self.assertNotIn(f"other {fits + 1}\n", run)                                  # the bound holds
        self.assertIn(f"[lines {fits + 1}-1000 of theories/Other.thy are not shown: this read shows at most "
                      f"{work_meter.READ_BYTES:,} bytes", run)
        second = min(work_meter.fitting(other, fits + 1), 1000)
        self.assertIn(f"`sed -n '{fits + 1},{second}p' theories/Other.thy`", run)   # and how to read on
        self.assertLessEqual(len(run.encode()), work_meter.READ_BYTES + 600)
        self.assertIn("already in your context", self.call("Bash", {"command": f"sed -n '1,{fits}p' theories/Other"
                                                                               ".thy"})[0])  # what it showed is known
        # partly in context and more than a read: both said, and what is shown fits
        refused, _ = self.call("Bash", {"command": f"sed -n '{fits - 5},{fits + 2000}p' theories/Other.thy"})
        self.assertIsNone(refused)
        run = subprocess.run(["bash", "-c", self.rewritten()["command"]], cwd=self.w.project, capture_output=True,
                             text=True).stdout
        self.assertIn(f"[lines {fits - 5}-{fits} of theories/Other.thy are already in your context", run)
        self.assertIn(f"other {fits + 1}\n", run)
        self.assertIn("are not shown", run)
        self.w.write("theories/Wide.thy", "y" * 5_000 + "\nshort\n")
        self.assertIn("line 1 alone is 5,001 bytes", self.call("Bash", {"command": "cat theories/Wide.thy"})[0])

    def test_every_output_is_cut_where_a_read_ends_and_kept_whole(self):
        refused = self.guard("Bash", {"command": "grep -rn other theories"}, tool_use="u1")
        self.assertIsNone(refused)
        cmd = self.rewritten()["command"]
        self.assertIn(f"cut.py {work_meter.READ_BYTES} head", cmd)
        run = subprocess.run(["bash", "-c", cmd], cwd=self.w.project, capture_output=True, text=True)
        self.assertLessEqual(len(run.stdout.encode()), work_meter.READ_BYTES + 600)  # the read, and what was cut
        self.assertIn("[this call's output stops here", run.stdout)
        kept = work_meter.KEPT.search(run.stdout).group(1)
        whole = subprocess.run(["bash", "-c", "grep -rn other theories"], cwd=self.w.project, capture_output=True,
                               text=True).stdout
        self.assertEqual(open(kept).read(), whole)                     # the whole, to be read on by its lines
        on = re.search(r"`sed -n '(\d+),(\d+)p' ", run.stdout)
        self.assertEqual(whole.splitlines()[int(on.group(1)) - 1] + "\n" in run.stdout, False)  # where it goes on
        self.assertIn(whole.splitlines()[int(on.group(1)) - 2], run.stdout)
        self.assertIsNone(self.guard("Bash", {"command": "cd theories && ls"}, tool_use="u2"))
        self.assertTrue(self.rewritten()["command"].startswith("cd theories && { ( ls"))  # the cd still moves the shell
        for inp in ({"command": "python3 tools/probe_theories.py Ready --timeout 60"},        # a check: its end
                    {"command": "mkdir -p .build/tasks/1/d && ls .build"},       # a write
                    {"command": "v2.py ask --to kb 'which?'"},                   # the harness's own
                    {"command": "python3 tools/x.py"}):                          # a script
            self.assertIsNone(self.guard("Bash", inp, tool_use="u5"))
            self.assertIn("cut.py", self.rewritten()["command"], inp)
            self.assertEqual(work_meter.unwrapped(self.rewritten()["command"]), inp["command"])
        for inp in ({"command": "sed -n '1,5p' theories/Other.thy"},                 # its size is known: no cut
                    {"command": "v2.py read theories/Base.thy"},                     # it bounds itself
                    {"command": "grep -rn x theories", "run_in_background": True}):  # it writes a file
            self.assertIsNone(self.guard("Bash", inp, tool_use="u5"))
            self.assertIsNone(self.rewritten(), inp)

    def test_a_cut_call_is_recorded_as_the_call_the_session_made(self):
        # the transcript holds the call as the session made it; the hook after it may be given it as rewritten, and
        # whichever it is given it counts the call as what it is: a question is no read, a copy a write
        def made(tool_use, command, response):
            self.n += 1
            self.records.append(assistant(f"m{self.n}", fakes.iso(time.time()), [
                {"type": "tool_use", "id": tool_use, "name": "Bash", "input": {"command": command}}]))
            self.w.transcript("s1", self.records)
            self.assertIsNone(self.guard("Bash", {"command": command}, tool_use=tool_use))
            _, out, _ = self.w.hook("ctx_gauge.py", "gauge", self.hook("Bash", self.rewritten(), response,
                                                                        tool_use=tool_use))
            return ((out or {}).get("hookSpecificOutput") or {}).get("additionalContext") or ""
        self.assertNotIn("reads", made("u6", "v2.py ask --to kb 'which?'", {"stdout": "asked"}))
        self.assertNotIn("reads", made("u7", "cp theories/Base.thy .build/tasks/1/Base.thy", {"stdout": ""}))
        self.assertIn(f"1 of {work_meter.ROUNDS} reads", self.read()[1])
        self.assertNotIn("m2", self.meter()["batches"])  # the question and the copy read nothing
        self.assertNotIn("m3", self.meter()["batches"])
        # and a check is a check, hidden as it is in check_errors.py's `bash -c` inside the cut: its result is what a
        # failure's repeats are counted from
        made("u8", "python3 tools/probe_theories.py --work .build/tasks/1/p --timeout 60", {"stdout": "ok"})
        self.assertIsNotNone(self.meter()["last_check"])

    def test_a_batch_reads_at_most_its_bytes_and_the_rest_goes_in_the_next(self):
        big = ("Bash", {"command": "grep -rn other theories"}, {"stdout": "z" * work_meter.READ_BYTES})
        per = work_meter.BATCH // work_meter.READ_BYTES
        out = self.call(*big, *([big] * (per + 1)))
        self.assertTrue(all(refused is None for refused, _ in out[:per]))
        self.assertIn(f"a batch reads at most {work_meter.BATCH // 1000}K", out[per][0])
        self.assertIsNotNone(out[per + 1][0])
        self.assertIn(f"2 of {work_meter.ROUNDS} reads", self.read()[1])  # the next batch reads; the refusals cost none

    def test_the_note_waits_for_its_call_s_line_as_the_guard_does(self):
        # a probe put in the background returns at once, and its hook ran before its request was written: looked up
        # without waiting, implement-68 was never told its change and probe could be one request (2026-09-21)
        change = {"command": ".claude/orchestration/v2.py change <<'EOF'\n=== write .build/tasks/1/a.md\nx\nEOF"}
        self.call("Bash", change, {"stdout": "changed: .build/tasks/1/a.md (written anew)"})
        last = self.records[-1]["message"]["content"][0]["id"]
        self.records.append({"type": "user", "timestamp": fakes.iso(time.time()), "message": {"role": "user", "content": [
            {"type": "tool_result", "tool_use_id": last, "content": "changed: .build/tasks/1/a.md (written anew)"}]}})
        self.w.transcript("s1", self.records)                                       # the probe's request not yet in it
        probe = {"command": "python3 tools/probe_theories.py --work .build/tasks/1/probe --load Ready --timeout 60",
                 "run_in_background": True}
        self.assertIsNone(self.guard("Bash", probe, tool_use="late-0"))
        # the line lands well after the hook has started and looked (a sleep shorter than its start let a lookup that
        # did not wait find the line anyway, and the test held nothing), and well within the wait
        gauge = subprocess.Popen([sys.executable, str(fakes.HERE / "ctx_gauge.py"), "gauge"], stdin=subprocess.PIPE,
                                 stdout=subprocess.PIPE, text=True, env=dict(self.w.env, ORCH_BATCH_WAIT="6"),
                                 cwd=self.w.project)
        gauge.stdin.write(json.dumps(self.hook("Bash", probe, {"stdout": "Command running in background"}, "late-0")))
        gauge.stdin.close()
        time.sleep(2.5)                                                             # its line lands a moment after
        self.records.append(assistant("mlate", fakes.iso(time.time()),
                                      [{"type": "tool_use", "id": "late-0", "name": "Bash", "input": probe}]))
        self.w.transcript("s1", self.records)
        out = json.loads(gauge.stdout.read() or "{}")
        gauge.wait(timeout=30)
        self.assertIn("was ready in your last one", (out.get("hookSpecificOutput") or {}).get("additionalContext", ""))

    def test_a_check_refused_for_a_full_machine_is_told_to_park_for_it(self):
        # "try it when one has ended" invited trying again: seven tries in forty seconds (implement-78, 2026-09-21)
        self.w.env["ORCH_ISABELLE_RUNS"] = str(work_meter.v2.ISABELLE_MAX)
        said = self.guard("Bash", {"command": "python3 tools/incremental_check.py check --output .build/check-t1"})
        self.assertIn(f"{work_meter.v2.ISABELLE_MAX} heavy Isabelle runs (checks, replays, builds) are going", said)
        self.assertIn("park for the machine (`.claude/orchestration/v2.py park machine`)", said)
        self.assertNotIn("try it when", said)
        self.assertEqual(self.meter()["run_refused"], "heavy")

    def test_no_run_starts_while_the_machine_s_memory_is_short(self):
        # whatever the counts allow (the owner, 2026-09-21): a heavy check's main process was 7.5 GB on a 60 GiB machine
        probe = {"command": "python3 tools/probe_theories.py --work .build/tasks/1/probe --load Ready --timeout 60"}
        self.w.env["ORCH_MEM_AVAILABLE_GB"] = str(work_meter.v2.MEM_MARGIN_GB - 1)
        said = self.guard("Bash", probe)
        self.assertIn("GiB of memory available, below the", said)
        self.assertIn("park for the machine", said)
        self.w.env["ORCH_MEM_AVAILABLE_GB"] = str(work_meter.v2.MEM_MARGIN_GB + 1)
        self.assertIsNone(self.guard("Bash", probe))

    def test_a_reviewer_refused_for_the_machine_ends_its_turn_and_is_not_told_to_park(self):
        # it holds no producing slot to free, and `park` is refused to it: told to park, it could neither end its
        # turn nor wait (2026-09-21)
        (self.w.state / "work-s1.json").unlink(missing_ok=True)
        self.w.set_st(sessions={})
        self.w.session("review-2", "reviewer", "s1", task="2", reviews="1")
        check = {"command": "python3 tools/incremental_check.py check --output .build/tasks/2/c"}
        self.w.env["ORCH_ISABELLE_RUNS"] = str(work_meter.v2.ISABELLE_MAX)
        said = self.guard("Bash", check)
        self.assertIn("when nothing else is left, end your turn: you are resumed when a run may start", said)
        self.assertNotIn("park machine", said)
        self.assertEqual(self.meter()["run_refused"], "heavy")
        self.assertIn("you do not park", self.w.v2("park", "machine", env=self.w.as_session("s1")))
        self.w.env["ORCH_ISABELLE_RUNS"] = "0"
        self.assertIsNone(self.guard("Bash", check))
        self.assertIsNone(self.meter()["run_refused"])  # let through: it waits on the machine no longer
        self.assertIn("no run of yours was refused", self.w.v2("park", "machine", env=self.w.as_session("s1")))

    def test_probes_have_their_own_limit_and_a_bounded_time(self):
        # probes take seconds and were held to the limit of the heavy runs; implement-24's hung for 900 s (2026-09-21)
        probe = "python3 tools/probe_theories.py --work .build/tasks/1/probe --load Ready --timeout {}"
        self.w.env["ORCH_ISABELLE_RUNS"] = str(work_meter.v2.ISABELLE_MAX)       # the heavy runs full
        self.assertIsNone(self.guard("Bash", {"command": probe.format(work_meter.v2.PROBE_SECONDS)}))  # a probe goes
        said = self.guard("Bash", {"command": probe.format(900)})
        self.assertIn(f"A probe gets `--timeout {work_meter.v2.PROBE_SECONDS}` at most", said)
        self.assertIn("(this one names 900)", said)
        # without one it gets the tool's own default, read where it is run: 1200 in a tree made before the tool's
        # became 60 (2026-09-21 23:02), refused; 60, let go as it is
        bare = {"command": "python3 tools/probe_theories.py --work p --load Ready"}
        self.w.write("tools/probe_theories.py", "    parser.add_argument('--timeout', type=int, default=1200)\n")
        self.assertIn("without one it would get the tool's own 1200, as it stands where you run it",
                      self.guard("Bash", bare))
        self.w.write("tools/probe_theories.py", "DEFAULT_TIMEOUT = 60\n")
        self.assertIsNone(self.guard("Bash", bare))
        (self.w.project / "tools/probe_theories.py").unlink()
        self.assertIn("the tool's own default, which could not be read", self.guard("Bash", bare))
        self.w.env["ORCH_PROBE_RUNS"] = str(work_meter.v2.PROBE_MAX)             # the probes full
        said = self.guard("Bash", {"command": probe.format(900)})
        self.assertIn(f"{work_meter.v2.PROBE_MAX} probes are going", said)       # both said at once
        self.assertIn("A probe gets `--timeout", said)
        self.assertEqual(self.meter()["run_refused"], "probe")
        (self.w.state / "isabelle-exclusive").write_text(json.dumps(
            {"task": "1", "why": "a measurement", "session": "implement-1", "at": time.time()}))
        self.w.env["ORCH_PROBE_RUNS"] = "0"
        self.assertIsNone(self.guard("Bash", {"command": probe.format(900)}))    # its own measurement: unbounded

    def test_a_small_read_followed_by_another_is_named_once_a_stretch(self):
        # implement-24 read four small things in four requests, two from its reserve, and was told only the count
        # every read is told (2026-09-21)
        small = "Your last request read"
        self.produce()
        self.assertNotIn(small, self.read()[1] or "")                              # after a production: nothing before
        said = self.read()[1]
        self.assertIn(small, said)                                                  # a small read, then another
        self.assertIn("cost a whole read", said)
        self.assertNotIn(small, self.read()[1] or "")                              # once between two productions
        self.produce()
        self.read(400)                                                              # a read that was not small
        self.assertNotIn(small, self.read()[1] or "")
        self.assertIn(small, self.read()[1])                                        # a new stretch, a small one again

    def test_the_small_read_note_counts_the_whole_request_and_reads_alone(self):
        # implement-192 was told "your last request read 3,966 bytes" after a request that read about 33K in three
        # calls, and fix-279 had a probe's 831 bytes counted as a read (2026-09-22)
        small = "Your last request read"
        self.produce()
        self.call(*self.sed(200), *[self.sed(200) for _ in range(2)])        # three reads in one request, not small
        self.assertNotIn(small, self.read()[1] or "")
        self.produce()
        refused, _ = self.call("Bash", {"command": "python3 -B tools/probe_theories.py --work .build/tasks/1/p "
                                           "--theory Ready --timeout 60"},
                               {"stdout": "ok", "stderr": "", "interrupted": False})    # a probe is no read
        self.assertIsNone(refused)
        self.assertNotIn(small, self.read()[1] or "")

    def test_a_read_refused_early_takes_nothing_from_the_tiers(self):
        # a read refused late (the tiers, a batch's bytes) was left out of the count; one refused early — a removed
        # tool, a malformed `again` — was counted (the owner, 2026-09-21: a refused request counts nowhere)
        for _ in range(work_meter.ROUNDS + 2):
            self.assertIsNotNone(self.call("Read", {"file_path": "theories/Base.thy"})[0])
            self.assertIsNotNone(self.call("Bash", {"command": ".claude/orchestration/v2.py again 99"})[0])
        self.assertIn(f"1 of {work_meter.ROUNDS} reads", self.read()[1])

    def test_a_request_whose_changes_were_ready_in_the_last_one_is_told(self):
        # brief-10 wrote the ten briefs of its proposal in five requests, one after another, nothing read between;
        # implement-54 probed each change in the request after it (2026-09-21): each re-read the whole context
        def change(name, answer=None):
            return ("Bash", {"command": f".claude/orchestration/v2.py change <<'EOF'\n=== write .build/tasks/1/{name}.md"
                                        "\nx\nEOF"}, {"stdout": answer or f"changed: .build/tasks/1/{name}.md (written anew)"})

        def answered(*extra):  # the last request's answers, as Claude Code writes them, and anything after
            last = self.records[-1]["message"]
            self.records.append({"type": "user", "timestamp": fakes.iso(time.time()), "message": {"role": "user", "content": [
                {"type": "tool_result", "tool_use_id": c["id"], "content": "changed: it"} for c in last["content"]]}})
            self.records.extend(extra)
            self.w.transcript("s1", self.records)

        ready = "was ready in your last one"
        self.assertNotIn(ready, self.call(*change("a"))[1] or "")
        answered()
        self.assertIn(ready, self.call(*change("b"))[1])                          # another change, nothing learnt
        answered()
        out = self.call(*change("c"), change("d"))
        self.assertIn(ready, out[0][1])
        self.assertNotIn(ready, out[1][1] or "")                                  # said once a request
        answered()
        check = ("Bash", {"command": "python3 tools/probe_theories.py --work .build/tasks/1/probe --load Ready --timeout 60"},
                 {"stdout": "ok"})
        self.assertIn(ready, self.call(*check)[1])                                # its check, in the next request
        self.read()
        answered()
        self.assertNotIn(ready, self.call(*change("e"))[1] or "")                 # a read between
        answered({"type": "attachment", "timestamp": fakes.iso(time.time()),
                  "attachment": {"type": "queued_command", "prompt": "<task-notification>ended</task-notification>"}})
        self.assertNotIn(ready, self.call(*change("f"))[1] or "")                 # a job's end reached it
        self.records.append({"type": "user", "timestamp": fakes.iso(time.time()), "message": {"role": "user", "content": [
            {"type": "tool_result", "tool_use_id": self.records[-1]["message"]["content"][0]["id"],
             "content": "refused: change 1 (replace a.md): its SEARCH text occurs 0 times"}]}})
        self.w.transcript("s1", self.records)
        self.assertNotIn(ready, self.call(*change("g"))[1] or "")                 # the correction of a refusal

    def test_a_cut_that_did_not_take_is_said(self):
        # the rewrite is Claude Code's to apply; a read that comes back longer than a read shows says it did not. A
        # `v2.py read` is bounded by itself, and shows the briefs it names whole beside a read's bytes
        log = self.w.state / "v2.log"
        self.call("Bash", {"command": ".claude/orchestration/v2.py read task:1 task:2"},
                  {"stdout": "z" * (work_meter.READ_BYTES * 3)})
        self.assertNotIn("did not apply", log.read_text() if log.exists() else "")
        self.call("Bash", {"command": "grep -rn other theories"}, {"stdout": "z" * (work_meter.READ_BYTES * 3)})
        self.assertIn("the guard's rewrite of it through cut.py did not apply", (self.w.state / "v2.log").read_text())

    # production, and the meter itself

    def test_a_session_in_its_own_tree_is_credited_for_what_it_writes_there(self):
        # its deliverable stands in its tree: measured in the one tree, no write of it was ever production
        tree = self.w.project / ".build/trees/1"
        (tree / "theories").mkdir(parents=True)
        (tree / "theories/Ready.thy").write_text(THEORY)
        self.w.session("implement-1", "implementer", "s1", task="1", tree=".build/trees/1")
        self.thy = tree / "theories/Ready.thy"
        self.call("Bash", {"command": "true"}, {"stdout": ""})
        for _ in range(work_meter.ROUNDS + 2):
            self.read()
        self.assertIn("Production recorded", self.produce())

    def test_a_record_that_fails_is_said(self):
        (self.w.state / "work-s1.json.lock").unlink()
        (self.w.state / "work-s1.json.lock").mkdir()  # the meter cannot be opened
        self.read()
        self.assertIn("ATTENTION the work meter could not record a call of implement-1",
                      (self.w.state / "v2.log").read_text())

    def test_the_meter_is_written_under_its_lock(self):
        import fcntl
        import subprocess as sp
        with open(self.w.state / "work-s1.json.lock", "a") as held:
            fcntl.flock(held, fcntl.LOCK_EX)
            p = sp.Popen([sys.executable, str(fakes.HERE / "ctx_gauge.py"), "gauge"], stdin=sp.PIPE, stdout=sp.PIPE,
                         env=dict(self.w.env), cwd=self.w.project, text=True)
            p.stdin.write(json.dumps(self.hook("Bash", {"command": "ls"}, {"stdout": "x"}, tool_use="late")))
            p.stdin.close()
            time.sleep(1.0)
            self.assertIsNone(p.poll())  # it waits for the lock rather than write over another call's record
        self.assertEqual(p.wait(timeout=30), 0)


class PlannerGraphTests(Guarded):
    """The planner's TaskUpdate is the one door to the graph the harness does not own. Through it the planner
    completed four builds on taking stock with their work uncommitted and unreviewed, and it was never refused an
    edge. Review comes before commit, and nothing is added at the end of a chain past the limit (the owner,
    2026-09-21)."""

    def setUp(self):
        super().setUp()
        self.w.session("plan-1", "planner", "s1", settings="planner-settings.json")
        brief = fakes.BRIEF
        for i in range(1, 12):  # a chain eleven deep: 1 <- 2 <- ... <- 11
            self.w.task(str(i), description=brief, blockedBy=[str(i - 1)] if i > 1 else [])
        self.w.task("20", description=brief)  # a new task, waiting on nothing yet

    def test_a_build_fix_or_review_is_not_completed_by_hand(self):
        refused = self.guard("TaskUpdate", {"taskId": "5", "status": "completed"})
        self.assertIn("not completed by hand", refused)
        self.assertIn("Review comes before commit", refused)
        self.w.task("21", description=fakes.REVIEW_TASK.format(task="5"))
        self.assertIn("a review is completed by its verdict",
                      self.guard("TaskUpdate", {"taskId": "21", "status": "completed"}, tool_use="t1"))
        self.w.task("22", description=fakes.BRIEF.replace("Kind: build", "Kind: design"))
        self.assertIsNone(self.guard("TaskUpdate", {"taskId": "22", "status": "completed"}, tool_use="t2"))

    def test_nothing_is_hung_at_the_end_of_a_chain_past_the_limit(self):
        refused = self.guard("TaskUpdate", {"taskId": "20", "addBlockedBy": ["11"]})
        self.assertIn("would be added at the end of a chain already 11 deep, above 10", refused)
        # by the other door: making a new task wait on the end of the chain from the chain's side
        self.assertIn("at the end of a chain already 11 deep", self.guard("TaskUpdate", {"taskId": "11",
                                                                                         "addBlocks": ["20"]},
                                                                           tool_use="t1"))
        # detail is admitted at any depth: spliced in, with something already there waiting on it
        self.assertIsNone(self.guard("TaskUpdate", {"taskId": "20", "addBlockedBy": ["4"], "addBlocks": ["5"]},
                                     tool_use="t2"))
        self.assertIsNone(self.guard("TaskUpdate", {"taskId": "20", "description": "x"}, tool_use="t3"))

    def test_a_goal_at_the_end_of_a_short_chain_is_added_while_another_is_deep(self):
        # per chain (the owner, 2026-09-21): the eleven-deep chain closes only its own end
        self.w.task("30", description=fakes.BRIEF)
        self.assertIsNone(self.guard("TaskUpdate", {"taskId": "20", "addBlockedBy": ["30"]}))

    def test_repair_is_never_refused(self):
        # what the planner planned before does not bind it: deleting, rewriting and re-pointing are repair, and only
        # growing a chain past the limit at its end is refused
        self.assertIsNone(self.guard("TaskUpdate", {"taskId": "11", "status": "deleted"}))
        self.assertIsNone(self.guard("TaskUpdate", {"taskId": "11", "description": "a rewritten brief"}, tool_use="t1"))
        self.assertIsNone(self.guard("TaskUpdate", {"taskId": "11", "addBlockedBy": ["3"]}, tool_use="t2"))

    def test_an_edit_of_the_graph_through_the_harness_is_the_planner_s_production(self):
        # TaskUpdate counted and the harness's graph commands did not, so batching the graph spent the reading
        # budget a change a call would have given back
        record = lambda inp, out: self.w.hook("ctx_gauge.py", "gauge", self.hook("Bash", inp, {"stdout": out}))[1]
        record({"command": "true"}, "")  # the first call takes the baseline
        note = record({"command": ".claude/orchestration/v2.py edit .build/plans/plan-1/edit.json"},
                      "edited: g is task 21")
        self.assertIn("Production recorded", note["hookSpecificOutput"]["additionalContext"])
        note = record({"command": ".claude/orchestration/v2.py blockers 20 11"}, "refused: task 20 would be added")
        self.assertNotIn("Production recorded", (note or {}).get("hookSpecificOutput", {}).get("additionalContext", ""))

    def test_within_the_limit_a_goal_may_be_added(self):
        (self.w.tasks / "11.json").unlink()  # ten deep: at the limit, not above it
        self.assertIsNone(self.guard("TaskUpdate", {"taskId": "20", "addBlockedBy": ["10"]}))


class ReviewerWriteTests(Guarded):
    """C7 (the owner's yes of 2026-09-23): a reviewer corrects the words of the work it judges — the task's commit
    message, its result, the row of a theory it changed — and writes nothing else of the repository."""

    def setUp(self):
        super().setUp()
        self.w.session("review-3", "reviewer", "s1", task="3", reviews="3")
        self.w.write(".build/tasks/3/finalize.json", json.dumps({"files": ["theories/Ready.thy", "THEORY_MAP.md"]}))
        self.w.write("theories/Ready.thy", THEORY)
        self.w.write("THEORY_MAP.md", "| Ready | Main | The readiness theory. |\n")

    def test_its_verdict_the_task_s_words_and_its_scratch_are_its_own(self):
        for path in (".build/tasks/3/review.md", ".build/tasks/3/commit.md", ".build/tasks/3/result.md",
                     ".build/tasks/3/diffs/rows.txt"):
            self.assertIsNone(self.guard("Bash", {"command": fakes.change((path, "text\n"))}), path)
        self.assertIsNone(self.guard("Bash", {"command": "git diff main > $TMPDIR/r3.diff"}))

    def test_a_row_of_a_theory_the_task_changed_by_its_verb_alone(self):
        row = ".claude/orchestration/v2.py change <<'EOF'\n=== row Ready\nThe readiness theory, over its base.\nEOF"
        self.assertIsNone(self.guard("Bash", {"command": row}))
        said = self.guard("Bash", {"command": row.replace("row Ready", "row Other")})
        self.assertIn("only by `=== row THEORY`, for a theory the task it judges changed (Ready)", said)
        said = self.guard("Bash", {"command": fakes.change(("THEORY_MAP.md", "| Ready | Main | x |\n"))})
        self.assertIn("only by `=== row THEORY`", said)
        self.assertIn("only by `=== row THEORY`", self.guard("Bash", {"command": "echo '| X |' >> THEORY_MAP.md"}))
        self.w.write(".build/tasks/3/finalize.json", json.dumps({"files": ["theories/Ready.thy"]}))
        self.assertIn("only when that task hands THEORY_MAP.md over", self.guard("Bash", {"command": row}))

    def test_in_the_reviewed_task_s_tree_its_folder_and_the_tree_s_map_are_read_through_the_link(self):
        tree = self.w.project / ".build/trees/3"
        tree.mkdir(parents=True)
        os.symlink(self.w.project / ".build", tree / ".build")          # every tree's .build is the project's
        (tree / "THEORY_MAP.md").write_text("| Ready | Main | x |\n")
        (tree / "theories").mkdir()
        st = json.loads((self.w.state / "v2.json").read_text())
        st["sessions"]["review-3"]["tree"] = ".build/trees/3"
        (self.w.state / "v2.json").write_text(json.dumps(st))

        def guard(command):
            hook = dict(self.hook("Bash", {"command": command}), cwd=str(tree))
            out = self.w.hook("work_meter.py", "guard", hook)[1] or {}
            said = out.get("hookSpecificOutput") or {}
            return said.get("permissionDecisionReason") if said.get("permissionDecision") == "deny" else None
        self.assertIsNone(guard(fakes.change((".build/tasks/3/commit.md", "text\n"))))
        self.assertIsNone(guard(".claude/orchestration/v2.py change <<'EOF'\n=== row Ready\nThe theory.\nEOF"))
        self.assertIn("A reviewer judges", guard(fakes.change(("theories/Ready.thy", "x\n"))))

    def test_a_theory_code_or_a_decision_is_a_finding_and_refused(self):
        for path in ("theories/Ready.thy", "DECISIONS.md", "ROOT", "tools/x.py", ".build/tasks/3/finalize.json",
                     ".build/tasks/3/brief.json"):
            said = self.guard("Bash", {"command": fakes.change((path, "text\n"))})
            self.assertIn("A reviewer judges", said, path)
            self.assertIn("is a rejection", said, path)
        self.assertIn("A reviewer judges", self.guard("Bash", {"command": "echo x >> theories/Ready.thy"}))


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

    def record(self, tool, inp, response, tool_use="t0"):
        code, out, err = self.w.hook("ctx_gauge.py", "gauge", self.hook(tool, inp, response, tool_use=tool_use))
        self.assertEqual((code, err), (0, ""))
        return out

    def meter(self):
        return json.loads((self.w.state / "work-s1.json").read_text())

    def sed(self, a, b, path="theories/Base.thy"):
        lines = (self.w.project / path).read_text().splitlines()[a - 1:b]
        return {"command": f"sed -n '{a},{b}p' {path}"}, {"stdout": "\n".join(lines) + "\n", "stderr": "", "interrupted": False}

    def produce(self, text=LEMMA):
        self.thy.write_text(THEORY.replace("\nend\n", "\n" + text + "end\n"))
        self.record("Bash", {"command": fakes.change(str(self.thy))}, {"filePath": str(self.thy)})

    def test_a_probe_marked_queue_is_queued_when_the_machine_refuses_it(self):
        import base64
        (self.w.state / "isabelle-exclusive").write_text(json.dumps(
            {"task": "9", "why": "a measurement", "session": "implement-9", "at": time.time()}))
        probe = "python3 -B tools/probe_theories.py --work .build/tasks/1/p --theory Ready --timeout 60 2>&1 | tail -5"
        said = self.guard("Bash", {"command": probe})                          # unmarked: refused, and told it may queue
        self.assertIn("Task 9 holds the machine", said)
        self.assertIn("lead the probe with QUEUE=1", said)
        change = fakes.change((".build/tasks/1/x.md", "drafted\n"))
        self.assertIsNone(self.guard("Bash", {"command": change + "\nQUEUE=1 " + probe}))
        command = self.rewritten()["command"]
        self.assertIn("drafted", command)                                      # its change goes through
        head, _, queued = command.rpartition(" queue-probe ")
        self.assertTrue(head.endswith("v2.py"))
        self.assertEqual(base64.b64decode(queued).decode(), probe)             # and the probe waits in the queue
        self.assertLess(command.index(work_meter.STATUS_LINE), command.index("queue-probe"))

    def test_a_measurement_holds_the_machine_for_the_call_that_runs_it(self):
        # run in the foreground, a measurement is no job of its session, and its hold stood CLAIM_GRACE from the
        # grant: fix-220's 17 s timing held the machine three minutes while two checks waited, and task 128's pair of
        # about 200 s lost its hold at 189 s (2026-09-22). The call that runs it holds it, and no longer
        claim = self.w.state / "isabelle-exclusive"
        claim.write_text(json.dumps({"task": "1", "why": "a timing", "session": "implement-1", "at": time.time() - 60}))
        probe = "python3 -B tools/probe_theories.py --work .build/tasks/1/m --theory Ready --timeout 360"
        self.assertIsNone(self.guard("Bash", {"command": probe}, tool_use="t-m"))
        held = json.loads(claim.read_text())
        self.assertEqual(held["call"], "t-m")
        claim.write_text(json.dumps(dict(held, at=time.time() - 900)))  # the run goes on past the grace
        code = f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; print(v2.exclusive_holder())"
        holder = lambda: subprocess.run([sys.executable, "-c", code], env=self.w.env, capture_output=True,
                                        text=True).stdout.strip()
        self.assertEqual(holder(), "1")                                  # past its grace, while the call runs
        self.record("Bash", {"command": probe}, {"stdout": "MEASURE 0.2"}, tool_use="t-m")
        self.assertFalse(claim.exists())                                  # and it ends with the call
        self.assertIn("the measurement of task 1 ended with the call that ran it", (self.w.state / "v2.log").read_text())
        self.assertEqual(holder(), "None")
        # recorded where its review reads it (#129's review: a claim had left no durable record)
        self.assertIn("the machine held for a timing, no other run beside it",
                      (self.w.project / ".build/tasks/1/measurements.log").read_text())

    def test_a_measurement_holds_the_machine_at_most_its_bound_under_the_owner_s_switch(self):
        # C14: 37 holds of 09-20/22 took 3.0 hours; four past ten minutes, 1.1 hours — the longest one probe of 31 minutes
        claim = self.w.state / "isabelle-exclusive"
        long_ago = time.time() - 900
        claim.write_text(json.dumps({"task": "1", "why": "a timing", "session": "implement-1", "at": long_ago,
                                     "call": "t-m", "call_at": long_ago}))
        code = f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; print(v2.exclusive_holder())"
        holder = lambda: subprocess.run([sys.executable, "-c", code], env=dict(self.w.env, ORCH_MEASURE_MAX="600"),
                                        capture_output=True, text=True).stdout.strip()
        self.assertEqual(holder(), "1")                           # the switch is off: it holds while its call runs
        (self.w.state / "measure-bound").write_text("")
        self.assertEqual(holder(), "None")                        # on: past its bound, it lapses
        self.assertFalse(claim.exists())
        self.assertIn("the measurement of task 1 held the machine past 10 min: its claim lapses",
                      (self.w.state / "v2.log").read_text())
        self.assertIn("until the bound of 10 min lapsed it", (self.w.project / ".build/tasks/1/measurements.log").read_text())
        mail = subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                               "print(v2.take_mail('implement-1'))"], env=self.w.env, capture_output=True, text=True).stdout
        self.assertIn("the most a measurement holds it", mail)
        # a check that advances the base is no session's measurement: it holds as long as it runs
        claim.write_text(json.dumps({"task": "2", "why": "its final check advances the base heap", "pid": os.getpid(),
                                     "at": long_ago}))
        self.assertEqual(holder(), "2")
        # the window is a number the owner changes: the switch's file says it in seconds, else ORCH_MEASURE_MAX (180)
        minutes = lambda: subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); "
                                          "import v2; print(v2.measure_minutes())"], env=self.w.env,
                                         capture_output=True, text=True).stdout.strip()
        self.assertEqual(minutes(), "3")
        (self.w.state / "measure-bound").write_text("240\n")
        self.assertEqual(minutes(), "4")
        claim.write_text(json.dumps({"task": "1", "why": "a timing", "session": "implement-1", "at": time.time() - 200,
                                     "call": "t-m", "call_at": time.time() - 200}))
        self.assertEqual(holder(), "1")                           # 200 s: inside the 240 its file says
        (self.w.state / "measure-bound").write_text("60")
        self.assertEqual(holder(), "None")                        # past the 60 it says now, though inside ORCH's 600

    def test_a_shared_measurement_takes_its_kind_s_slot_holds_nothing_and_is_told_the_load(self):
        # the owner, 2026-09-23: "the only difference should be that it gets ran without holding all of the machine, but
        # if it is heavy then it uses a heavy slot if it is like a probe it uses a probe slot"
        self.w.env.update(ORCH_ISABELLE_RUNS="1", ORCH_LOAD_SAMPLER="0")  # one heavy slot of two taken
        said = subprocess.run([sys.executable, str(fakes.HERE / "v2.py"), "measuring", "--shared", "the judgment's cost"],
                              env=dict(self.w.env, **self.w.as_session("s1"), ORCH_CONTROL="0"), capture_output=True,
                              text=True, cwd=self.w.project).stdout
        self.assertIn("measure now, sharing the machine", said)
        self.assertIn("a heavy slot for a heavy run, a probe slot for a probe", said)
        self.assertIn("fitted to 3 minutes", said)
        long_probe = "python3 -B tools/probe_theories.py --work .build/tasks/1/m --theory Ready --timeout 600"
        self.assertIn("A measurement fits its window: `--timeout 180` at most", self.guard("Bash", {"command": long_probe}))
        check = "python3 -B tools/incremental_check.py check --output .build/tasks/1/c1"
        self.assertIsNone(self.guard("Bash", {"command": check}, tool_use="t-sh"))  # the free heavy slot
        self.assertFalse((self.w.state / "isabelle-exclusive").exists())             # and nothing held
        marker = json.loads((self.w.state / "measure-shared" / "implement-1.json").read_text())
        self.assertEqual(marker["call"], "t-sh")
        self.assertIn("cpu_total", marker["sample"])
        note = self.record("Bash", {"command": check}, {"stdout": "done"}, tool_use="t-sh")
        self.assertIn("Your measurement ran", json.dumps(note))
        self.assertIn("runnable work waited for a CPU", json.dumps(note))
        self.assertIn("Isabelle runs counted on the machine 2 heavy and 0 probes", json.dumps(note))  # its own among them
        log = (self.w.project / ".build/tasks/1/measurements.log").read_text()
        self.assertIn("the judgment's cost, shared, the machine not held;", log)
        self.assertFalse((self.w.state / "measure-shared" / "implement-1.json").exists())  # one measurement a claim
        # with every heavy slot taken it waits for one, as any heavy run does
        self.w.env.update(ORCH_ISABELLE_RUNS="2")
        subprocess.run([sys.executable, str(fakes.HERE / "v2.py"), "measuring", "--shared", "again"],
                       env=dict(self.w.env, **self.w.as_session("s1"), ORCH_CONTROL="0"), capture_output=True,
                       cwd=self.w.project)
        self.assertIn("heavy Isabelle runs (checks", self.guard("Bash", {"command": check}) or "")

    def test_the_load_over_an_interval_and_its_sampler(self):
        import threading
        v2 = work_meter.v2
        with tempfile.TemporaryDirectory() as temp, patch.object(v2, "LOADS", temp), patch.object(v2, "LOAD_EVERY", 0.05):
            start = v2.machine_sample()
            worker = threading.Thread(target=v2.cmd_sample_load, args=("c1",))
            worker.start()
            time.sleep(0.3)
            line, fig = v2.machine_load(start, "c1")
            worker.join(5)
            self.assertFalse(worker.is_alive())                        # it ends with the call
            self.assertIn("memory in use", line)
            self.assertTrue(0 <= fig["cpu_busy"] <= 1, fig)
            self.assertIn("% busy on average", line)
            self.assertGreaterEqual(fig["memory_peak"], fig["memory_mean"])
            self.assertFalse(os.path.exists(os.path.join(temp, "c1.samples")))
        self.assertIn("little contention", v2.load_verdict({"cpu_pressure": 0.01, "memory_pressure": 0}))
        self.assertIn("heavy contention", v2.load_verdict({"cpu_pressure": 0.4, "memory_pressure": 0}))

    def test_a_worker_may_not_wait_start_subagents_or_read_a_running_jobs_output(self):
        self.assertIn("starts no subagents", self.guard("Agent", {"prompt": "x"}))
        self.assertIn("Waiting is refused", self.guard("TaskOutput", {"task_id": "b1"}))
        self.assertIn("Waiting is refused", self.guard("Bash", {"command": "sleep 30"}))
        self.assertIn("Waiting is refused", self.guard("Bash", {"command": "tail -f .build/probe.log"}))
        self.assertIn("Waiting is refused", self.guard("Bash", {"command": "until [ -e x ]; do sleep 5; done"}))
        self.assertIsNone(self.guard("Bash", {"command": "sleep 1"}))
        job = "/tmp/claude-1000/x/tasks/b7x.output"
        self.w.transcript("s1", self.records)
        self.assertIn("still running", self.guard("Bash", {"command": f"cat {job}"}))
        self.records.append({"type": "user", "timestamp": fakes.iso(time.time()), "message": {"content":
                             "<task-notification><task-id>b7x</task-id><status>completed</status></task-notification>"}})
        self.w.transcript("s1", self.records)
        self.assertIsNone(self.guard("Bash", {"command": f"cat {job}"}))

    def test_rounds_since_production_are_limited_and_production_resets_them(self):
        self.w.env["ORCH_READ_RESERVE"] = "0"  # the first tier alone: the reserve is tested apart (ReadTiersTests)
        self.requests(work_meter.ROUNDS - 1)
        self.assertIsNone(self.guard("Bash", {"command": "ls theories"}, tool_use="t-new"))  # this request makes ROUNDS
        self.requests(1)
        reason = self.guard("Bash", {"command": "ls theories"}, tool_use="t-new")
        self.assertIn(f"{work_meter.ROUNDS} reads since your last production", reason)
        self.assertIsNone(self.guard("Bash", {"command": "ls"}, tool_use=f"t{self.n}"))  # recorded already: not twice
        self.assertIsNone(self.guard("Bash", {"command": fakes.change(str(self.thy))}, tool_use="t-new"))  # writing is never refused
        self.assertIsNotNone(self.guard("Bash", {"command": "sed -n '1,5p' theories/Other.thy"}, tool_use="t-new"))
        self.assertIsNone(self.guard("Bash", {"command": ".claude/orchestration/v2.py ask 1 x"}, tool_use="t-new"))
        # the protocols write the harness's own commands both ways, and the short form is the one that ends a turn
        self.assertIsNone(self.guard("Bash", {"command": "v2.py park run"}, tool_use="t-new"))
        self.assertIsNone(self.guard("Bash", {"command": "cd /tmp && v2.py result 1"}, tool_use="t-new"))
        self.assertIsNotNone(self.guard("Bash", {"command": "grep -n park v2.py"}, tool_use="t-new"))  # a mention reads
        self.assertIsNotNone(self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready --timeout 60"}, tool_use="t-new"))
        time.sleep(0.01)
        self.produce()
        self.assertIsNone(self.guard("Bash", {"command": "ls theories"}, tool_use="t-new"))

    def test_every_read_is_told_what_is_left_and_production_restarts_the_count(self):
        self.w.env["ORCH_READ_RESERVE"] = "0"  # the first tier alone: the reserve is tested apart (ReadTiersTests)
        n = work_meter.ROUNDS
        self.requests(1)
        note = self.record("Bash", *self.sed(1, 10, "theories/Other.thy"))["hookSpecificOutput"]["additionalContext"]
        self.assertIn(f"Since your last production: 2 of {n} reads", note)
        self.assertIn(f"{n - 2} more read before the reserve", note)
        self.requests(1)
        note = self.record("Bash", *self.sed(11, 20, "theories/Other.thy"))["hookSpecificOutput"]["additionalContext"]
        self.assertIn(f"{n} of {n} reads", note)
        self.assertIn("That was your last read", note)
        time.sleep(0.01)
        self.thy.write_text(THEORY.replace("\nend\n", "\n" + LEMMA + "end\n"))
        note = self.record("Bash", {"command": fakes.change(str(self.thy))}, {})["hookSpecificOutput"]["additionalContext"]
        self.assertIn("Production recorded: the count restarts", note)

    def test_production_is_content_in_a_deliverable(self):
        at = self.meter()["production_at"]
        self.thy.write_text(THEORY.replace("\n\nend", "\n(* a comment *)\n\nend"))  # a comment is no production
        self.record("Bash", {"command": fakes.change(str(self.thy))}, {})
        self.assertEqual(self.meter()["production_at"], at)
        self.w.write("Scratch.thy", THEORY + LEMMA)  # not a deliverable
        self.record("Bash", {"command": fakes.change("Scratch.thy")}, {})
        self.assertEqual(self.meter()["production_at"], at)
        self.w.write("NOTES.md", "notes\n" + "word " * 25)  # 25 words: not yet
        self.record("Bash", {"command": fakes.change("NOTES.md")}, {})
        self.assertEqual(self.meter()["production_at"], at)
        self.w.write("NOTES.md", "notes\n" + "word " * 25 + " ".join(f"new{i}" for i in range(20)))  # 45 since
        self.record("Bash", {"command": fakes.change("NOTES.md")}, {})
        at2 = self.meter()["production_at"]
        self.assertGreater(at2, at)
        self.w.write("tool.py", "# a comment\n\n" + "".join(f"x{i} = {i}\n" for i in range(5)))
        self.record("Bash", {"command": fakes.change("tool.py")}, {})
        at3 = self.meter()["production_at"]
        self.assertGreater(at3, at2)
        self.w.write(".build/tasks/1/Draft.thy", THEORY)  # a draft counts
        self.record("Bash", {"command": fakes.change(".build/tasks/1/Draft.thy")}, {})
        self.assertGreater(self.meter()["production_at"], at3)

    # reads of lines already in context: filtered, not refused (the owner, 2026-09-21)

    def run_rewritten(self):
        return subprocess.run(["bash", "-c", self.rewritten()["command"]], cwd=self.w.project, capture_output=True,
                              text=True).stdout

    def test_a_read_of_lines_in_context_is_filtered_until_the_file_changes(self):
        self.record("Bash", *self.sed(1, 60))
        self.assertIsNone(self.guard("Bash", self.sed(61, 80)[0]))
        self.assertIsNone(self.rewritten())                                   # nothing of it in context: read as it is
        whole = self.guard("Bash", self.sed(10, 50)[0])                       # all of it: only the note
        self.assertIn("[lines 10-50 of theories/Base.thy are already in your context", whole)
        self.assertIn("nothing else to show, and it counts as no read", whole)
        self.assertIsNone(self.guard("Bash", self.sed(50, 70)[0]))            # part of it: the rest, and the note
        shown = self.run_rewritten()
        self.assertIn("[lines 61-70 of theories/Base.thy]\nline 61\n", shown)
        self.assertIn("line 70\n", shown)
        self.assertNotIn("line 60\n", shown)
        self.assertNotIn("line 71\n", shown)
        self.assertIn("[lines 50-60 of theories/Base.thy are already in your context", shown)
        with open(self.w.project / "theories/Base.thy", "a") as f:
            f.write("line 101\n")
        self.assertIsNone(self.guard("Bash", self.sed(10, 50)[0]))
        self.assertIsNone(self.rewritten())  # changed since: nothing of it is in context
        self.record("Bash", *self.sed(10, 50))
        self.assertIn("[lines 20-30 of theories/Base.thy are already in your context",
                      self.guard("Bash", self.sed(20, 30)[0]))  # and what is read of it now is

    def test_a_read_with_several_gaps_shows_each_and_records_what_it_showed(self):
        self.record("Bash", *self.sed(1, 20))
        self.record("Bash", *self.sed(41, 60))
        self.assertIsNone(self.guard("Bash", self.sed(1, 80)[0], tool_use="f1"))
        shown = self.run_rewritten()
        self.assertIn("[lines 21-40 of theories/Base.thy]\nline 21\n", shown)
        self.assertIn("[lines 61-80 of theories/Base.thy]\nline 61\n", shown)
        self.assertNotIn("line 20\n", shown)
        self.assertNotIn("line 41\n", shown)
        self.assertIn("[lines 1-20, 41-60 of theories/Base.thy are already in your context", shown)
        self.record("Bash", self.rewritten(), {"stdout": shown, "stderr": "", "interrupted": False}, tool_use="f1")
        ranges = self.meter()["reads"][str(self.w.project / "theories/Base.thy")]["ranges"]
        self.assertEqual(work_meter.gaps(ranges, 1, 80), [])                  # what it showed is in context now
        self.assertIn("[lines 1-80 of theories/Base.thy are already in your context", self.guard("Bash", self.sed(1, 80)[0]))

    def test_a_filtered_read_that_did_not_run_records_nothing(self):
        self.record("Bash", *self.sed(1, 20))
        self.assertIsNone(self.guard("Bash", self.sed(1, 40)[0], tool_use="f2"))
        self.record("Bash", self.rewritten(), {"stdout": "", "stderr": "", "interrupted": True}, tool_use="f2")
        self.assertIsNone(self.guard("Bash", self.sed(21, 40)[0]))
        self.assertIsNone(self.rewritten())  # lines 21-40 were never shown: not in context

    def test_the_same_failure_after_fixes_stops_checks_until_the_planner_answers(self):
        def check(failure):
            self.assertIsNone(self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready --timeout 60"}, tool_use=f"c{time.time()}"))
            self.record("Bash", {"command": "python3 tools/probe_theories.py Ready --timeout 60"},
                        {"stdout": f'*** {failure}\n*** At command "by" (line 7 of "{self.thy}")\n'})
        check("Failed to finish proof")
        for i in range(work_meter.CIRCLING):
            self.produce(LEMMA.replace("simp", f"auto{i}"))  # a fix
            check("Failed to finish proof")
        reason = self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready --timeout 60"}, tool_use="t-new")
        self.assertIn(f"came back {work_meter.CIRCLING} times after fixes", reason)
        time.sleep(0.01)
        self.w.set_st(asks={"q1": {"from": "implement-1", "text": "q", "asked": time.time(), "answered": time.time(),
                                   "state": "answered"}})
        self.assertIsNone(self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready --timeout 60"}, tool_use="t-new"))

    def test_failures_that_move_are_progress(self):
        for i in range(work_meter.CIRCLING + 2):
            self.produce(LEMMA.replace("simp", f"auto{i}"))
            self.record("Bash", {"command": "python3 tools/probe_theories.py Ready --timeout 60"},
                        {"stdout": f'*** Failed {i}\n*** At command "by" (line {7 + i} of "{self.thy}")\n'})
        self.assertIsNone(self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready --timeout 60"}, tool_use="t-new"))

    def test_a_quick_fix_has_its_own_budget(self):
        self.fix(time.time())
        self.requests(work_meter.ROUNDS + 1, after=0.01)
        self.assertIsNone(self.guard("Bash", {"command": "ls"}, tool_use="t-new"))  # the production limits do not apply
        self.requests(work_meter.FIX_ROUNDS - work_meter.ROUNDS - 1, after=0.02)
        self.assertIn(f"{work_meter.FIX_ROUNDS} requests) is spent", self.guard("Bash", {"command": "ls"}, tool_use="t-new"))
        self.records = []
        self.requests(1, after=0.03)
        self.fix(time.time() - work_meter.FIX_MINUTES * 60 - 1)
        self.assertIn("budget", self.guard("Bash", {"command": "ls"}, tool_use="t-new"))
        self.assertIsNone(self.guard("Bash", {"command": ".claude/orchestration/v2.py result 1"}, tool_use="t-new"))
        self.assertIsNone(self.guard("Bash", {"command": fakes.change(str(self.w.project / ".build/tasks/1/result.md"))}, tool_use="t-new"))
        self.assertIsNotNone(self.guard("Bash", {"command": fakes.change(str(self.thy))}, tool_use="t-new"))

    def test_a_refused_request_counts_in_no_limit(self):
        # fix-46 lost one of its eight requests to a refused form; the owner: a refused request counts for nothing
        # anywhere (2026-09-21)
        self.fix(time.time())
        first = self.n + 1
        self.requests(work_meter.FIX_ROUNDS + 2, after=0.01)
        for i in range(first, self.n + 1):  # every call of every one of them refused
            self.assertIsNotNone(self.guard("Bash", {"command": "echo x > NOTES.md"}, tool_use=f"t{i}"))
        self.assertIsNone(self.guard("Bash", {"command": "ls"}, tool_use="t-new"))  # none of them counted
        self.requests(work_meter.FIX_ROUNDS + 1, after=0.02)                        # made, not refused: counted
        self.assertIn("is spent", self.guard("Bash", {"command": "ls"}, tool_use="t-last"))

    def fix(self, since):
        st = self.w.st()
        st["sessions"]["implement-1"]["fix"] = {"since": since}
        (self.w.state / "v2.json").write_text(json.dumps(st))

    def test_a_session_without_a_role_is_not_guarded(self):
        self.w.set_st(sessions={})
        self.assertIsNone(self.guard("Agent", {"prompt": "x"}))  # the owner's own session, and anything not the harness's
        self.assertIsNone(self.guard("Read", {"file_path": "HANDOFF.md"}))


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
        self.assertIn("reads statements, not details", self.guard("Bash", {"command": "cat theories/Ready.thy"}))
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
        # the task designer proposes and no longer edits the graph, so the task tools are not its production: its
        # proposal, written where the protocol names it, is (2026-09-20)
        self.w.session("brief-2", "task-designer", "s1", task="2", settings="planner-settings.json")
        record("Bash", {"command": "true"})
        self.w.write(".build/tasks/2/brief/proposal.json", '[{"key": "a", "subject": "s", "description": "'
                     + "word " * 45 + '"}]')
        record("Bash", {"command": fakes.change(".build/tasks/2/brief/proposal.json")})
        self.assertEqual(meter()["productions"], 1)
        (self.w.state / "work-s1.json").unlink()
        self.w.set_st(sessions={})
        self.w.session("review-2", "reviewer", "s1", task="2")
        record("Bash", {"command": "true"})
        self.w.write(".build/tasks/2/review.md", "Verdict: accept\n## Summary\n" + "word " * 45)
        record("Bash", {"command": fakes.change(".build/tasks/2/review.md")})
        self.assertEqual(meter()["productions"], 1)
        (self.w.state / "work-s1.json").unlink()
        self.w.set_st(sessions={})
        self.w.session("plan-4", "planner", "s1", settings="planner-settings.json")
        record("Bash", {"command": "true"})
        self.w.write(".build/plans/plan-4/notes.md", " ".join(f"note{i}" for i in range(45)))
        record("Bash", {"command": fakes.change(".build/plans/plan-4/notes.md")})
        self.assertEqual(meter()["productions"], 1)

    def test_the_knowledge_base_is_not_metered(self):
        self.w.session("kb-1", "kb", "s1")
        self.assertIsNone(self.guard("Bash", {"command": "cat HANDOFF.md"}))
        self.assertIsNotNone(self.guard("Bash", {"command": "cat theories/Ready.thy"}))


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
        self.assertIsNone(self.guard("Bash", {"command": fakes.change(str(self.w.project / "ROOT"))}))
        # they are its own while it checks, while a quick fix repairs them, and while it commits
        for stage in ("committing", "fixing"):
            self.w.set_st(tasks={"1": {"stage": stage}, "2": {"stage": "running", "session": "implement-2"}})
            self.assertIn(f"ROOT belongs to task 1's finalization, which is {stage}",
                          self.guard("Bash", {"command": fakes.change(str(self.w.project / "ROOT"))}))
        self.assertIsNone(self.guard("Bash", {"command": fakes.change(str(self.w.project / "theories/Elsewhere.thy"))}))
        self.w.set_st(tasks={"1": {"stage": "checking"}, "2": {"stage": "running", "session": "implement-2"}})
        reason = self.guard("Bash", {"command": fakes.change(str(self.w.project / "theories/Other.thy"))})
        self.assertIn("Task 1 holds the working tree (its finalization, checking", reason)
        self.assertIn("drafts under .build/tasks/2/", reason)
        self.assertIsNotNone(self.guard("Bash", {"command": "echo x >> ROOT"}))  # a shell write, any file
        self.assertIsNotNone(self.guard("Bash", {"command": "rm theories/Old.thy"}))
        self.assertIsNone(self.guard("Bash", {"command": fakes.change(str(self.w.project / ".build/tasks/2/Other.thy"))}))
        self.assertIsNone(self.guard("Bash", {"command": "cat theories/Other.thy"}))  # reads are free
        self.assertEqual(self.w.st()["sessions"]["implement-2"]["tree_wait"], "1")
        self.w.set_st(tasks={"1": {"stage": "done"}, "2": {"stage": "running", "session": "implement-2"}})
        self.w.v2("dispatch")
        self.assertIn("it is yours", json.dumps(self.w.mail("implement-2")))  # busy: its hooks deliver it
        self.assertNotIn("tree_wait", self.w.st()["sessions"]["implement-2"])
        self.assertIsNone(self.guard("Bash", {"command": fakes.change(str(self.w.project / "theories/Other.thy"))}))

    def test_a_write_inside_a_loop_or_a_condition_is_a_write(self):
        # task 56's `for f in …; do cp … theories/$f.thy; done` was read as `do`, no write, and four theories went into
        # the tree task 66 held, one of them undeclared, while its ROOT edit was refused (2026-09-22)
        self.w.set_st(tasks={"1": {"stage": "checking"}, "2": {"stage": "running", "session": "implement-2"}})
        for c in ("for f in A B; do cp .build/tasks/2/draft/$f.thy theories/$f.thy; done",
                  "if true; then rm theories/Old.thy; fi", "while false; do mv x theories/Y.thy; done"):
            self.assertIn("Task 1 holds the working tree", self.guard("Bash", {"command": c}) or "", c)
        self.assertIsNone(self.guard("Bash", {"command": "for f in A B; do cp .build/tasks/2/draft/$f.thy "
                                                         ".build/tasks/2/probe/$f.thy; done"}))  # its own drafts

    def test_a_draft_written_beside_a_copy_into_the_tree_is_a_draft(self):
        # implement-62's `git show HEAD:$f > .build/tasks/62/head/$f` was refused as a redirection into the tree for
        # the `cp` of those files into the tree after it — copying stands (2026-09-22 03:10)
        self.w.set_st(tasks={"2": {"stage": "running", "session": "implement-2"}})
        c = ("set -eu; d=.build/tasks/2/head; mkdir -p $d; for f in ROOT NOTES.md; do git show HEAD:$f > $d/$f; done; "
             "cp $d/ROOT $d/NOTES.md .")
        self.assertIsNone(self.guard("Bash", {"command": c}))
        self.assertIn("Not by a redirection", self.guard("Bash", {"command": "echo x > ROOT; cp a b"}))

    def test_a_script_writing_by_a_name_it_gave_a_path_is_read(self):
        # implement-26 and fix-97.2 were refused their own result's edit as a script whose target could not be read:
        # `p='.build/tasks/…/result.md'` and then `open(p, 'w')` (2026-09-22)
        self.w.set_st(tasks={"2": {"stage": "running", "session": "implement-2"}})
        script = "python3 - <<'EOF'\np = '{}'\ns = open(p).read() if False else ''\nopen(p, 'w').write(s + 'x')\nEOF"
        self.assertIsNone(self.guard("Bash", {"command": script.format(".build/tasks/2/result.md")}))
        self.assertIn("Not by a script that writes", self.guard("Bash", {"command": script.format("theories/A.thy")}))

    def test_a_temporary_file_is_no_write_into_the_tree(self):
        # review-97.3's `git show main:THEORY_MAP.md > $TMPDIR/main.md` was refused as a redirection into its tree
        # (2026-09-22 06:30)
        self.w.set_st(tasks={"2": {"stage": "running", "session": "implement-2"}})
        for c in ("git show HEAD:README > $TMPDIR/main.md; cmp $TMPDIR/main.md README",
                  "git show HEAD:README > /tmp/main.md"):
            self.assertIsNone(self.guard("Bash", {"command": c}), c)

    def test_a_script_writing_into_a_temporary_directory_it_makes_stands(self):
        # review-122's test of fix-122's function in a `tempfile.TemporaryDirectory()` was refused twice (06:55)
        self.w.set_st(tasks={"2": {"stage": "running", "session": "implement-2"}})
        script = ("python3 - <<'EOF'\nimport tempfile, pathlib\nwith tempfile.TemporaryDirectory() as d:\n"
                  "    pathlib.Path(d, 'out.txt').write_text('x')\n{}EOF")
        self.assertIsNone(self.guard("Bash", {"command": script.format("")}))
        self.assertIn("Not by a script that writes", self.guard("Bash", {"command": script.format(
            "open('theories/A.thy', 'w').write('x')\n")}))                       # a path it names is still judged

    def test_a_redirection_writes_where_the_call_stands_then(self):
        # brief-141's `cd .build/tasks/141/brief && jq … > proposal.json` after its change was read as writing the
        # project's proposal.json (2026-09-22 10:46)
        self.w.set_st(tasks={"2": {"stage": "running", "session": "implement-2"}})
        change = fakes.change((".build/tasks/1/brief/a.md", "x\n"))
        self.assertIsNone(self.guard("Bash", {"command": change + "\ncd .build/tasks/1/brief && echo '{}' > proposal.json"}))
        self.assertIn("Not by a redirection", self.guard("Bash", {"command": "cd theories && echo x > A.thy"}))
        self.assertIn("Not by a redirection", self.guard("Bash", {"command": "cd .build/tasks/1 && cd ../../../theories && echo x > A.thy"}))
        # a name given from a variable already known: review-227's `T="$TMPDIR/r227"` (2026-09-22 20:12)
        self.assertIsNone(self.guard("Bash", {"command": 'T="$TMPDIR/r227"; mkdir -p "$T"; for n in a b; do '
                                                         'git show HEAD:ROOT > "$T/$n"; done'}))
        self.assertIn("Not by a redirection", self.guard("Bash", {"command": 'T="$PWD/theories"; echo x > "$T/A.thy"'}))

    def test_a_script_whose_paths_are_made_at_run_time_in_a_draft_s_place_stands(self):
        # plan-42's `open('.build/plans/plan-42/b'+tid+'.md','w')` and review-94.2's `open(f'{T}/{n}','wb')` with
        # `T=os.environ['TMPDIR']+'/mf'` were refused as scripts whose targets could not be read (2026-09-22 11:01)
        self.w.set_st(tasks={"2": {"stage": "running", "session": "implement-2"}})
        run = "python3 - <<'EOF'\nimport os\n{}EOF"
        self.assertIsNone(self.guard("Bash", {"command": run.format(
            "T=os.environ['TMPDIR']+'/mf'\nfor n in 'bmt':\n    open(f'{T}/{n}','wb').write(b'x')\n")}))
        self.assertIsNone(self.guard("Bash", {"command": run.format(
            "for tid in ('155', '157'):\n    open('.build/tasks/1/b'+tid+'.md','w').write('x')\n")}))
        self.assertIn("Not by a script that writes", self.guard("Bash", {"command": run.format(
            "for n in ('A', 'B'):\n    open('theories/'+n+'.thy','w').write('x')\n")}))       # made, but in the tree
        self.assertIn("could not be read", self.guard("Bash", {"command": run.format(
            "import sys\nopen(sys.argv[1],'w').write('x')\n")}))                              # made from nothing fixed
        # a triple-quoted string holds text, not where the script writes; a path joined under a known name writes in
        # its directory (fix-265, 2026-09-22 20:08)
        self.assertIsNone(self.guard("Bash", {"command": run.format(
            "from pathlib import Path\ndst=Path('.build/tasks/1/frame')\ns='''    theory.write_text(text)\n'''\n"
            "(dst/'inject.py').write_text(s)\n")}))
        self.assertIn("Not by a script that writes", self.guard("Bash", {"command": run.format(
            "from pathlib import Path\ndst=Path('theories')\n(dst/'A.thy').write_text('x')\n")}))  # in the tree
        said = self.guard("Bash", {"command": run.format("open('.build/outputs/implement-1/mf/b','wb').write(b'x')\n")})
        self.assertIn(".build/outputs/ is the harness's", said)                           # and why not there
        self.assertIn(".build/tasks/<your task>/", said)

    def test_the_planner_reads_a_task_tree_s_documents_and_not_its_theories(self):
        # plan-37, judging design 85, was refused its DECISIONS.md entry in the design's tree (2026-09-22 06:21)
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json")
        self.w.write(".build/trees/5/DECISIONS.md", "## An entry\nIt says why.\n")
        self.w.write(".build/trees/5/theories/A.thy", "theory A imports Main begin end\n")
        said = lambda c: ((self.w.hook("work_meter.py", "guard", dict(self.hook("Bash", {"command": c}, tool_use="t-p"),
                                                                        session_id="p1"))[1] or {})
                          .get("hookSpecificOutput") or {})
        self.assertNotEqual(said("sed -n '1,2p' .build/trees/5/DECISIONS.md").get("permissionDecision"), "deny")
        self.assertEqual(said("sed -n '1,2p' .build/trees/5/theories/A.thy").get("permissionDecision"), "deny")

    def test_a_session_without_a_task_is_told_whose_the_held_tree_is(self):
        # plan-35 was told to write drafts under `.build/tasks/None/` and to park (2026-09-22 03:14)
        self.w.session("plan-1", "planner", "p1", settings="planner-settings.json")
        self.w.set_st(tasks={"1": {"stage": "checking"}})
        _, out, _ = self.w.hook("work_meter.py", "guard", dict(self.hook(
            "Bash", {"command": "mv theories/Other.thy .build/tasks/1/"}, tool_use="t-plan"), session_id="p1"))
        said = ((out or {}).get("hookSpecificOutput") or {}).get("permissionDecisionReason") or ""
        self.assertIn("Task 1 holds the working tree", said)
        self.assertIn("v2.py tell 1", said)
        self.assertNotIn("None", said)
        self.assertNotIn("park tree", said)

    def test_reads_are_read_as_reads_and_writes_where_they_write(self):
        # four requests lost to `git merge-base` read as `git merge`, six to reads of a check's tool or output taken
        # for a check while the machine was full, two to `cp` out of theories/ taken for a write into the held tree,
        # and four to writes under .build/ behind a `cd` or a variable taken for writes into a tree (2026-09-21)
        self.w.set_st(tasks={"1": {"stage": "checking"}, "2": {"stage": "running", "session": "implement-2"}})
        for c in ("git merge-base --is-ancestor HEAD main && echo yes", "git merge-base HEAD main",
                  "cp theories/A.thy theories/B.thy .build/tasks/2/draft/",
                  "cd .build/tasks/2 && echo x > out.txt", "W=.build/tasks/2/time; mkdir -p $W; echo x > $W/out.txt"):
            self.assertIsNone(self.guard("Bash", {"command": c}), c)
        self.assertIsNotNone(self.guard("Bash", {"command": "git merge main"}))
        self.assertIn("Task 1 holds the working tree", self.guard("Bash", {"command": "cp .build/tasks/2/A.thy theories/"}))
        # its number is said, so that the change can be corrected into the drafts (implement-62, 2026-09-22)
        for path, why in (("theories/Other.thy", "Task 1 holds the working tree"), ("ROOT", "belongs to task 1's")):
            said = self.guard("Bash", {"command": fakes.change(str(self.w.project / path))})
            self.assertIn(why, said)
            self.assertIn("v2.py again", said)
        # a search pattern naming a writing call is no script that writes (investigate-82, 2026-09-22)
        self.assertIsNone(self.guard("Bash", {"command": 'mkdir .build/tasks/2/p; test -d /tmp/p && rmdir /tmp/p; '
                                                         'grep -n "shutil.copy" tools/x.py'}))
        self.w.set_st(tasks={"2": {"stage": "running", "session": "implement-2"}})
        self.assertIn("Not by a redirection", self.guard("Bash", {"command": "cd theories && echo x > Bad.thy"}) or "")
        self.w.env["ORCH_ISABELLE_RUNS"] = str(work_meter.v2.ISABELLE_MAX)                   # the machine full
        for c in ('grep -n "def retain" tools/incremental_check.py', "python3 tools/probe_theories.py --help",
                  "sed -n 1,40p tools/probe_theories.py", "cd .build/check-a && ls"):
            self.assertIsNone(self.guard("Bash", {"command": c}), c)
        for c in ("python3 -B tools/incremental_check.py check --output .build/check-t", "timeout 600 /usr/bin/env "
                  "X=1 /opt/isabelle/bin/isabelle ML_process -l Pure", "python3 tools/replay_development_answers.py"):
            self.assertIn("heavy Isabelle runs", self.guard("Bash", {"command": c}) or "", c)

    def test_a_question_that_names_a_change_in_its_text_is_not_a_change(self):
        # task 56's question to the planner named `v2.py change` and was refused as a change out of its form (2026-09-22)
        self.assertIsNone(self.guard("Bash", {"command": '.claude/orchestration/v2.py ask --to planner "the harness '
                                                         'refused my v2.py change of ROOT; restore theories/X.thy"'}))

    def test_a_finalization_in_its_own_tree_holds_none_of_the_one_tree_s_files(self):
        # its commit is made in its tree and carries nothing written here, and its landing waits for what stands here
        # (finalize.committed_run): implement-54 was refused THEORY_MAP.md for task 24's finalization in tree 24,
        # while `park tree` told it the tree was free — it could neither write nor wait (2026-09-21)
        (self.w.project / ".build/trees/1").mkdir(parents=True)
        self.w.env["ORCH_TREES"] = "1"
        for stage in ("checking", "fixing", "committing"):
            self.w.set_st(tasks={"1": {"stage": stage}, "2": {"stage": "running", "session": "implement-2"}})
            self.assertIsNone(self.guard("Bash", {"command": fakes.change(str(self.w.project / "ROOT"))}), stage)

    def test_a_session_with_nothing_left_but_the_tree_parks_and_the_slot_is_free(self):
        self.w.set_st(tasks={"1": {"stage": "checking"}, "2": {"stage": "running", "session": "implement-2"}})
        out = self.w.v2("park", "tree", env=self.w.as_session("s1"))
        self.assertIn("resumed here, your context intact, when task 1 has let the working tree go", out)
        self.assertEqual(self.w.st()["sessions"]["implement-2"]["state"], "parked")
        self.assertIsNone(self.w.hook("ctx_gauge.py", "stop", {"session_id": "s1", "hook_event_name": "Stop"})[1])
        self.assertIn("You are parked", self.guard("Bash", {"command": "cat ROOT"}))
        self.assertTrue((self.w.state / "flags" / "s1.ended").exists())  # the park ends its turn at its hook
        # woken early (its run's completion), it is refused and its turn ends there: nothing is left to say
        _, out, _ = self.w.hook("work_meter.py", "guard", self.hook("Bash", {"command": "cat ROOT"}, tool_use="t1"))
        self.assertIs(out["continue"], False)
        self.assertIn("You are parked", out["stopReason"])

    def test_no_session_changes_the_index_or_the_history(self):
        for c in ("git add theories/X.thy", "git commit -m x", "git stash", "git checkout -- ROOT", "git -C . reset --hard",
                  "cd theories && git restore X.thy", "git push origin HEAD"):
            self.assertIn("only by the finalizer", self.guard("Bash", {"command": c}), c)
        for c in ("git status", "git diff HEAD -- ROOT", "git log --stat -3"):
            self.assertIsNone(self.guard("Bash", {"command": c}), c)

    def test_writes_to_the_working_tree_are_attributed_to_the_task(self):
        self.assertIsNone(self.guard("Bash", {"command": fakes.change(str(self.w.project / "theories/Other.thy"))}))
        self.assertIsNone(self.guard("Bash", {"command": fakes.change(str(self.w.project / ".build/tasks/2/draft.thy"))}))
        owners = json.loads((self.w.state / "tree-owners.json").read_text())
        self.assertEqual(owners, {"theories/Other.thy": "2"})  # .build drafts are nobody's change of the tree

    def test_handoff_is_the_planners(self):
        self.assertIn("HANDOFF.md is the planner's state", self.guard("Bash", {"command": fakes.change("HANDOFF.md")}))

    def test_the_harness_s_own_scripts_are_not_a_session_s_to_run(self):
        # `finalize.py commit ID` would put a task's work in the history with no check and no verdict, and health.py
        # would read it the whole state: a session's interface is v2.py, and show.py for reading (2026-09-21)
        for command in ("python3 .claude/orchestration/finalize.py commit 1",
                        "python3 .claude/orchestration/health.py",
                        "sh .claude/orchestration/base.sh max warm",
                        ".claude/orchestration/watchdog.py"):
            reason = self.guard("Bash", {"command": command}, tool_use="t-new")
            self.assertIsNotNone(reason, f"{command} was allowed")
            self.assertIn("the harness's own to run", reason)
        self.assertIn("the harness's own to run",                      # by its own path as well as by that one
                      self.guard("Bash", {"command": f"python3 {fakes.HERE}/finalize.py check 1"}, tool_use="t-new"))
        for command in (".claude/orchestration/v2.py result 1", ".claude/orchestration/show.py --statement ready",
                        "python3 tools/probe_theories.py Ready --timeout 60", "grep -rn finalize.py .build/tasks/1/",
                        "python3 tools/digest.py x"):   # the repository's own, whatever the harness holds beside it
            self.assertNotIn("the harness's own to run",
                             self.guard("Bash", {"command": command}, tool_use="t-new") or "")

    def test_a_session_starts_no_session_and_waits_through_nothing(self):
        # the Agent tool is refused, and `claude --bg` is the same thing by another door: a session outside every
        # slot, every limit and every record the harness keeps. Monitor is waiting, and reading through its events.
        said = self.guard("Bash", {"command": "claude --bg -n mine 'do the work'"}, tool_use="t-new")
        self.assertIn("A session starts no session", said)
        self.assertIn("Waiting is refused", self.guard("Monitor", {"command": "tail -f x.log"}, tool_use="t-new"))
        # a path that merely names it is not one: the harness's own commands live under .claude
        self.assertIsNone(self.guard("Bash", {"command": ".claude/orchestration/v2.py status"}, tool_use="t-new"))
        self.assertIsNone(self.guard("Bash", {"command": "grep -rn claude .build/tasks/2/notes.md"}, tool_use="t-new"))

    def test_the_harness_s_own_files_are_not_a_session_s_to_change(self):
        # `.claude/` is exempt from the tree's ownership, so a session that edited the harness would change the
        # rules it runs under and nothing would record it (2026-09-21)
        for tool, inp in (("Bash", {"command": fakes.change(str(fakes.HERE / "v2.py"))}),
                          ("Bash", {"command": fakes.change(str(fakes.HERE / "protocols/implementer.md"))}),
                          ("Bash", {"command": f"sed -i s/a/b/ {fakes.HERE}/work_meter.py"})):
            reason = self.guard(tool, inp, tool_use="t-new")
            self.assertIsNotNone(reason, f"{tool} {inp} reached the harness")
            self.assertIn("the owner's", reason)
        # its state and its switches too: removing state/no-launch would start the run again from inside it
        for command in (f"rm {self.w.state}/no-launch", f"echo x > {self.w.state}/graph-held"):
            self.assertIn("the owner's", self.guard("Bash", {"command": command}, tool_use="t-new"))
        # the harness writes its own state through its commands, which never reach this guard, and a draft is its own
        self.assertIsNone(self.guard("Bash", {"command": ".claude/orchestration/v2.py queue 4"}, tool_use="t-new"))
        self.assertIsNone(self.guard("Bash", {"command": fakes.change(str(self.w.project / ".build/tasks/2/draft.md"))},
                                     tool_use="t-new"))

    def test_a_task_file_is_written_by_no_session_at_all(self):
        # "the task graph is the planner's alone to edit" was held over TaskCreate and TaskUpdate, and the list is a
        # directory of JSON files a Write or a redirection reaches as easily — past Claude Code's lock on the task
        # and past the id allocation (2026-09-21)
        graph = self.w.tasks
        for tool, inp in (("Bash", {"command": fakes.change(str(graph / "99.json"))}),
                          ("Bash", {"command": fakes.change(str(graph / "4.json"))}),
                          ("Bash", {"command": f"echo '{{}}' > {graph}/99.json"}),
                          ("Bash", {"command": f"rm {graph}/4.json"})):
            reason = self.guard(tool, inp, tool_use="t-new")
            self.assertIsNotNone(reason, f"{tool} {inp} reached the graph")
            self.assertIn("A task file is not written by hand", reason)
        self.assertIsNone(self.guard("Bash", {"command": fakes.change(str(self.w.project / ".build/tasks/2/x.md"))},
                                     tool_use="t-new"))

    def test_a_check_the_machine_refuses_takes_no_change_of_its_call_with_it(self):
        # implement-189, implement-182 and fix-227 lost the change before their probe with the probe, refused while
        # task 220 waited to measure, and learned so only by looking (fix-227: three requests, 2026-09-22 17:30)
        (self.w.state / "isabelle-exclusive").write_text(json.dumps(
            {"task": "1", "why": "a measurement", "session": "implement-1", "at": time.time()}))
        change = fakes.change((".build/tasks/2/x.md", "drafted\n"))
        probe = "python3 -B tools/probe_theories.py --work .build/tasks/2/p --theory Ready --timeout 60"
        self.assertIsNone(self.guard("Bash", {"command": change + "\n" + probe}))
        command = self.rewritten()["command"]
        self.assertIn("drafted", command)                                  # the change goes through
        self.assertNotIn("probe_theories", command)                        # and only the probe waits
        self.assertIn("Your changes were made; what followed them in this call was not run. Task 1 holds the machine",
                      command)
        self.assertLess(command.index(work_meter.STATUS_LINE), command.index("Your changes were made"))  # if they were
        # a check before the change, or a call without one, is refused whole as before
        self.assertIn("Task 1 holds the machine", self.guard("Bash", {"command": probe + "\n" + change}))
        self.assertIn("Task 1 holds the machine", self.guard("Bash", {"command": probe}))

    def test_no_check_beside_a_measurement_either(self):
        # a run whose result is a timing holds the machine the same way a base-advancing check does
        (self.w.state / "isabelle-exclusive").write_text(json.dumps(
            {"task": "1", "why": "a measurement of the machinery's evaluation", "session": "implement-1",
             "at": time.time()}))
        reason = self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready --timeout 60"})
        self.assertIn("Task 1 holds the machine (a measurement of the machinery's evaluation)", reason)
        self.assertIn("Continue with what needs no check", reason)

    def test_a_heavy_check_let_start_counts_until_the_snapshot_shows_it(self):
        # a sandboxed guard counts the machine's runs from the watchdog's snapshot, and two sessions' checks and a
        # landing check ran together within one snapshot's life, against a limit of two (2026-09-22 05:43, 6 GiB left);
        # the mark counts until the snapshot shows its run — matched by its start, in a session's sandbox (07:55)
        self.w.env["ORCH_ISABELLE_RUNS"] = "1"
        check = "python3 -B tools/incremental_check.py check --output .build/tasks/2/c1"
        self.assertIsNone(self.guard("Bash", {"command": check}))                    # room for one: let start
        mark = self.w.state / "isabelle-admitted" / "session-implement-2"
        self.assertTrue(mark.exists())
        self.w.session("implement-3", "implementer", "s3", task="3")
        other = lambda: ((self.w.hook("work_meter.py", "guard", dict(self.hook(
            "Bash", {"command": check.replace("/2/", "/3/")}, tool_use="t-s3"), session_id="s3"))[1] or {})
            .get("hookSpecificOutput") or {}).get("permissionDecisionReason")
        self.assertIn("2 heavy Isabelle runs", other() or "")                          # counted before it shows
        snap, marked = self.w.state / "isabelle-processes.json", mark.stat().st_mtime
        run = lambda started: {"pid": 7, "kind": "heavy", "started": started, "session": True}
        for roots in ([], [run(marked - 600)]):   # newer, but its run not in it (preparing), or an earlier run only
            snap.write_text(json.dumps({"runs": 1, "heavy": 1, "probes": 0, "roots": roots}))
            os.utime(snap, (marked + 300, marked + 300))
            self.assertIn("2 heavy Isabelle runs", other() or "", roots)              # still counted
        snap.write_text(json.dumps({"runs": 1, "heavy": 1, "probes": 0, "roots": [run(marked + 5)]}))
        os.utime(snap, (marked + 300, marked + 300))                                 # a snapshot that shows it
        self.assertIsNone(other())                                                    # the mark counts no more
        # a check the count let through but another part of the guard refused starts nothing, and is not counted
        mark.unlink()
        self.w.session("implement-2", "implementer", "s1", task="2",
                       fix={"since": time.time() - work_meter.FIX_MINUTES * 60 - 60})
        self.assertIn("quick fix's budget", self.guard("Bash", {"command": check}) or "")
        self.assertFalse(mark.exists())

    def test_a_session_s_check_waits_its_turn_in_the_planner_s_order(self):
        # the machine goes in the planner's order, finalizers included (the owner, 2026-09-22)
        self.w.env["ORCH_ISABELLE_RUNS"] = "0"
        self.w.set_st(queue=["1", "2"])
        (self.w.state / "machine-wait").mkdir()
        (self.w.state / "machine-wait" / "1").write_text(str(time.time()))      # task 1's finalizer waits
        check = "python3 -B tools/incremental_check.py check --output .build/tasks/2/c1"
        self.assertIn("Task 1 waits for a heavy run ahead of yours", self.guard("Bash", {"command": check}) or "")
        # but not while the machine is its own for a measurement: task 1 cannot start before it has run, and fix-274,
        # holding the claim, waited parked behind task 271's finalizer, which waited on that claim (2026-09-22 20:37)
        (self.w.state / "isabelle-exclusive").write_text(json.dumps(
            {"task": "2", "why": "a timing", "pid": None, "session": "implement-2", "at": time.time(), "seen": True}))
        self.assertIsNone(self.guard("Bash", {"command": check}))
        (self.w.state / "isabelle-exclusive").unlink()
        (self.w.state / "machine-wait" / "1").unlink()
        self.assertIsNone(self.guard("Bash", {"command": check}))

    def test_no_check_beside_a_final_check_that_advances_the_base(self):
        (self.w.state / "isabelle-exclusive").write_text(f"1 {os.getpid()}")  # its check is running
        reason = self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready --timeout 60"})
        self.assertIn("Task 1 holds the machine (its final check advances the base heap)", reason)
        (self.w.state / "isabelle-exclusive").unlink()
        self.assertIsNone(self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready --timeout 60"}))


class ChangeGuardTests(Guarded):
    """Files are changed with one command, `v2.py change`, and no other way (the owner, 2026-09-21): the guard reads its
    files from the same blocks the command applies, and refuses a file's content written any other way."""

    def setUp(self):
        super().setUp()
        self.w.session("implement-1", "implementer", "s1", task="1")

    def change(self, blocks, lead=""):
        return {"command": f"{lead}.claude/orchestration/v2.py change <<'EOF'\n{blocks}EOF"}

    def test_a_change_and_the_check_that_needs_it_are_one_call_each_judged_as_what_it_is(self):
        # three of the seventeen sessions of 2026-09-21's night put a probe on the line after their change and lost a
        # request to its refusal; the owner: judge the check as the check it is (2026-09-22)
        probe = "python3 -B tools/probe_theories.py --work .build/tasks/1/probe --timeout {} 2>&1 | tail -40"
        call = self.change("=== write .build/tasks/1/probe/A.thy\ntheory A imports Main begin end\n")["command"]
        self.assertIsNone(self.guard("Bash", {"command": call + "\n" + probe.format(60)}))
        run = work_meter.unwrapped(self.rewritten()["command"])
        self.assertIn(work_meter.STATUS_LINE + "\n" + probe.format(60), run)             # only if the change went through
        self.assertIn("check_errors.py", self.rewritten()["command"])                    # and gathered as a check is
        self.assertIn("A probe gets `--timeout", self.guard("Bash", {"command": call + "\n" + probe.format(900)}))
        self.w.env["ORCH_ISABELLE_RUNS"] = "0"
        self.w.env["ORCH_PROBE_RUNS"] = str(work_meter.v2.PROBE_MAX)                     # the probes full
        self.assertIsNone(self.guard("Bash", {"command": call + "\n" + probe.format(60)}))  # the change goes through,
        self.assertIn("probes are going", self.rewritten()["command"])                 # and only its probe waits
        self.assertNotIn("probe_theories", self.rewritten()["command"])
        self.w.env["ORCH_PROBE_RUNS"] = "0"
        # its change is the change it is: the harness's files refused, its files the task's
        harness = self.change(f"=== write {fakes.HERE / 'x.py'}\nx\n")["command"]
        self.assertIn("owner's", self.guard("Bash", {"command": harness + "\n" + probe.format(60)}))
        self.assertIsNone(self.guard("Bash", {"command": self.change("=== write theories/B.thy\nx\n")["command"]
                                                         + "\n" + probe.format(60)}))
        self.assertEqual(json.loads((self.w.state / "tree-owners.json").read_text()).get("theories/B.thy"), "1")
        # and anything may follow it (the owner, 2026-09-22), running only if the change went through
        self.assertIsNone(self.guard("Bash", {"command": call + "\nsed -n 1p NOTES.md"}))
        self.assertIn(work_meter.STATUS_LINE + "\nsed -n 1p NOTES.md", work_meter.unwrapped(self.rewritten()["command"]))

    def test_where_a_probe_runs_is_recorded_for_its_task(self):
        probe = "python3 -B tools/probe_theories.py --work .build/tasks/named-folder/probe1 --theory A --timeout 60"
        self.assertIsNone(self.guard("Bash", {"command": probe}))
        self.assertIn(os.path.realpath(self.w.project / ".build/tasks/named-folder/probe1"),
                      json.loads((self.w.state / "probes/1/dirs.json").read_text()))

    def test_an_index_edit_writes_its_index_file_and_a_result_s_text_is_data(self):
        # `=== row` and `=== root` write THEORY_MAP.md and ROOT where `=== replace` would name them: the guard, the
        # ownership of the tree and the command read the same paths
        self.assertIsNone(self.guard("Bash", self.change("=== write theories/B.thy\nx\n=== row B\nIts row.\n=== root B\n")))
        owners = json.loads((self.w.state / "tree-owners.json").read_text())
        self.assertEqual((owners.get("THEORY_MAP.md"), owners.get("ROOT")), ("1", "1"))
        # a result given as the command's text is the harness's to write: what it says is not run
        said = self.guard("Bash", {"command": ".claude/orchestration/v2.py result 1 <<'EOF'\nStatus: done\n\n## Produced\n"
                                              "`git commit -m x > THEORY_MAP.md` was not run\nEOF"})
        self.assertIsNone(said)

    def test_what_follows_a_change_runs_in_the_sessions_own_shell_only_if_the_change_went_through(self):
        # Claude Code runs a session's command in zsh, where `status` is read-only: the line put after a change failed
        # there on every call that went on after one, 157 times, while this file ran the rewritten commands in bash
        # (2026-09-21 23:08 to 2026-09-22 10:40)
        change = lambda block: self.change(block, lead=f"{fakes.HERE}/")["command"].replace("/.claude/orchestration/", "/", 1)
        good = change("=== write .build/tasks/1/x.txt\nwritten\n") + "\necho after-the-change"
        bad = change("=== replace .build/tasks/1/x.txt\n<<<<<<< SEARCH\nnot there\n=======\nx\n>>>>>>> REPLACE\n") \
            + "\necho after-the-change"
        for shell in ("zsh", "bash"):
            if not shutil.which(shell):
                continue
            (self.w.project / ".build/tasks/1/x.txt").unlink(missing_ok=True)
            self.assertIsNone(self.guard("Bash", {"command": good}))
            run = subprocess.run([shell, "-c", self.rewritten()["command"]], cwd=self.w.project, capture_output=True,
                                 text=True, timeout=60, env=self.w.env)
            self.assertIn("after-the-change", run.stdout, shell + ": " + run.stdout + run.stderr)
            self.assertNotIn("read-only", run.stdout + run.stderr, shell)
            self.assertEqual((self.w.project / ".build/tasks/1/x.txt").read_text(), "written\n")
            self.assertIsNone(self.guard("Bash", {"command": bad}))
            run = subprocess.run([shell, "-c", self.rewritten()["command"]], cwd=self.w.project, capture_output=True,
                                 text=True, timeout=60, env=self.w.env)
            self.assertNotIn("after-the-change", run.stdout, shell)          # a refused change stops the call
            self.assertIn("refused", run.stdout, shell)

    def test_a_call_too_long_to_start_runs_from_a_file_and_is_recorded_as_made(self):
        # implement-38's change of 59K bytes reached the shell as one argument of 200K, past Linux's 128K, and was
        # refused (E2BIG) without running (2026-09-22)
        text = "".join(f'lemma l{i}: "True" by simp\n' for i in range(1500))
        call = self.change(f"=== write .build/tasks/1/Big.thy\ntheory Big imports Main begin\n{text}end\n",
                           lead=f"{fakes.HERE}/")["command"].replace("/.claude/orchestration/", "/", 1)
        self.assertGreater(len(call), work_meter.ARG_SAFE)
        self.assertIsNone(self.guard("Bash", {"command": call}, tool_use="big"))
        cmd = self.rewritten()["command"]
        self.assertTrue(cmd.startswith(". ") and len(cmd) < 300, cmd[:300])
        run = subprocess.run(["bash", "-c", cmd], cwd=self.w.project, capture_output=True, text=True, timeout=60,
                             env=self.w.env)  # the world's: v2.py writes into its project
        self.assertEqual(run.returncode, 0, run.stdout + run.stderr)
        self.assertIn("lemma l1499", (self.w.project / ".build/tasks/1/Big.thy").read_text())
        _, out, _ = self.w.hook("ctx_gauge.py", "gauge", self.hook("Bash", {"command": cmd}, {"stdout": run.stdout},
                                                                    tool_use="big"))
        note = ((out or {}).get("hookSpecificOutput") or {}).get("additionalContext") or ""
        self.assertNotIn("before the reserve", note)  # recorded as the change it is, not as a read
        self.assertNotIn(f"of {work_meter.ROUNDS} reads", note)
        # a call that fits runs as it is
        self.assertIsNone(self.guard("Bash", {"command": self.change("=== write .build/tasks/1/S.thy\nx\n")["command"]}))
        self.assertFalse((self.rewritten() or {}).get("command", "").startswith(". "))
        # and one of 10K is spilled too: fix-255's change of 23.8K was refused at spawn where 8.1K had started, the
        # sandbox's profile taking the rest of the argument (2026-09-22 19:14)
        mid = self.change("=== write .build/tasks/1/M.thy\n" + "x" * 10_000 + "\n")["command"]
        self.assertIsNone(self.guard("Bash", {"command": mid}, tool_use="mid"))
        self.assertTrue(self.rewritten()["command"].startswith(". "))

    def test_a_probe_in_a_script_of_the_session_s_own_is_the_check_it_runs(self):
        # implement-76 ran its probe as `bash .build/tasks/76/runprobe.sh …` (2026-09-22): read from the command alone
        # it was no check — its change and the probe after it refused in one call, and a probe run so was one the
        # machine's limits and a measurement's claim of the whole machine did not reach
        d, root = self.w.project / ".build/tasks/1", str(self.w.project)
        d.mkdir(parents=True, exist_ok=True)
        script = ("#!/bin/bash\nset -u\nW=.build/tasks/1/probe/$1\nmkdir -p $W\ntimeout 90 python3 -B "
                  "tools/probe_theories.py --work $W --timeout {} > $W/out.txt 2>&1\ngrep -c x $W/out.txt\n")
        (d / "runprobe.sh").write_text(script.format(60))
        (d / "again").write_text("#!/usr/bin/env bash\nbash .build/tasks/1/runprobe.sh a\n")  # by its path, two deep
        (d / "look.sh").write_text("grep -c probe_theories.py NOTES.md\n")                    # reads the tool's name
        run = "bash .build/tasks/1/runprobe.sh a 2>&1 | tail -5"
        self.assertTrue(work_meter.runs_check(run, root))
        self.assertTrue(work_meter.runs_check(".build/tasks/1/again", root))
        self.assertTrue(work_meter.runs_check("cd .build/tasks/1 && bash runprobe.sh a", root))
        self.assertFalse(work_meter.runs_check("bash .build/tasks/1/look.sh", root))
        self.assertFalse(work_meter.runs_check("bash .build/tasks/1/none.sh", root))
        self.assertEqual(work_meter.kind("Bash", {"command": run}, root), "check")
        call = self.change("=== write .build/tasks/1/probe/A.thy\ntheory A imports Main begin end\n")["command"]
        self.assertIsNone(self.guard("Bash", {"command": call + "\n" + run}))        # one call, the check after
        self.assertIn(work_meter.STATUS_LINE + "\n" + run, work_meter.unwrapped(self.rewritten()["command"]))
        (self.w.state / "isabelle-exclusive").write_text(json.dumps(
            {"task": "2", "why": "a measurement of the machinery's evaluation", "session": "implement-2",
             "at": time.time()}))
        self.assertIn("Task 2 holds the machine", self.guard("Bash", {"command": run}))  # the claim reaches it
        (self.w.state / "isabelle-exclusive").unlink()
        (d / "runprobe.sh").write_text(script.format(900))
        self.assertIn("A probe gets `--timeout", self.guard("Bash", {"command": run}))  # and the bound
        (d / "runprobe.sh").write_text(script.format(60) + "git commit -qam probe\n")
        self.assertIn("index and history only by the finalizer", self.guard("Bash", {"command": run}))

    def test_an_in_place_edit_of_a_draft_under_build_stands(self):
        # implement-76's `perl -0pi -e '…' runprobe.sh` on its own draft was refused as an in-place edit whose files
        # could not be read: perl's were not (2026-09-22)
        d, root = self.w.project / ".build/tasks/1", str(self.w.project)
        d.mkdir(parents=True, exist_ok=True)
        (d / "runprobe.sh").write_text("n=$1\n")
        (self.w.project / "theories").mkdir(exist_ok=True)
        (self.w.project / "theories/A.thy").write_text("theory A imports Main begin end\n")
        edit = "cd .build/tasks/1 && perl -0pi -e 's/n=/m=/' runprobe.sh && cat runprobe.sh"
        self.assertEqual(work_meter.write_targets("Bash", {}, edit, root), [str(d / "runprobe.sh")])
        self.assertIsNone(self.guard("Bash", {"command": edit}))
        self.assertIn("Not by an in-place edit", self.guard("Bash", {"command": "perl -pi -e 's/A/B/' theories/A.thy"}))
        self.assertEqual(work_meter.write_targets("Bash", {}, "perl -Mstrict -ne 'print' theories/A.thy", root), [])

    def test_a_change_and_the_unit_tests_that_need_it_are_one_call(self):
        # fix-122's `cd tools && python3 -m unittest …` after its change of tools/incremental_check.py was refused
        # twice (2026-09-22 06:36); unit tests are no Isabelle run, so none of the machine's limits hold them
        call = self.change("=== write .build/tasks/1/probe/a.py\nx = 1\n")["command"]
        tests = "cd tools && timeout 60 python3 -B -m unittest test_check 2>&1 | tail -5"
        self.assertEqual(work_meter.kind("Bash", {"command": call + "\n" + tests}), "write")
        self.w.env["ORCH_ISABELLE_RUNS"] = str(work_meter.v2.ISABELLE_MAX)             # the machine full: no matter
        self.assertIsNone(self.guard("Bash", {"command": call + "\n" + tests}))
        self.assertIn(work_meter.STATUS_LINE + "\n" + tests, work_meter.unwrapped(self.rewritten()["command"]))
        self.assertIsNone(self.guard("Bash", {"command": call + "\npython3 tools/other.py"}))  # any command may follow

    def test_a_change_is_a_write_naming_exactly_its_files(self):
        blocks = ("=== write A.thy\nopen(p, 'w').write(x) > b.md; tools/incremental_check.py check\n"
                  "=== replace ../NOTES.md\n<<<<<<< SEARCH\na\n=======\nb\n>>>>>>> REPLACE\n")
        call = self.change(blocks, lead="cd theories && ")
        self.assertEqual(work_meter.kind("Bash", call), "write")          # the prose inside is neither a check nor
        self.assertEqual(work_meter.write_targets("Bash", call, call["command"], str(self.w.project)),
                         [str(self.w.project / "theories/A.thy"), str(self.w.project / "NOTES.md")])  # a write of b.md
        self.assertIsNone(self.guard("Bash", call))
        self.assertIn("cut.py", self.rewritten()["command"])
        self.assertEqual(work_meter.unwrapped(self.rewritten()["command"]), call["command"])

    def test_its_one_form_is_a_quoted_heredoc_of_its_own(self):
        self.assertIn("Quote the heredoc's delimiter",
                      self.guard("Bash", {"command": ".claude/orchestration/v2.py change <<EOF\n=== write a.md\nx\nEOF"}))
        self.assertIn("takes its changes in a quoted heredoc of the same call",
                      self.guard("Bash", {"command": ".claude/orchestration/v2.py change < changes.txt"}))
        self.assertIsNone(self.guard("Bash", {"command": ".claude/orchestration/v2.py change <<'EOF'\n=== write a.md\nx\n"
                                                         "EOF\nls"}))                   # anything may follow

    def test_a_change_s_text_is_data_and_what_else_the_call_runs_is_still_read(self):
        # fix-48's edit of its commit message named `git rm --cached` and was refused as a git command (2026-09-21)
        text = ("=== write .build/tasks/1/commit.md\nStage `git rm --cached tools/x.pyc`; the run waited (sleep 60) and "
                "wrote .build/tasks/abc.output\n")
        self.assertIsNone(self.guard("Bash", self.change(text)))
        pushed = self.guard("Bash", {"command": self.change(text)["command"] + "\ngit push"})
        self.assertIsNotNone(pushed)                                                # outside the text: still read
        script = "python3 - <<'PY'\nimport subprocess\nsubprocess.run(['sh', '-c', 'git commit -m x'])\nPY"
        self.assertIn("index and history only by the finalizer", self.guard("Bash", {"command": script}))  # it runs

    def test_a_harness_command_s_quoted_words_are_data_and_the_rest_is_read(self):
        # plan-32's question to the owner named `git rm --cached` and was refused as a git command (2026-09-21)
        self.assertIsNone(self.guard("Bash", {"command": '.claude/orchestration/v2.py ledger "Q9: Task 48 would '
                                                         'git rm --cached the tracked object; sleep 60 meanwhile?"'}))
        self.assertIsNotNone(self.guard("Bash", {"command": '.claude/orchestration/v2.py status; git commit -m "x"'}))
        self.assertIsNotNone(self.guard("Bash", {"command": '.claude/orchestration/v2.py ask --to planner '
                                                            '"$(git commit -am x)"'}))  # run from inside the quote

    def test_the_harness_s_commands_that_read_nothing_may_follow_a_change_and_need_it(self):
        # every session that recorded its result lost a request to `change` then `v2.py result` in one call
        good = self.change("=== write .build/tasks/1/result.md\nStatus: done\n")["command"]
        self.assertIsNone(self.guard("Bash", {"command": good + "\n.claude/orchestration/v2.py result 1"}))
        run = work_meter.unwrapped(self.rewritten()["command"])
        self.assertIn(work_meter.STATUS_LINE + "\n.claude/orchestration/v2.py result 1", run)
        self.assertIsNone(self.guard("Bash", {"command": good + "\nsed -n 1p NOTES.md"}))  # a read too, since 09-22
        refused = self.change("=== replace NOTES.md\n<<<<<<< SEARCH\nabsent\n=======\nx\n>>>>>>> REPLACE\n")["command"]
        self.assertIsNone(self.guard("Bash", {"command": refused + '\n.claude/orchestration/v2.py ask --to planner "hi"'}))
        subprocess.run(["bash", "-c", work_meter.unwrapped(self.rewritten()["command"])], cwd=self.w.project,
                       env=dict(self.w.env, **self.w.as_session("s1")), capture_output=True, text=True, timeout=60)
        self.assertEqual(self.w.st().get("asks") or {}, {})                         # the change failed: no question
        # a claim of the machine reads nothing either: implement-56 put one after its change twice (2026-09-21)
        self.assertIsNone(self.guard("Bash", {"command": good + '\n.claude/orchestration/v2.py measuring "a timing"'}))
        # and a question's quoted text may hold `;`, `|` and `&` (investigate-82, 2026-09-22)
        self.assertIsNone(self.guard("Bash", {"command": good + '\n.claude/orchestration/v2.py ask --to planner '
                                                         '"(a) this; (b) that | or & the other?"\n'
                                                         '.claude/orchestration/v2.py park answer'}))

    def test_a_cd_to_its_own_directory_and_a_runner_by_path_are_the_one_form(self):
        # every one-tree session led its changes with `cd <the project>;` (3 of the 4 refusals of the form, 2026-09-21):
        # a cd to where the session already is changes nothing if it fails, so `;` joins it as well as `&&` does
        self.assertIsNone(self.guard("Bash", self.change("=== write a.md\nx\n", lead=f"cd {self.w.project}; ")))
        self.assertIsNone(self.guard("Bash", {"command": "/usr/bin/python3 -B .claude/orchestration/v2.py change "
                                                         "<<'EOF'\n=== write a.md\nx\nEOF"}))
        self.assertIsNone(self.guard("Bash", {"command": self.change("=== write a.md\nx\n", lead=f"cd {self.w.project}; ")
                                                         ["command"] + "\nsed -n 1,2p a.md"}))

    def test_a_change_stands_in_a_call_with_any_other_commands_each_judged_as_alone(self):
        # the owner, 2026-09-22: "why not allow any batch of commands in general" — nine refusals of the form that
        # night, reads, removals and preparations joined to changes
        for lead in ("mkdir -p .build/tasks/1/brief; ", "ls; ", f"cd {self.w.project} && ", "sed -n 1p NOTES.md && "):
            self.assertIsNone(self.guard("Bash", self.change("=== write .build/tasks/1/brief/a.md\nx\n", lead=lead)), lead)
        # a cd elsewhere joined by `;` would leave a change writing elsewhere if it failed
        self.assertIn("joined to it by `&&`", self.guard("Bash", self.change("=== write a.md\nx\n", lead="cd theories; ")))
        change = self.change("=== write .build/tasks/1/a.md\nx\n")["command"]
        probe = "python3 -B tools/probe_theories.py --work .build/tasks/1/probe --timeout {} 2>&1 | tail -5"
        batch = "sed -n 1p NOTES.md\n" + change + "\nls .build/tasks/1\n" + probe.format(60)
        self.assertEqual(work_meter.kind("Bash", {"command": batch}), "check")         # the check it holds decides
        self.assertIsNone(self.guard("Bash", {"command": batch}))
        run = work_meter.unwrapped(self.rewritten()["command"])
        self.assertIn("EOF\n" + work_meter.STATUS_LINE + "\nls .build/tasks/1", run)    # only if the change went through
        self.assertIn("A probe gets `--timeout", self.guard("Bash", {"command": batch.replace("60", "900")}))
        self.w.env["ORCH_PROBE_RUNS"] = str(work_meter.v2.PROBE_MAX)
        self.assertIsNone(self.guard("Bash", {"command": batch}))                       # the machine's limits too:
        self.assertIn("probes are going", self.rewritten()["command"])                 # what follows the change waits
        self.assertNotIn("probe_theories", self.rewritten()["command"])
        self.w.env["ORCH_PROBE_RUNS"] = "0"
        # the rest of the call is judged as it would be alone: its writes and its git
        self.assertIn("Not by a redirection", self.guard("Bash", {"command": change + "\necho x > NOTES.md"}))
        self.assertIn("by the finalizer", self.guard("Bash", {"command": change + "\ngit commit -qam x"}))
        # the harness's commands after a change carry their quoted words as data, as alone
        self.assertIsNone(self.guard("Bash", {"command": change + '\n.claude/orchestration/v2.py ask --to planner '
                                                         '"would git rm --cached x settle it?"'}))
        # two changes in one call: both judged, both the task's
        two = (self.change("=== write theories/B.thy\nx\n")["command"] + "\n"
               + self.change("=== write theories/C.thy\ny\n")["command"])
        self.assertIsNone(self.guard("Bash", {"command": two}))
        owners = json.loads((self.w.state / "tree-owners.json").read_text())
        self.assertEqual((owners.get("theories/B.thy"), owners.get("theories/C.thy")), ("1", "1"))
        self.assertEqual(work_meter.unwrapped(self.rewritten()["command"]).count(work_meter.STATUS_LINE), 1)

    def test_every_other_way_of_writing_a_file_s_content_is_refused_and_pointed_to_it(self):
        for command in ("echo x > NOTES.md", "cat > NOTES.md <<'EOF'\nx\nEOF", "sort a.txt | tee b.txt",
                        "sed -i 's/a/b/' NOTES.md", "perl -pi -e 's/a/b/' NOTES.md",
                        "python3 - <<'EOF'\nopen('NOTES.md', 'w').write('x')\nEOF",
                        "python3 tools/probe_theories.py Ready --timeout 60 > theories/probe.log 2>&1",       # a check's too
                        "ls &> theories/list.txt",
                        "echo x > .build/outputs/implement-1/commands/1.sh"):     # the harness's record of the session
            refused = self.guard("Bash", {"command": command})
            self.assertIsNotNone(refused, command)
            self.assertIn("Files are changed with `.claude/orchestration/v2.py change", refused, command)
        self.assertIn("is in task 4's own tree",  # a tree's own files are its task's, whatever the form
                      self.guard("Bash", {"command": "cat > .build/trees/4/theories/A.thy <<'EOF'\nx\nEOF"}))
        # a program's output, or a draft, may be written under .build/: generated data pasted through `v2.py change`
        # would have been the only way (found 2026-09-21, in the pass over what the restrictions left undoable)
        for command in ("cp theories/Base.thy .build/tasks/1/Base.thy", "mv .build/tasks/1/a .build/tasks/1/b",
                        "mkdir -p .build/tasks/1/d", "rm -f .build/tasks/1/x", "ls > /dev/null",
                        "grep -n x NOTES.md 2>&1 | head", "ls theories 2>/dev/null",
                        "python3 tools/probe_theories.py Ready --timeout 60 > .build/tasks/1/probe.log 2>&1",
                        "python3 - > .build/tasks/1/rows.json <<'EOF'\nprint(1)\nEOF", "ls | tee .build/tasks/1/ls.txt",
                        "ls &> .build/tasks/1/ls.txt",
                        "echo $((3 > 2))", "[[ a > b ]] && ls"):                   # a comparison is no redirection
            self.assertIsNone(self.guard("Bash", {"command": command}), command)
        p = Path(work_meter.v2.PROJECT)  # the check itself, in this process's project
        self.assertEqual([work_meter.scratch(str(p / x)) for x in (
            ".build/tasks/1/d.json", ".build/trees/4/.build/tasks/4/n.md", ".build/trees/4/theories/A.thy",
            ".build/outputs/implement-1/1.txt", "theories/A.thy")], [True, True, False, False, False])  # a tree's .build

    def test_git_s_reading_forms_stand_and_its_changing_forms_do_not(self):
        for command in ("git stash list", "git stash show -p", "git worktree list", "git tag", "git tag -l", "git tag | head",
                        "git notes show HEAD", "git log --oneline -3", "git diff --stat"):
            self.assertIsNone(self.guard("Bash", {"command": command}), command)
        for command in ("git stash", "git stash pop", "git worktree add x", "git tag v1", "git tag -d v1", "git notes add"):
            self.assertIn("no session stages, commits, stashes", self.guard("Bash", {"command": command}), command)

    def test_where_it_writes_is_judged_before_how(self):
        # told the harness is the owner's, not told to try again with `v2.py change` and be refused for that
        self.assertIn("The orchestration's own files are the owner's",
                      self.guard("Bash", {"command": f"sed -i 's/a/b/' {fakes.HERE / 'v2.py'}"}))
        self.assertIn("HANDOFF.md is the planner's state", self.guard("Bash", {"command": "echo x >> HANDOFF.md"}))
        self.assertIn("HANDOFF.md is the planner's state", self.guard("Bash", self.change("=== write HANDOFF.md\nx\n")))

    def test_a_check_is_run_to_list_every_error_from_where_it_logs(self):
        probe = "cd theories && python3 ../tools/probe_theories.py --work ../.build/tasks/1/probe --theory Ready --timeout 60"
        self.assertIsNone(self.guard("Bash", {"command": probe}))
        command = self.rewritten()["command"]
        self.assertIn(f"check_errors.py --watch {self.w.project / '.build/tasks/1/probe'} --keep "
                      f"{self.w.project / '.build/outputs/implement-1'} -- bash -c", command)
        self.assertIn(f"cut.py {work_meter.READ_BYTES} tail", command)
        self.assertEqual(work_meter.unwrapped(command), probe)
        check = {"command": "python3 -B tools/incremental_check.py check --output=.build/c1", "run_in_background": True}
        self.assertIsNone(self.guard("Bash", check))
        command = self.rewritten()["command"]
        self.assertIn(f"--watch {self.w.project / '.build/c1'} --keep", command)
        self.assertNotIn("cut.py", command)                                    # its output goes to its own file
        self.assertEqual(work_meter.unwrapped(command), check["command"])
        read = {"command": "python3 - <<'EOF'\nprint(open('tools/incremental_check.py').read()[:100])\nEOF"}
        self.assertEqual(work_meter.kind("Bash", read), "other")              # prose naming a check is no check
        note = {"command": "cat > .build/tasks/1/n.md <<'EOF'\npython3 -B tools/incremental_check.py check --output x\nEOF"}
        self.assertEqual(work_meter.kind("Bash", note), "write")              # nor is a heredoc's line that is one

    def test_a_probe_reports_every_failing_proof_of_a_theory_in_one_run(self):
        # in place (--parallel-proofs 0) a probe stops at the first proof that fails: implement-221 found three of one
        # theory in three probes (2026-09-22); forked, every one comes in one run, in the same seconds
        probe = "python3 -B tools/probe_theories.py --work .build/tasks/1/p --theory Ready --parallel-proofs 0 --timeout 60"
        self.assertIsNone(self.guard("Bash", {"command": probe}))
        command = self.rewritten()["command"]
        self.assertEqual(work_meter.unwrapped(command), probe.replace(" --parallel-proofs 0", ""))
        self.assertIn(f"--note {shlex.quote(work_meter.FORKED_NOTE)}", command)  # and it is told so, and how to ask
        # in place stays for what it is for: which proof does not return
        self.assertIsNone(self.guard("Bash", {"command": "IN_PLACE=1 " + probe}))
        self.assertEqual(work_meter.unwrapped(self.rewritten()["command"]), "IN_PLACE=1 " + probe)
        # what a heredoc says is data, as it is
        change = self.change("=== write .build/tasks/1/n.md\nprobe with --parallel-proofs 0 in place\n")["command"]
        self.assertIsNone(self.guard("Bash", {"command": change + "\n" + probe}))
        command = work_meter.unwrapped(self.rewritten()["command"])
        self.assertIn("\nprobe with --parallel-proofs 0 in place\nEOF\n", command)
        self.assertTrue(command.endswith("\n" + probe.replace(" --parallel-proofs 0", "")), command)

    def test_stopping_its_own_job_is_neither_refused_nor_counted(self):
        self.assertEqual(work_meter.kind("TaskStop", {"task_id": "b1"}), "own")
        self.assertIn("TaskStop", work_meter.UNGUARDED_TOOLS)


class AgainTests(Guarded):
    """A command that went wrong is fixed, not written again (the owner, 2026-09-21): every command is kept, numbered,
    and `v2.py again N` sends only its correction, which the guard applies and guards as if it had been typed."""

    def setUp(self):
        super().setUp()
        self.w.session("implement-1", "implementer", "s1", task="1")
        self.w.write("NOTES.md", "a note\n")

    def kept(self, n):
        path = self.w.project / f".build/outputs/implement-1/commands/{n}.sh"
        return path.read_text() if path.exists() else None

    def again(self, n, blocks, tool_use="a"):
        return self.guard("Bash", {"command": f".claude/orchestration/v2.py again{' ' + str(n) if n else ''} <<'EOF'\n"
                                              f"{blocks}EOF"}, tool_use=tool_use)

    def run_rewritten(self):
        return subprocess.run(["bash", "-c", self.rewritten()["command"]], cwd=self.w.project, capture_output=True,
                              text=True, timeout=60)

    def test_every_command_is_kept_numbered_and_a_refused_one_says_how_to_fix_it(self):
        self.assertIsNone(self.guard("Bash", {"command": "ls theories"}, tool_use="k1"))
        refused = self.guard("Bash", {"command": "echo more >> NOTES.md"}, tool_use="k2")
        self.assertEqual((self.kept(1), self.kept(2)), ("ls theories", "echo more >> NOTES.md"))  # refused, kept too
        self.assertIn("[kept as command 2: when the command is what is wrong, send the correction and not the command "
                      "again — `.claude/orchestration/v2.py again 2 <<'EOF'`", refused)
        self.assertNotIn("kept as command", self.guard("Bash", {"command": "sleep 60"}, tool_use="k3"))  # not its fault

    def test_again_runs_the_kept_command_fixed_as_if_it_had_been_typed(self):
        script = "python3 - <<'PY'\nimport json\nfor n in range(3):\n    print('row', n, jsn.dumps({'n': n}))\nPY"
        self.assertIsNone(self.guard("Bash", {"command": script}, tool_use="s1"))
        self.assertIn("NameError", self.run_rewritten().stderr + self.run_rewritten().stdout)
        self.assertIsNone(self.again(1, "<<<<<<< SEARCH\njsn.dumps\n=======\njson.dumps\n>>>>>>> REPLACE\n"))
        fixed = script.replace("jsn.", "json.")
        self.assertEqual(work_meter.unwrapped(self.rewritten()["command"]), fixed)  # the correction alone was sent
        self.assertEqual(self.kept(2), fixed)                                      # kept as the next command
        self.assertIn('row 2 {"n": 2}', self.run_rewritten().stdout)
        self.assertIsNone(self.again(None, ""))                                    # the last, as it was
        self.assertEqual(work_meter.unwrapped(self.rewritten()["command"]), fixed)
        self.guard("Bash", {"command": "sed -n '1,1p' NOTES.md"})                   # a read no cut rewrites
        self.assertIsNone(self.again(None, "<<<<<<< SEARCH\nNOTES.md\n=======\nREADME.md\n>>>>>>> REPLACE\n"))
        self.assertEqual(self.rewritten()["command"], "sed -n '1,1p' README.md")  # still run, as fixed

    def test_again_alone_runs_the_command_as_it_was_and_a_change_it_needs_is_a_call_before_it(self):
        # the planner, 2026-09-21: `again 30` alone refused for its form, then a change and its `again` in one call
        # refused without being told how to batch them — two requests spent on the form
        self.guard("Bash", {"command": "echo one"}, tool_use="b1")
        self.assertIsNone(self.guard("Bash", {"command": ".claude/orchestration/v2.py again 1"}, tool_use="b2"))
        self.assertEqual(work_meter.unwrapped(self.rewritten()["command"]), "echo one")
        self.assertEqual(self.kept(2), "echo one")                                  # kept as the next command
        self.assertIsNone(self.guard("Bash", {"command": "python3 .claude/orchestration/v2.py again"}, tool_use="b3"))
        self.assertEqual(work_meter.unwrapped(self.rewritten()["command"]), "echo one")  # the last, N left out
        both = (".claude/orchestration/v2.py change <<'EOF'\n=== write .build/plans/plan-1/b1.md\nx\nEOF\n"
                ".claude/orchestration/v2.py again 1")
        said = self.guard("Bash", {"command": both}, tool_use="b4")
        self.assertIn("the call holds nothing else", said)
        self.assertIn("a call of its own before it in the same request", said)
        self.assertIn("Quote the heredoc's delimiter",                             # still said with a heredoc
                      self.guard("Bash", {"command": ".claude/orchestration/v2.py again 1 <<EOF\nx\nEOF"}))

    def test_again_by_a_runner_given_by_its_path_runs(self):
        # ask-q23 wrote `/usr/bin/python3 …/v2.py again 6`, refused as out of form (2026-09-21)
        self.guard("Bash", {"command": "echo one"}, tool_use="p1")
        self.assertIsNone(self.guard("Bash", {"command": "/usr/bin/python3 .claude/orchestration/v2.py again 1"},
                                     tool_use="p2"))
        self.assertEqual(work_meter.unwrapped(self.rewritten()["command"]), "echo one")

    def test_a_correction_of_a_change_may_hold_its_marker_lines(self):
        # fix-48's correction of its change was refused: a change's own lines are marker lines (2026-09-21)
        self.guard("Bash", {"command": ".claude/orchestration/v2.py change <<'EOF'\n=== write a.md\nold\nEOF"},
                   tool_use="m1")
        self.assertIsNone(self.again(1, "<<<<<<< SEARCH\nold\n=======\n=======\n>>>>>>> REPLACE\n", tool_use="m2"))
        self.assertIn("=== write a.md\n=======\nEOF", work_meter.unwrapped(self.rewritten()["command"]))

    def test_what_again_makes_is_guarded_as_if_typed(self):
        self.guard("Bash", {"command": "ls theories"})
        refused = self.again(1, "<<<<<<< SEARCH\nls theories\n=======\necho x > NOTES.md\n>>>>>>> REPLACE\n")
        self.assertIn("Files are changed with `.claude/orchestration/v2.py change", refused)
        self.assertEqual(self.kept(2), "echo x > NOTES.md")                         # kept as what it would have run

    def test_a_live_session_keeps_its_newest_commands_and_a_released_one_nothing(self):
        for i in range(work_meter.KEPT_COMMANDS + 5):
            self.guard("Bash", {"command": f"ls {i}"}, tool_use=f"p{i}")
        folder = self.w.project / ".build/outputs/implement-1/commands"
        self.assertEqual(sorted(int(f.stem) for f in folder.iterdir()), list(range(6, work_meter.KEPT_COMMANDS + 6)))
        self.assertEqual(self.kept(work_meter.KEPT_COMMANDS + 5), f"ls {work_meter.KEPT_COMMANDS + 4}")  # numbered on
        self.w.write(".build/outputs/implement-1/1.txt", "a kept output\n")
        (self.w.state / "work-s1.json").write_text("{}")
        (self.w.state / "work-s1.json.lock").write_text("")
        subprocess.run([sys.executable, "-c", f"import sys; sys.path.insert(0, {str(fakes.HERE)!r}); import v2; "
                        "v2.release('implement-1')"], env=self.w.env, check=True)
        self.assertFalse((self.w.project / ".build/outputs/implement-1").exists())  # outputs, commands, lists
        self.assertFalse((self.w.state / "work-s1.json").exists())                   # the reads it held
        self.assertFalse((self.w.state / "work-s1.json.lock").exists())

    def test_again_is_refused_loudly_and_runs_nothing(self):
        self.guard("Bash", {"command": "ls theories"})
        self.assertIn("No command 7 of yours is kept", self.again(7, ""))
        said = self.again(1, "<<<<<<< SEARCH\nls theory\n=======\nls\n>>>>>>> REPLACE\n<<<<<<< SEARCH\nnope\n=======\n"
                             "x\n>>>>>>> REPLACE\n")
        self.assertIn("Nothing was run: command 1 could not be fixed so", said)
        self.assertIn("change 1 (replace command 1): its SEARCH text occurs 0 times in the command 1", said)
        self.assertIn("change 2 (replace command 1): its SEARCH text occurs 0 times in the command 1", said)  # each
        self.assertIn("Quote the heredoc's delimiter",
                      self.guard("Bash", {"command": ".claude/orchestration/v2.py again 1 <<EOF\nEOF"}))
        self.assertIsNone(self.kept(2))                                             # a refused `again` is kept as nothing

    def test_a_failing_command_shows_its_end_where_the_failure_is(self):
        script = "python3 -c 'print(\"\\n\".join(map(str, range(3000)))); raise KeyError(\"native field\")'"
        self.guard("Bash", {"command": script})
        run = self.run_rewritten()
        self.assertEqual(run.returncode, 1)
        self.assertIn("it shows its last lines", run.stdout)
        self.assertIn("KeyError: 'native field'", run.stdout)                   # the end, not the head
        self.assertNotIn("\n1\n2\n", run.stdout)

    def test_a_search_that_found_nothing_is_not_told_it_failed(self):
        self.guard("Bash", {"command": "grep -n nowhere NOTES.md"})
        run = self.run_rewritten()
        self.assertEqual(run.returncode, 1)
        self.assertNotIn("If it failed", run.stdout)

    def test_a_command_that_ended_failing_is_told_its_number_but_a_check_is_not(self):
        self.guard("Bash", {"command": "python3 -c 'import sys; print(1); sys.exit(3)'"})
        run = self.run_rewritten()
        self.assertEqual(run.returncode, 3)
        self.assertIn("[command 1 ended with status 3. If it failed, send the correction and not the command again: "
                      "`.claude/orchestration/v2.py again 1 <<'EOF'`", run.stdout)
        self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready --timeout 60"})
        self.assertNotIn(f"cut.py {work_meter.READ_BYTES} tail " + str(self.w.project / ".build/outputs/implement-1") + " 2",
                         self.rewritten()["command"])                                # a check's fault is elsewhere
        self.w.write("NOTES.md", "a note\n")
        self.guard("Bash", {"command": ".claude/orchestration/v2.py change <<'EOF'\n=== replace NOTES.md\n"
                                       "<<<<<<< SEARCH\nno such\n=======\nx\n>>>>>>> REPLACE\nEOF"})
        run = subprocess.run(["bash", "-c", self.rewritten()["command"].replace(
            ".claude/orchestration/v2.py", f"{sys.executable} {fakes.HERE / 'v2.py'}")], cwd=self.w.project,
            capture_output=True, text=True, env=self.w.env, timeout=60)
        self.assertEqual(run.returncode, 1)                                        # a refused change reads as failing
        self.assertIn("[command 3 ended with status 1. If it failed, send the correction", run.stdout)


class TreeGuardTests(Guarded):
    """A task's own tree is its own, and the one tree is written only by the tasks that work in it. The library a
    session holds names the repository's own directory by absolute path: a session in a tree that wrote there would
    install its work in the one tree, owned there by its task — which would then work there and hold the tree against
    every other, the very thing a tree of its own exists to end (2026-09-21)."""

    def setUp(self):
        super().setUp()
        self.tree = self.w.project / ".build/trees/2"
        self.tree.mkdir(parents=True)
        self.w.session("implement-2", "implementer", "s1", task="2", tree=".build/trees/2")
        self.w.session("implement-3", "implementer", "s3", task="3")

    def guard_as(self, session, cwd, tool, inp):
        hook = dict(self.hook(tool, inp, tool_use=f"t-{session}"), session_id=session,
                    cwd=str(cwd))
        _, out, err = self.w.hook("work_meter.py", "guard", hook)
        self.assertEqual(err, "")
        said = (out or {}).get("hookSpecificOutput") or {}
        return said.get("permissionDecisionReason") if said.get("permissionDecision") == "deny" else None

    def test_the_repository_s_check_of_a_task_in_its_tree_is_asked_of_the_harness(self):
        # every task ran the repository's check on its own, and 27 of 69 were refused for the machine and tried again
        # (2026-09-22): the harness runs it once for every task waiting (v2.py check, train.Batch)
        self.w.env.update(ORCH_TREES="1", ORCH_BATCHES="1")
        check = {"command": "python3 -B tools/incremental_check.py check --output .build/tasks/2/check"}
        said = self.guard_as("s1", self.tree, "Bash", check)
        self.assertIn("ask for it with `.claude/orchestration/v2.py check`", said)
        probe = {"command": "python3 tools/probe_theories.py --work .build/tasks/2/probe --load Ready --timeout 60"}
        self.assertIsNone(self.guard_as("s1", self.tree, "Bash", probe))      # probes are the session's own
        self.assertNotIn("v2.py check", self.guard_as("s3", self.w.project, "Bash", check) or "")  # the one tree's
        self.w.env["ORCH_BATCHES"] = "0"
        self.assertNotIn("v2.py check", self.guard_as("s1", self.tree, "Bash", check) or "")

    def test_a_session_in_its_tree_writes_there_and_not_in_the_one_tree(self):
        self.assertIsNone(self.guard_as("s1", self.tree, "Bash", {"command": fakes.change(str(self.tree / "theories/Ready.thy"))}))
        self.assertIsNone(self.guard_as("s1", self.tree, "Bash", {"command": fakes.change("ROOT")}))  # where it stands
        self.assertIsNone(self.guard_as("s1", self.tree, "Bash",  # a draft: the one .build is everyone's
                                        {"command": fakes.change(str(self.w.project / ".build/tasks/2/draft.thy"))}))
        refused = self.guard_as("s1", self.tree, "Bash", {"command": fakes.change(str(self.w.project / "theories/Ready.thy"))})
        self.assertIn("You work in your task's own tree, .build/trees/2", refused)
        self.assertIn("Write .build/trees/2/theories/Ready.thy", refused)
        owners = self.w.state / "tree-owners.json"
        self.assertEqual(json.loads(owners.read_text()) if owners.exists() else {}, {})  # nothing of the one tree

    def test_a_session_does_not_write_its_tree_s_copy_of_the_harness(self):
        # its hooks run that copy: one that removed the hand-over to the one harness would run under its own rules
        refused = self.guard_as("s1", self.tree, "Bash",
                                {"command": fakes.change(str(self.tree / ".claude/orchestration/work_meter.py"))})
        self.assertIn("The orchestration's own files are the owner's", refused)

    def test_no_session_writes_another_task_s_tree(self):
        target = {"command": fakes.change(str(self.tree / "theories/Ready.thy"))}
        self.assertIn("is in task 2's own tree", self.guard_as("s3", self.w.project, "Bash", target))
        self.assertIsNone(self.guard_as("s3", self.w.project, "Bash",  # the one tree is still its own to write
                                        {"command": fakes.change(str(self.w.project / "theories/Other.thy"))}))


class RoundsTests(unittest.TestCase):
    def test_reading_requests_count_each_batch_once_and_nothing_else(self):
        with _World() as w:
            t = time.time()
            call = lambda i, name="Read", inp=None: {"type": "tool_use", "id": i, "name": name, "input": inp or {}}
            path = w.transcript("s", [
                assistant("old", fakes.iso(t - 5), [call("r0")]),                                # before the moment
                assistant("a", fakes.iso(t + 1), [call("r1"), call("r2", "Grep")]),              # a batch of two
                assistant("a", fakes.iso(t + 1.1), [call("r3", "Bash", {"command": "cat x"})]),  # the same batch
                assistant("b", fakes.iso(t + 2), [call("w1", "Edit")]),                          # a write
                assistant("c", fakes.iso(t + 3), [call("o1", "Bash", {"command": "v2.py ask --to kb x"})]),  # own
                assistant("h", fakes.iso(t + 3.5), [call("g1", "Bash", {"command": "v2.py read x"})]),  # a read
                assistant("d", fakes.iso(t + 4), [call("s1", "TaskStop")]),                      # never guarded
                assistant("e", fakes.iso(t + 5), [call("r4")]),                                  # refused, below
                assistant("f", fakes.iso(t + 6)),                                                # text alone
                assistant("g", fakes.iso(t + 7), [call("r5", "Bash", {"command": "python3 x.py"})])])  # other: reads
            since = fakes.iso(t)
            self.assertEqual(work_meter.reading_requests(path, since, refused=["r4"]), 3)  # a, h and g
            self.assertEqual(work_meter.reading_requests(path, since), 4)                  # and e
            self.assertEqual(work_meter.reading_requests(path, since, ["r4"], "r5"), 3)    # g makes the call
            self.assertEqual(work_meter.reading_requests(path, since, ["r4"], "new"), 4)   # not written yet
            self.assertEqual(work_meter.reading_requests(path, None, [], "new"), 0)
            self.assertEqual(work_meter.batch_id(path, "r3"), "a")                        # a call's batch
            self.assertIsNone(work_meter.batch_id(path, "nowhere", wait=0.2))            # not placed: none

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

    def test_a_guard_that_fails_says_so_rather_than_letting_the_call_through_in_silence(self):
        # it lets the call through by design; doing it silently is every limit and every refusal switched off with
        # nothing to show for it, which is the PreToolUse matcher's fault in another form (2026-09-20)
        w = fakes.World()
        try:
            w.session("implement-4", "implementer", "s1", task="4")
            code, out, err = w.run("work_meter.py", "guard", stdin="not json at all")
            self.assertEqual((code, out.strip()), (0, ""))      # the call goes through
            self.assertIn("the guard failed and let the call through",
                          (w.state / "v2.log").read_text())     # and it is said
            before = (w.state / "v2.log").read_text().count("the guard failed")
            w.run("work_meter.py", "guard", stdin="still not json")
            self.assertEqual((w.state / "v2.log").read_text().count("the guard failed"), before)  # not every call
        finally:
            w.close()

    def test_the_settings_let_every_guarded_tool_reach_the_guard(self):
        for settings in ("planner-settings.json", "worker-settings.json"):
            matcher = self.matcher(settings)
            for tool in work_meter.GUARDED_TOOLS:
                self.assertTrue(re.search(matcher, tool),
                                f"{tool} never reaches the guard in {settings}: the matcher is {matcher!r}, so the "
                                f"guard's refusals and records for it simply do not happen")

    def test_both_settings_files_wire_the_same_hooks_to_the_same_scripts(self):
        # the guard is one of five hooks, and the others are what deliver mail, hold a turn, catch a compaction and
        # record the owner's words. One missing from one file is that role's turn control simply gone, in silence
        wiring = []
        for settings in ("planner-settings.json", "worker-settings.json"):
            hooks = json.load(open(HERE / settings))["hooks"]
            wiring.append({event: sorted(h["hooks"][0]["command"].split("/orchestration/")[-1] + f" [{h.get('matcher')}]"
                                         for h in entries) for event, entries in hooks.items()})
        self.assertEqual(wiring[0], wiring[1], "the planner's settings and the workers' have drifted apart")
        for event in ("PreToolUse", "PostToolUse", "Stop", "PreCompact", "UserPromptSubmit"):
            self.assertIn(event, wiring[0], f"{event} is wired in neither settings file")

    def test_the_guarded_tools_are_the_ones_the_guard_itself_names(self):
        # a tool given a branch in kind() or in session_guard() and left out of GUARDED_TOOLS would be left out of
        # the matcher too, and nothing above would notice
        source = inspect.getsource(work_meter.kind) + inspect.getsource(work_meter.session_guard)
        named = {n for n in re.findall(r"""['"]([A-Z][A-Za-z]+)['"]""", source)}
        self.assertEqual(named | set(work_meter.REMOVED_TOOLS), set(work_meter.GUARDED_TOOLS) | set(work_meter.UNGUARDED_TOOLS),
                         "the tools the guard names and the tools it declares it guards have drifted apart")
        self.assertIn("REMOVED_TOOLS", inspect.getsource(work_meter._guard))  # the removed ones, refused there

    def test_the_removed_tools_are_in_no_session_and_refused_to_every_role(self):
        # the owner, 2026-09-21: no hook can bound what they show, so no base and no fork has them
        flags = (fakes.HERE / "session-flags").read_text().split()
        tools = flags[flags.index("--tools") + 1:]
        tools = tools[:next((i for i, t in enumerate(tools) if t.startswith("--")), len(tools))]
        self.assertEqual(set(tools), {"Bash", "TaskCreate", "TaskUpdate", "TaskStop"})
        self.assertEqual(set(tools) & set(work_meter.REMOVED_TOOLS), set())
        self.assertTrue(set(work_meter.REMOVED_TOOLS) >= {"Grep", "Glob", "WebFetch", "WebSearch", "Read", "Edit", "Write",
                                                          "Agent", "TaskOutput", "Monitor", "ToolSearch"})
        w = fakes.World()
        self.addCleanup(w.close)
        for role, name in (("implementer", "implement-1"), ("planner", "plan-1"), ("kb", "kb-1"), ("reviewer", "review-1")):
            w.session(name, role, f"s-{name}", task="1")
            for tool in work_meter.REMOVED_TOOLS:
                _, out, _ = w.hook("work_meter.py", "guard", {
                    "session_id": f"s-{name}", "tool_name": tool, "tool_input": {"file_path": "HANDOFF.md", "query": "q"},
                    "cwd": str(w.project), "transcript_path": "", "tool_use_id": "t", "hook_event_name": "PreToolUse"})
                reason = (out or {}).get("hookSpecificOutput", {}).get("permissionDecisionReason", "")
                self.assertIn(f"{tool} is not a session's tool", reason, (role, tool))
                self.assertIn(REMOVED_SAID[tool], reason)  # and where its work goes


class _World:
    def __enter__(self):
        self.w = fakes.World()
        return self.w

    def __exit__(self, *exc):
        self.w.close()


if __name__ == "__main__":
    unittest.main()
