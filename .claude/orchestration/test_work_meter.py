"""The guards (work_meter.py guard, a PreToolUse hook) and what a worker reads and produces (recorded by the gauge's
PostToolUse call), run as the hooks run, in a throwaway world (fakes.py)."""
import inspect
import json
import os
import re
from pathlib import Path
import subprocess
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
        self.last = (out or {}).get("hookSpecificOutput") or {}
        return self.last.get("permissionDecisionReason") if self.last.get("permissionDecision") == "deny" else None

    def rewritten(self):
        """The input the last guarded call runs with, when the guard rewrote it."""
        return self.last.get("updatedInput")

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
        check = {"command": "python3 tools/probe_theories.py Ready"}
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
        self.assertIn("one read shows at most", self.call("Bash", {"command": "sed -n '1,2000p' theories/Other.thy"})[0])

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

    def test_a_read_of_a_file_longer_than_a_read_shows_is_refused_with_the_lines_that_fit(self):
        refused, _ = self.call("Bash", {"command": "sed -n '1,1000p' theories/Other.thy"})
        self.assertIn(f"one read shows at most {work_meter.READ_BYTES:,}", refused)
        fits = work_meter.fitting(str(self.w.project / "theories/Other.thy"), 1)
        self.assertIn(f"lines 1-{fits} fit: read them (`sed -n '1,{fits}p' theories/Other.thy`", refused)
        self.assertLessEqual(work_meter.read_size(str(self.w.project / "theories/Other.thy"), 1, fits),
                             work_meter.READ_BYTES)
        self.assertGreater(work_meter.read_size(str(self.w.project / "theories/Other.thy"), 1, fits + 1),
                           work_meter.READ_BYTES)
        self.assertIsNone(self.call("Bash", {"command": f"sed -n '1,{fits}p' theories/Other.thy"},
                                    {"stdout": "x"})[0])  # what fits is read
        self.at = fits
        self.assertIn(f"2 of {work_meter.ROUNDS} reads", self.read()[1])  # and the two refusals cost nothing
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
        for inp in ({"command": "python3 tools/probe_theories.py Ready"},        # a check: its end
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

    def test_a_batch_reads_at_most_its_bytes_and_the_rest_goes_in_the_next(self):
        big = ("Bash", {"command": "grep -rn other theories"}, {"stdout": "z" * work_meter.READ_BYTES})
        per = work_meter.BATCH // work_meter.READ_BYTES
        out = self.call(*big, *([big] * (per + 1)))
        self.assertTrue(all(refused is None for refused, _ in out[:per]))
        self.assertIn(f"a batch reads at most {work_meter.BATCH // 1000}K", out[per][0])
        self.assertIsNotNone(out[per + 1][0])
        self.assertIn(f"2 of {work_meter.ROUNDS} reads", self.read()[1])  # the next batch reads; the refusals cost none

    def test_a_cut_that_did_not_take_is_said(self):
        # the rewrite is Claude Code's to apply; a read that comes back longer than a read shows says it did not
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
        self.assertIsNotNone(self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready"}, tool_use="t-new"))
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
        self.assertIsNone(self.guard("Bash", {"command": fakes.change(str(self.w.project / ".build/tasks/1/result.md"))}, tool_use="t-new"))
        self.assertIsNotNone(self.guard("Bash", {"command": fakes.change(str(self.thy))}, tool_use="t-new"))

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

    def test_a_session_with_nothing_left_but_the_tree_parks_and_the_slot_is_free(self):
        self.w.set_st(tasks={"1": {"stage": "checking"}, "2": {"stage": "running", "session": "implement-2"}})
        out = self.w.v2("park", "tree", env=self.w.as_session("s1"))
        self.assertIn("resumed here, your context intact, when task 1 has let the working tree go", out)
        self.assertEqual(self.w.st()["sessions"]["implement-2"]["state"], "parked")
        self.assertIsNone(self.w.hook("ctx_gauge.py", "stop", {"session_id": "s1", "hook_event_name": "Stop"})[1])
        self.assertIn("You are parked", self.guard("Bash", {"command": "cat ROOT"}))

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
                        "python3 tools/probe_theories.py Ready", "grep -rn finalize.py .build/tasks/1/",
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


class ChangeGuardTests(Guarded):
    """Files are changed with one command, `v2.py change`, and no other way (the owner, 2026-09-21): the guard reads its
    files from the same blocks the command applies, and refuses a file's content written any other way."""

    def setUp(self):
        super().setUp()
        self.w.session("implement-1", "implementer", "s1", task="1")

    def change(self, blocks, lead=""):
        return {"command": f"{lead}.claude/orchestration/v2.py change <<'EOF'\n{blocks}EOF"}

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
        for command in (".claude/orchestration/v2.py change < changes.txt",
                        ".claude/orchestration/v2.py change <<'EOF'\n=== write a.md\nx\nEOF\nls"):
            self.assertIn("takes its changes in a quoted heredoc of the same call", self.guard("Bash", {"command": command}))

    def test_every_other_way_of_writing_a_file_s_content_is_refused_and_pointed_to_it(self):
        for command in ("echo x > NOTES.md", "cat > NOTES.md <<'EOF'\nx\nEOF", "sort a.txt | tee b.txt",
                        "sed -i 's/a/b/' NOTES.md", "perl -pi -e 's/a/b/' NOTES.md",
                        "python3 - <<'EOF'\nopen('NOTES.md', 'w').write('x')\nEOF",
                        "python3 tools/probe_theories.py Ready > theories/probe.log 2>&1",       # a check's too
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
                        "python3 tools/probe_theories.py Ready > .build/tasks/1/probe.log 2>&1",
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
        probe = "cd theories && python3 ../tools/probe_theories.py --work ../.build/tasks/1/probe --theory Ready"
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
        self.guard("Bash", {"command": "python3 tools/probe_theories.py Ready"})
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
        self.assertIn("REMOVED_TOOLS", inspect.getsource(work_meter.guard))  # the removed ones, refused there

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
