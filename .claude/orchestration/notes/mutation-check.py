"""Break one repair at a time and see whether the test meant to catch it does.

Not part of the harness and nothing runs it automatically: it is the check that found, on 2026-09-21, that
two of the day's repairs were held by nothing and that a third had a branch nothing could reach. Run it from
.claude/orchestration after changing any of the repairs it names, and add a case for every new one. It always
restores the file it broke, in a finally.
"""
import shutil, subprocess, sys, os
ORCH = "/home/julius/structure_and_semantics/.claude/orchestration"
os.chdir(ORCH)
CASES = [
    ("v2.py", 'and k not in skip)', 'and True)', "graphs_shape", "graph_shape's skip"),
    ("v2.py", 'if os.path.isfile(dotgit):', 'if False:', "copy_of_the_harness_in_a_worktree", "_one_tree"),
    ("v2.py", 'if tid not in tasks or tasks[tid].get("status") == "completed":',
     'if tid not in tasks:', "startable_agrees", "startable's completed check"),
    ("v2.py", 'n = max(high, max(used, default=0)) + 1', 'n = max(used, default=0) + 1',
     "high_water_mark", "allocation above the mark"),
    ("v2.py", 'or stage == "unformed" or orphan', 'or orphan', "not_in_form_is_named_again", "the unformed notice"),
    ("ctx_gauge.py", 'v2.py propose {task}', 'v2.py briefed {task}', "no_message_names_a_command", "the command-name test"),
    ("worker-settings.json", '"Write|Edit|MultiEdit|NotebookEdit|Read', '"Read', "guarded_tool_reach", "the guard's matcher"),
    ("work_meter.py", 'ISABELLE_SYMBOL.sub(" ", ', '(lambda s: s)(', "isabelle_cartouche", "the cartouche strip"),
    ("watchdog.py", 'v2.wake_planner(name)  # cold', 'None  # cold', "sealed_planners_box", "planner_mail"),
    ("v2.py", 'holds_tree = tree_writer(st) == tid', 'holds_tree = False', "holds_the_working_tree", "the tree notice"),
    ("v2.py", 'fed = {n for n, e in group.items() if e.get("feeds")}', 'fed = set()',
     "spliced_into_the_graph", "the feeds seed"),
    ("v2.py", 'if briefs and why:', 'if False:', "as_much_independent_work", "the width detention"),
    ("v2.py", 'if goals and depth is not None and depth > GRAPH_DEPTH:', 'if False:',
     "never_reaches_the_graph", "the depth refusal"),
    ("v2.py", 'if c and not ROLES.get(c["role"], {}).get("graph"):', 'if False:', "sets_what_a_task_waits_on",
     "blockers' permission"),
    ("v2.py", 'w["tasks"][tid]["stage"] = "done"\n        log("the stage of "',
     'pass\n        log("the stage of "', "follows_the_list", "reconcile_stages"),
    ("ctx_gauge.py", '.get("stage") not in ("running", "fixing", None)', ' and False', "taken_on_may_end", "may_end"),
    ("v2.py", 'if not TREES:\n        return PROJECT', 'if False:\n        return PROJECT',
     "left_behind_does_not_capture", "worktree_of's guard"),
    ("v2.py", 'if tree or (TREES and os.path.isdir', 'if tree or (True and os.path.isdir',
     "not_told_it_has_a_tree", "tree_text's guard"),
    ("v2.py", 'for tid in order:\n            with contextlib.suppress(OSError):', 'for tid in []:\n            with contextlib.suppress(OSError):',
     "all_of_it_or_none", "accept's rollback"),
    ("v2.py", '(peek()["tasks"].get(t.get("reviews") or "") or {}).get("stage") == "done")',
     'False)', "subject_has_finished", "the orphaned review"),
    ("v2.py", 'fresh_sweep(st)  # a charge', 'None  # a charge', "drops_the_events_it_supersedes", "fresh_sweep"),
    ("health.py", 'standing(st, now)\n        return\n    if not st["active"]:', 'return\n    if not st["active"]:',
     "restart_meets", "the stopped run's standing state"),
    ("v2.py", 'taken = {tid for tid, t in st["tasks"].items() if (t or {}).get("stage") not in ("ready", None)}',
     'taken = set()', "admitted_again_once_a_slot", "the width's taken set"),
    ("v2.py", '    left = unread(name)', '    left = []', "cannot_be_delivered", "the unread-mail notice"),
    ("v2.py", 'if task is not None and task.get("status") != "completed":',
     'if task is None or task.get("status") != "completed":', "taken_out_of_the_list", "the task gone from the list"),
    ("health.py", 'return "warm_daemon" in open(f"/proc/{pid}/cmdline").read()', 'return True',
     "not_the_daemon", "daemon_alive by name"),
    ("warm_daemon.sh", 'tr \'\\0\' \' \' < "/proc/$p/cmdline" | grep -q warm_daemon', 'true',
     "not_the_daemon", "--ensure by name"),
    ("health.py", 'tended = daemon_alive() and not read("stopped")', 'tended = True',
     "stale_layer", "who refreshes a stale layer"),
    ("ctx_gauge.py", 'if role in v2.PRODUCING:\n            # a producing session holds the slot',
     'if False:\n            # a producing session holds the slot', "whose_work_was_taken_on",
     "the producing session's own stop reason"),
    ("ctx_gauge.py", '\n        blocked_again(session, rec, role)', '\n        None',
     "cannot_end_at_all", "the blocked-turn count"),
    ("work_meter.py", 'if head[:1] == ["v2.py"] or (head[:1] and head[0] in RUNNERS and head[1:] == ["v2.py"]):',
     'if ".claude/orchestration/v2.py" in command:', "rounds_since_production", "v2.py written short"),
    ("v2.py", 'if isinstance(e, OSError) and not os.path.exists(task_path(tid)):', 'if isinstance(e, OSError):',
     "cannot_be_read_is_not_read", "a task file that cannot be read"),
    ("health.py", 'if p in changed and (v2.read_task(t) or {}).get("status") == "completed"}',
     'if False}', "graph_calls_done", "work the repository does not hold"),
    ("v2.py", '        raise RuntimeError(f"{what} ({path}) is there and cannot be read: {e!r}. Nothing writes over it; move it "\n                           "aside only when you know what it should hold.") from e', '        return {}',
     "never_written_over", "a kept file that cannot be read"),
    ("v2.py", '        except OSError as e:\n            # a ledger that is there and cannot be read was replaced by a fresh header and this one entry: every\n            # direction the owner had ever given, gone, under the lock that was meant to protect them. The words are\n            # kept in the log instead and the file is left alone (2026-09-21).\n            log(f"ATTENTION the owner ledger could not be read ({e!r}) and is left untouched. What was said, in "\n                f"full:\\n{entry}")\n', '        except OSError:\n            s = "# Owner ledger"\n',
     "owner_types", "a ledger that cannot be read"),
    ("v2.py", '    if not os.path.exists(path):\n        return ""\n    try:\n        return open(path).read().strip()',
     '    try:\n        return open(path).read().strip()', "hold_whose_file", "a hold that fails closed"),
    ("v2.py", '    except (KeyError, FileNotFoundError):\n        return []      # it never started',
     '    except (KeyError, FileNotFoundError, OSError):\n        return []      # it never started',
     "transcript_that_cannot_be_read", "a transcript that cannot be read"),
    ("watchdog.py", '    if model == "<synthetic>" and re.search(r"hit your .*limit", said, re.I):\n        if time.time()',
     '    if False and re.search(r"hit your .*limit", said, re.I):\n        if time.time()',
     "usage_limit", "the limit before the mail"),
    ("efficiency.py", '            if s:\n                # a fork', '            if s and name is None:\n                # a fork',
     "own_launch_prompt", "a fork measured as itself"),
    ("v2.py", 'if t.get("stage") in ("planner", "unformed") or reopened:', 'if t.get("stage") in ("planner", "unformed"):',
     "puts_back_to_pending", "a task the planner re-opens"),
    ("v2.py", '        for f, waited_on in repointed.items():\n            with contextlib.suppress(Exception):\n'
     '                update_task(f, blockedBy=waited_on)\n', '',
     "all_of_it_or_none", "a splice put back when a placement fails"),
    ("v2.py", 'judge = stage == "reviewing" and t.get("kind") not in ("build", "fix")', 'judge = False',
     "waiting_for_the_planner_s_verdict", "a design waiting for a verdict"),
    ("v2.py", 'stopped = os.path.exists(os.path.join(STATE, "stopped")) and', 'stopped = False and',
     "start_then_stop_then_start_again", "nothing starts while the run is stopped"),
]
bad = []
for fname, old, new, k, label in CASES:
    src = open(fname).read()
    if src.count(old) != 1:
        bad.append(f"{label}: anchor not unique ({src.count(old)})"); continue
    shutil.copy(fname, fname + ".bak")
    try:
        open(fname, "w").write(src.replace(old, new))
        r = subprocess.run([sys.executable, "-m", "pytest", "-q", "-k", k] + [f for f in os.listdir(".") if f.startswith("test_") and f.endswith(".py")], capture_output=True, text=True)
        caught = "failed" in r.stdout.splitlines()[-1] if r.stdout.strip() else False
        print(f"  {'CAUGHT ' if caught else 'MISSED '} {label}")
        if not caught: bad.append(f"{label}: the mutation was not caught")
    finally:
        shutil.move(fname + ".bak", fname)
print()
print("\n".join("  ! " + b for b in bad) or "  every mutation was caught")
