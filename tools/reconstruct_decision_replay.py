"""Reconstruct complete original-requirement decisions and their native replay."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name="decision-replay",
    roots=("Decision_Replay_Execution",),
    export="Decision_Replay_Execution:decision_replay.ML",
    session="Reconstruct_decision_replay",
    groups=((Execution('presentation', 'check_presented_report.py', ('--project', '{project}',
                 '--module', 'Decision_Replay_Execution', '--report', 'decision_replay_report_value',
                 '--scope', 'requirement_decision_indices', '--selections', 'decision_replay_report_selections',
                 '--workers', '8', '--timeout', '3600'), 4200),),),
    boundary="Complete original source, requirements and terms determine each full decision and its exact target-certificate replay family. Every native graph, call, extending and retained environment, original-condition assessment, comparison and revision is reproduced. Derived sharing preserves the complete public reports. This scoped composition does not establish whole-workflow enforcement, original-policy and historical permission, complete subject and criticism coverage, physical cost or genesis.")


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
