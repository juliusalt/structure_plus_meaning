"""Reconstruct the complete native certificate replay execution from repository sources."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-certificate-replay',
    roots=('Native_Certificate_Replay_Execution',),
    export='Native_Certificate_Replay_Execution:certificate_replay.ML',
    session='Reconstruct_native_certificate_replay',
    groups=((Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Certificate_Replay_Execution', '--module', 'Native_Certificate_Replay_Execution', '--report', 'native_replay_report_value', '--scope', 'native_replay_indices', '--selections', 'native_replay_report_selections', '--workers', '4', '--timeout', '1200'), 1300),),),
    boundary='Complete original source and certificate families determine actual source-positioned graphs, newly installed graph and application artifacts, the least retained environment and closed native replay. Every candidate result, original-source correspondence, application and graph reading, individual and family condition, complete comparison and revision is reproduced. Shared readers have complete-input equality contracts. The full workflow, cost, mathematical-proof admission and genesis remain open.')


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
