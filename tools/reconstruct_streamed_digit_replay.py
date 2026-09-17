"""Reconstruct the complete digit replay packet through compressed report storage."""
from compressed_reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='digit-replay',
    roots=('Digit_Replay_Execution', 'Factor_Generation_History_Append'),
    export='Digit_Replay_Execution:digit_replay.ML',
    session='Reconstruct_Digit_Replay',
    groups=((Execution('presentation', 'check_presented_report.py', ('--project', '{project}',
                 '--module', 'Digit_Replay_Execution', '--report', 'digit_replay_report_value',
                 '--scope', 'digit_replay_indices', '--selections', 'digit_replay_report_selections',
                 '--workers', '16', '--timeout', '3600'), 10800),),),
    boundary='The complete original replay packet is rebuilt and executed from repository sources. '
             'Every context, candidate result, original certified-cause report, comparison, revision and '
             'source correspondence is retained in the complete native presented word through lossless compression. '
             'The original reconstruction stage, complete-report and unchanged-input checks are reused. '
             'Full physical cost, all six workflow conditions, historical permission and reachability, '
             'native mathematical-proof admission, genesis and final audit remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
