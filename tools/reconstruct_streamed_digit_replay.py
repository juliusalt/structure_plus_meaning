"""Reconstruct the complete digit replay packet through compressed report storage."""
from compressed_reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='digit-replay',
    roots=('Digit_Replay_Execution', 'Factor_Generation_History_Append'),
    export='Digit_Replay_Execution:digit_replay.ML',
    session='Reconstruct_Digit_Replay',
    groups=((Execution('comparison', 'check_streamed_digit_replay.py', ('--project', '{project}'), 10800),),),
    boundary='The complete original replay packet is rebuilt and executed from repository sources. '
             'Every context, candidate result, original certified-cause report, comparison, revision and '
             'source correspondence is retained through lossless compression and separate complete records. '
             'The original reconstruction stage, complete-report and unchanged-input checks are reused. '
             'Full physical cost, all six workflow conditions, historical permission and reachability, '
             'native mathematical-proof admission, genesis and final audit remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
