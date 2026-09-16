"""Reconstruct complete history operations using the actual quoted policy scope."""
from compressed_reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='quoted-history',
    roots=('Quoted_History_Execution',),
    export='Quoted_History_Execution:quoted_history.ML',
    session='Reconstruct_Quoted_History',
    groups=((Execution('comparison', 'check_quoted_history.py', ('--project', '{project}'), 10800),
             Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Quoted_History_Execution', '--module', 'Digit_History_Execution', '--report', 'quoted_history_report_value', '--scope', 'digit_history_indices', '--selections', 'quoted_history_report_selections'), 10800)),),
    boundary='The actual quoted judgment and generation-backend contracts establish the complete '
             'original scope and certification used by the constructed policy check. Every original '
             'history subject, method, full result, inspection, source and revision is retained. '
             'The additional raw omitted-replay control remains separate from the closed operation. '
             'Full physical cost, all six workflow conditions, historical permission and reachability, '
             'native mathematical-proof admission, genesis and final audit remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
