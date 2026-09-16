"""Reconstruct complete history transitions using admitted predecessor readings."""
from compressed_reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='known-history',
    roots=('Known_History_Execution',),
    export='Known_History_Execution:known_history.ML',
    session='Reconstruct_Known_History',
    groups=((Execution('comparison', 'check_known_history.py', ('--project', '{project}'), 10800),
             Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Known_History_Execution', '--module', 'Digit_History_Execution', '--report', 'known_history_report_value', '--scope', 'digit_history_indices', '--selections', 'known_history_report_selections'), 10800)),),
    boundary='Original closed history validity and actual index membership establish each complete '
             'predecessor reading. The reconstructed operation preserves the original target, replay, '
             'policy, allocation and append behavior. Every original subject, method, source field, '
             'complete result, inspection and revision is retained through verified compressed storage. '
             'Full physical cost, all six workflow conditions, historical permission and reachability, '
             'native mathematical-proof admission, genesis and final audit remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
