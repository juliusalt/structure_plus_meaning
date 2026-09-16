"""Reconstruct complete history construction using both established local premises."""
from compressed_reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='constructed-history',
    roots=('Constructed_History_Execution',),
    export='Constructed_History_Execution:constructed_history.ML',
    session='Reconstruct_Constructed_History',
    groups=((Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Constructed_History_Execution', '--module', 'Digit_History_Execution', '--report', 'constructed_history_report_value', '--scope', 'digit_history_indices', '--selections', 'constructed_history_report_selections'), 10800),),),
    boundary='Original closed history validity and actual indexed membership supply every known '
             'predecessor reading. Actual replay and quotation supply the complete policy scope. '
             'The composite operation retains both guards and every remaining original check, '
             'complete optional result, original subject and original method. Both preceding '
             'refinements and the raw omitted-membership control remain explicit. '
             'Full physical cost, all six workflow conditions, historical permission and reachability, '
             'native mathematical-proof admission, genesis and final audit remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
