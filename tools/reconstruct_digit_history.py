"""Reconstruct complete persistent digit histories with original policy and admission meaning."""
from reconstruction import Execution,Recipe,main


RECIPE=Recipe(
    name='digit-history',roots=('Digit_History_Execution',),
    export='Digit_History_Execution:digit_history.ML',session='Reconstruct_Digit_History',
    groups=((Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--module', 'Digit_History_Execution', '--report', 'digit_history_report_value', '--scope', 'digit_history_indices', '--selections', 'digit_history_report_selections'), 3600),),),
    boundary='The closed history stores its header, actual digit material, ordered ledger and exact cache. '
        'Actual membership, generation, cause and policy operations preserve every original bounded transition. '
        'All original and subsequent source inputs, whole results, counter and cache relations, actual coverage, '
        'comparisons and revisions are reconstructed. Full physical cost, whole workflow adequacy, all six '
        'workflow conditions, historical permission and reachability, native mathematical-proof admission, '
        'genesis and final audit remain open.')


if __name__=='__main__':raise SystemExit(main(RECIPE,__file__))
