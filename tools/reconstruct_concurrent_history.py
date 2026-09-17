"""Reconstruct a complete packet with proved sharing and ordered parallel execution."""
from compressed_reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='concurrent-history',
    roots=('Concurrent_History_Execution',),
    export='Concurrent_History_Execution:concurrent_history.ML',
    session='Reconstruct_Concurrent_History',
    groups=((Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Concurrent_History_Execution', '--module', 'Digit_History_Execution', '--report', 'concurrent_history_report_value', '--scope', 'digit_history_indices', '--selections', 'concurrent_history_report_selections', '--workers', '4', '--timeout', '1200'), 1300),),),
    fixtures=('tools/compressed_reconstruction_suite.py',),
    boundary='Every original subject, candidate, complete result, observation, comparison and revision '
             'is reconstructed from source under the original subject contract. Native exact sharing, '
             'source projection and Isabelle parallel-map equations preserve the complete packet. '
             'The compact report boundary includes its complete native artifact dictionary. The runtime '
             'uses the declared Isabelle2025-2 and Poly/ML 5.9.2 bootstrap and records its complete inputs. '
             'All six workflow conditions, historical permission and reachability, native mathematical-proof '
             'admission, genesis and final audit remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
