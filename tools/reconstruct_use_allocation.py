"""Reconstruct complete fresh-use mapping and coordinate-growth comparisons."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='use-allocation',
    roots=('Use_Allocation_Execution',),
    export='Use_Allocation_Execution:use_allocation.ML',
    session='Reconstruct_use_allocation',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Use_Allocation_Execution', '--module', 'Use_Allocation_Execution', '--report', 'use_allocation_report_value', '--scope', 'use_allocation_indices', '--selections', 'use_allocation_report_selections', '--workers', '4', '--timeout', '600'), 660),
    ),),
    boundary='Actual complete reserved-use sets, supplied boundaries and requested words produce complete mapping graphs and native coordinate counts. Original boundary identity, freshness, injectivity and suffix preservation remain distinct from one-coordinate growth. Every condition, semantic and growth comparison, and revision reason is reproduced. Initial head scanning, cached state, graft and generation adoption, natural-number bit cost, full physical cost, whole workflow and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
