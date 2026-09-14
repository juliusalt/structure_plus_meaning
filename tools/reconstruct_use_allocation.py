"""Reconstruct complete fresh-use mapping and coordinate-growth comparisons."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='use-allocation',
    roots=('Use_Allocation_Execution',),
    export='Use_Allocation_Execution:use_allocation.ML',
    session='Reconstruct_use_allocation',
    groups=((Execution('comparison', 'check_use_allocation.py', ('--project', '{project}'), 900),),),
    boundary='Actual complete reserved-use sets, supplied boundaries and requested words produce '
             'complete mapping graphs and native coordinate counts. Original boundary identity, '
             'freshness, injectivity and suffix preservation remain distinct from one-coordinate '
             'growth. Every condition, semantic and growth comparison, and revision reason is '
             'reproduced. Initial head scanning, cached state, graft and generation adoption, '
             'natural-number bit cost, full physical cost, whole workflow and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
