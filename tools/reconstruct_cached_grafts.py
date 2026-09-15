"""Reconstruct actual cached digit grafts and whole original result comparisons."""
from reconstruction import Execution, Recipe, main

RECIPE = Recipe(
    name='cached-grafts', roots=('Cached_Graft_Execution',),
    export='Cached_Graft_Execution:cached_graft.ML', session='Reconstruct_Cached_Grafts',
    groups=((Execution('comparison', 'check_cached_grafts.py', ('--project', '{project}'), 900),),),
    boundary='Original complete graft readiness and the explicit stored-prefix counter update determine '
             'every optional result. Exact lookup checks and batch insertion preserve the original '
             'whole environment and strict head bound in the existing closed digit store. Native '
             'persistent histories and complete original source cases are reconstructed with all '
             'candidate outputs, observations, comparisons and revisions. Generation-store adoption, '
             'full physical cost, complete workflow enforcement, historical permission and reachability, '
             'native proof checking, genesis and the final audit remain open.')

if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
