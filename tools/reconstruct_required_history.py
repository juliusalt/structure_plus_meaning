"""Reconstruct full original-policy history transitions and family controls."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='required-history',
    roots=('Required_History_Execution',),
    export='Required_History_Execution:required_history.ML',
    session='Reconstruct_required_history',
    groups=((Execution('comparison', 'check_required_history.py', ('--project', '{project}'), 2400),),),
    boundary='Actual original requirement evaluation supplies complete certificate and replay families. '
             'The invariant-carrying history API preserves the original request and policy, checks '
             'every requested predecessor against the admission ledger, joins actual replay and '
             'generation construction, and checks the original policy cause. Complete optional state '
             'outputs, certificate keys, unavailable positions, condition observations, comparisons, '
             'revisions and coverage counts are reproduced. Whole workflow-policy adequacy, complete '
             'historical permission and reachability, indexed generation storage and allocation, '
             'full physical cost and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
