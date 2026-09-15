"""Reconstruct native allocation-state transitions and actual path observations."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='allocated-environments',
    roots=('Allocated_Environment_Execution',),
    export='Allocated_Environment_Execution:allocated_environment.ML',
    session='Reconstruct_allocated_environments',
    groups=((Execution('comparison', 'check_allocated_environment.py', ('--project', '{project}'), 900),),),
    boundary='A closed store carries original formation and a strict actual head bound. Checked loading '
             'derives the bound from complete source rows; local allocation and binding updates preserve '
             'it with exact whole original-constructor contracts. Complete optional states, actual '
             'candidate results, original-condition observations, comparisons, revisions and persistent '
             'chains are reconstructed. Both traversals of the actual next insertion are counted. '
             'Current unary path growth, generic encoded stores, graft and generation adoption, full '
             'physical cost, complete workflow enforcement and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
