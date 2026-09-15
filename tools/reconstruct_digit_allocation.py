"""Reconstruct persistent digit allocation and complete original state comparisons."""
from reconstruction import Execution, Recipe, main

RECIPE = Recipe(
    name='digit-allocation',
    roots=('Digit_Allocation_Execution',),
    export='Digit_Allocation_Execution:digit_allocation.ML',
    session='Reconstruct_Digit_Allocation',
    groups=((Execution('comparison', 'check_digit_allocation.py', ('--project', '{project}'), 900),),),
    boundary='Complete original result relations govern typed persistent digit allocation. The actual '
             'counter bounds all original uses. Initialization and local updates preserve original '
             'formation, every relation row and all optional outcomes. Both traversals at each actual '
             'next allocation key are reconstructed with the prior original histories and full '
             'candidate comparisons. Key construction, arithmetic, complete physical cost, graft and '
             'generation adoption, whole workflow enforcement and genesis remain open.')

if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
