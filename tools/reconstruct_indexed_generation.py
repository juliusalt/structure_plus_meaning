"""Reconstruct complete original generation readings through actual digit-store lookups."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='indexed-generation',
    roots=('Indexed_Generation_Execution',),
    export='Indexed_Generation_Execution:indexed_generation.ML',
    session='Reconstruct_Indexed_Generation',
    groups=((Execution('comparison', 'check_indexed_generation.py', ('--project', '{project}'), 1800),),),
    boundary='All actual digit-store readings equal the complete original generation fields, '
             'recursive predecessor checks, readiness and anchors. Complete original construction '
             'requests, successful new-record queries, adverse claims, unavailable input, every '
             'candidate result and derived revision reason are retained. Installation, full '
             'physical cost, all six development conditions, native mathematical-proof admission, '
             'historical permission and reachability, and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
