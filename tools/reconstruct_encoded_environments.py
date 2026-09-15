"""Reconstruct exact encoded environment updates and complete insertion-path reports."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='encoded-environments',
    roots=('Encoded_Environment_Execution',),
    export='Encoded_Environment_Execution:encoded_environment.ML',
    session='Reconstruct_encoded_environments',
    groups=((Execution('comparison', 'check_encoded_environments.py', ('--project', '{project}'), 1200),),),
    boundary='Exact codec contracts preserve every original environment row, including malformed and '
             'conflicting inputs. Actual optional updates are compared with the original guarded '
             'constructor through the registered observation boundary. Complete input/output environments, '
             'conditions, comparisons and repair reasons are reconstructed. Actual counted insertions '
             'retain complete before and after buckets and the entire updated environment. Finite scope, '
             'cached allocation, graft and generation adoption, arithmetic and full physical cost, '
             'workflow and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
