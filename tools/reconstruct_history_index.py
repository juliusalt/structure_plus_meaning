"""Reconstruct complete indexed admission ledgers under the original history policy."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='history-index',
    roots=('History_Index_Execution',),
    export='History_Index_Execution:history_index.ML',
    session='Reconstruct_History_Index',
    groups=((Execution('comparison', 'check_history_index.py', ('--project', '{project}'), 2400),),),
    boundary='Actual indexed histories preserve every original request, policy, material and '
             'ordered ledger field and the complete decoded admission index. The original transition '
             'determines reference outputs independently. Shared actual operations feed adverse '
             'cache and transition controls; persistent subsequent steps and all original source '
             'cases are retained with complete observations, comparisons and revisions. Complete '
             'workflow adequacy, physical cost, historical permission and reachability, native '
             'mathematical-proof admission, generation-store adoption and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
