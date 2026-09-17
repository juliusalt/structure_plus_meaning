"""Reconstruct all registered built-in subject investigations from one proved export."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='builtin-investigations',
    roots=('Builtin_Investigation_Execution',),
    export='Builtin_Investigation_Execution:builtin_investigations.ML',
    session='Reconstruct_Builtin_Investigations',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Builtin_Investigation_Execution', '--module', 'Finite_Investigation', '--report', 'builtin_investigation_report_value', '--scope', 'builtin_investigation_selections', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='Every registered original-subject operation computes its complete observations, comparison, repairs and revision for empty, partial, complete and repeated selections; pattern markers also exercise the distinct and collapsed presentations. The typed owner contracts remain exact. These fixed scopes do not derive arbitrary development choices or establish practical gate 5a.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
