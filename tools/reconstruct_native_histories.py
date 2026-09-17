"""Rebuild source-derived inference histories and their complete native investigation."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-histories',
    roots=('Native_History_Investigation_Execution',),
    export='Native_History_Investigation_Execution:native_history_investigation.ML',
    session='Native_History_Reconstruction',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_History_Investigation_Execution', '--module', 'Native_History_Investigation_Execution', '--report', 'native_history_report_value', '--scope', 'native_history_indices', '--selections', 'native_history_report_selections', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='A run without --proof reconstructs the complete contracts from HOL. The actual source reader supplies the program and the complete finite evaluator retains every progressive preceding state with all original activated clauses, bindings and premise occurrences. Independent conditions assess original requested positive meaning, source identity, availability, the complete state sequence and exact schema witnesses. Every source, candidate history, answer difference, assessment, comparison and revision is reproduced. The finite scope does not establish arbitrary-method coverage, native proof-artifact construction, native mathematical-proof checking, complete development-cycle enforcement, the whole cost account or genesis.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
