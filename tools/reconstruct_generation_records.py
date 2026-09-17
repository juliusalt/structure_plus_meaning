"""Reconstruct complete native generation-records reports from their original sources."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='generation-records',
    roots=('Generation_Record_Execution',),
    export='Generation_Record_Execution:generation_record.ML',
    session='Reconstruct_generation_records',
    groups=((Execution("comparison", 'check_generation_records.py', ("--project", "{project}"), 2100),
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Generation_Record_Execution', '--module', 'Generation_Record_Execution', '--report', 'generation_record_report_value', '--scope', 'generation_record_indices', '--selections', 'generation_record_report_selections', '--workers', '4', '--timeout', '600'), 660),),),
    boundary='Complete original targets, history, predecessor cores and actual reference sites determine every construction and condition. All returned environments, field readings, original-reference sets, comparisons and revisions are reconstructed. The closed-replay cause join has a proved constructor; arbitrary cause reading, full workflow transitions, historical permission, physical cost and genesis remain open.')


if __name__ == "__main__":
    raise SystemExit(main(RECIPE, __file__))
