"""Reconstruct complete native data-reader comparisons from source."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='data-reading',
    roots=('Data_Reading_Execution',),
    export='Data_Reading_Execution:data_reading.ML',
    session='Reconstruct_data_reading',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Data_Reading_Execution', '--module', 'Data_Reading_Execution', '--report', 'data_reading_report_value', '--scope', 'data_reading_indices', '--selections', 'data_reading_report_selections', '--workers', '4', '--timeout', '600'), 660),
    ),),
    boundary='The native literal replay and joined generation constructor derive the complete source cause. Every certificate key and unavailable constructor position is retained. All original and candidate data readings, soundness and completeness observations, comparisons and revision reasons are reproduced from source. The original quotation relation remains the meaning boundary; full workflow policy, cost and genesis remain open.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
