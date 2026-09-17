"""Reconstruct the closed native producer-selection cycle from original subjects."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-steering',
    roots=('Native_Development_Steering',),
    export='Native_Development_Steering:native_steering.ML',
    session='Reconstruct_Native_Steering',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Steering', '--module', 'Native_Steering', '--report', 'native_steering_report_value', '--scope', 'development_case_inputs', '--selections', 'development_case_inputs', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-empty', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Steering', '--module', 'Native_Steering', '--report', 'native_steering_report_value', '--scope', 'development_empty_questions', '--selections', 'development_case_inputs', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-first', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Steering', '--module', 'Native_Steering', '--report', 'native_steering_report_value', '--scope', 'development_first_questions', '--selections', 'development_case_inputs', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='The complete original development questions reconstruct every actual producer result and independent original-goal reference. Computed observations construct ordinary native criteria with a proved original-subject equation. The closed native cycle derives producer selection through generation, original-condition compilation, certified observations, independent criticism, comparison, revision and admission. The unique native choice executes subsequent original requests; every resulting claim is checked against the original request again. Empty original scope refuses, retaining the unexecuted requests. A single-question scope exercises actual choice ambiguity. The finite producer and subject scope, broader development coverage and genesis remain explicit.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
