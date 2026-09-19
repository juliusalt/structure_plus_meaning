"""Reconstruct the first loop's own notions as a checked state and its residual problems."""
from reconstruction import Execution, Recipe, main


RECIPE = Recipe(
    name='native-development-machinery',
    roots=('Native_Development_Machinery',),
    export='Native_Development_Machinery:native_development_machinery.ML',
    session='Reconstruct_Native_Development_Machinery',
    groups=((
        Execution('presentation', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Machinery', '--module', 'Native_Development_Machinery', '--report', 'development_seed_report_value', '--scope', 'development_machinery_state', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-problems', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Machinery', '--module', 'Native_Development_Machinery', '--report', 'development_machinery_problem_value', '--scope', 'development_machinery_unanswered', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-loop', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Machinery', '--module', 'Native_Development_Machinery', '--report', 'development_machinery_loop_value', '--scope', 'development_machinery_unanswered', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='The checked context defines the notions the first loop\'s judgments consult as a rooted state, '
             'in the same way as the seeded state: the problem a constant poses and its dependencies, '
             'readiness, the selection question, issuability, the refinement request, the verdict and '
             'the repair, the policy constructor, the certified recording of a payload, the locus of a '
             'problem, the recording of the loop\'s decisions, the publication of an admitted answer and '
             'the successor. The roots are expanded and every development constant they mention stands '
             'on the frontier. The state report presents the state with its computed observations and the '
             'acceptance of its own entities, as for the seed. Each root is the problem of its constant '
             'under the definition reading, the same notion as a refinement problem with the other '
             'reading: its subject is the constant, its contract the constant as the checked context '
             'declares it, marked as a definition, its incumbent the kernel definitions the state states '
             'for it, its origin a residual and its authority generated, because every one of these '
             'notions was defined outside the native process. A root the definition reading states no '
             'problem for is retained as unstated. A residual depends on the residuals of the other roots '
             'its kernel definitions mention, read from those definitions. The problem report presents '
             'the residuals, the unstated roots, the dependencies and the assessment of the residuals '
             'with nothing answered; the loop report presents the contract decision of every root, the '
             'executed selection of the ready residuals and the residuals it admits. Which notions are '
             'roots is a choice generated outside the process and is itself a residual; the requirements '
             'an answer to a residual must meet and the verifier of a definition answer are not '
             'established by this recipe.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
