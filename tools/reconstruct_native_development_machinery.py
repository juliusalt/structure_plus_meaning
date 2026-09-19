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
        Execution('presentation-verification', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Machinery', '--module', 'Native_Development_Machinery', '--report', 'development_machinery_verification_value', '--scope', 'development_machinery_unanswered', '--workers', '4', '--timeout', '1200'), 1300),
        Execution('presentation-native-answers', 'check_presented_report.py', ('--project', '{project}', '--theory', 'Native_Development_Machinery', '--module', 'Native_Development_Machinery', '--report', 'development_machinery_native_answers_value', '--scope', 'development_machinery_unanswered', '--workers', '4', '--timeout', '1200'), 1300),
    ),),
    boundary='The checked context defines the notions the first loop\'s judgments consult as a rooted state, '
             'in the same way as the seeded state: the problem a constant poses and its dependencies, '
             'readiness, the selection question, issuability, the refinement request, the verdict and '
             'the repair, the definition request and the definition verdict, the policy constructor, the certified recording of a payload, the locus of a '
             'problem, the recording of the loop\'s decisions, the publication of an admitted answer and '
             'the successor, together with their constituents, the development constants their items '
             'mention. The notions and their constituents are the roots and are expanded, and every '
             'development constant the constituents mention stands on the frontier. The state report presents the state with its computed observations and the '
             'acceptance of its own entities, as for the seed. Each root is the problem of its constant '
             'under the definition reading, the same notion as a refinement problem with the other '
             'reading: its subject is the constant, its contract the constant as the checked context '
             'declares it, marked as a definition, its incumbent the kernel definitions the state states '
             'for it, its origin a residual and its authority generated, because every one of these '
             'notions was defined outside the native process. A root the definition reading states no '
             'problem for is retained as unstated. A residual depends on the residuals of the other roots '
             'its kernel definitions mention, read from those definitions, so a notion\'s residual depends '
             'on the residuals of its constituents and the loop takes constituents first. The problem '
             'report presents '
             'the residuals, the unstated roots, the dependencies and the assessment of the residuals '
             'with nothing answered; the loop report presents the contract decision of every root, the '
             'executed selection of the ready residuals and the residuals it admits. Which notions are '
             'roots and how far the record reaches are choices generated outside the process and are '
             'themselves residuals. The verification report issues every selected residual as a definition '
             'request, the request of its one constant under the definition reading with the support and '
             'least context of the constant\'s scope, and judges answer states derived from each request '
             'with the definition verdict, which lets an answer replace the kernel definitions of its '
             'subject and the code equations derived from them and nothing else: the unchanged state and '
             'its renaming are accepted, the subject\'s definitions stated as axioms, dropped or stated '
             'through an unknown constant are refused, as is dropping the other residuals\' definitions, '
             'and dropping the subject\'s code equations is accepted. That the library\'s contracts of a '
             'residual still hold under a new definition is Isabelle\'s acceptance of an actual answer, '
             'which this recipe does not judge; the requirements an answer to a residual must meet beyond '
             'those contracts are not established by this recipe. The native-answers report answers every issued '
             'definition request natively: the restating answer removes the subject\'s kernel definitions its '
             'context holds and adds them again, is presented with the names it uses, transported as the padded '
             'word of its presentation, read back by its exact reader and judged by the definition verdict on the '
             'answer state; the word without its terminating bit is refused. The judgment establishes that an '
             'answer is admissible for installation, not that the library\'s contracts hold under it.')


if __name__ == '__main__':
    raise SystemExit(main(RECIPE, __file__))
