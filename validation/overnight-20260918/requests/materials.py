from pathlib import Path
import ast, gzip, json, re, sys

base = Path('/tmp/native-control-segment9-20260918')
source = base / 'source-execution-v2'
output = Path(sys.argv[1]).resolve()
export_name = 'child-export'
sys.path.insert(0, str(source / 'tools'))
import isabelle_native_execution, check_presented_report, native_stage_timing, execution_support, investigation_json

native_stage_timing.PRELUDE = native_stage_timing.PRELUDE.replace(
    'in result end;', 'in TextIO.flushOut TextIO.stdOut; result end;')
proof = base / export_name / 'native_control_child_review.proof.json'
poly = Path('/opt/isabelle/contrib/polyml-5.9.2-2/x86_64_32-linux/poly')
presenter = Path('/tmp/native-control-segment4-20260918/execute_scope.py')
tree = ast.parse(presenter.read_text())
node = next(n.value for n in tree.body if isinstance(n, ast.Assign)
            and any(isinstance(t, ast.Name) and t.id == 'view' for t in n.targets))
view = eval(compile(ast.Expression(node), '<retained diagnostic presenter>', 'eval'),
            {'investigation_json': investigation_json})
word_values = {
    'original': 'N.judgment_artifact_value original_review',
    'children': 'N.judgment_artifact_value child_review',
    'applications': 'N.cause_root_results_value [applications]',
    'certificates': 'N.cause_child_proof_choices_value certificate_choices',
}

def program(engine, inputs):
    loading = 'use ' + execution_support.ml_string(str(engine)) + ';\nstructure N = Native_Control_Child_Review;\n'
    body = view + native_stage_timing.PRELUDE + r'''
fun jbool b = Bool.toString b;
fun jmatrix xs = jlist (jlist jbool) xs;
fun jmethod _ = "true";
fun japp (s,(d,(c,(missing,profiles)))) =
  "[" ^ jnat s ^ "," ^ jnat d ^ "," ^ jnat c ^ "," ^ jlist jnat missing ^ "," ^ jmatrix profiles ^ "]";
fun marker name value = (print (name ^ "_BEGIN\n" ^ value ^ "\n" ^ name ^ "_END\n"); TextIO.flushOut TextIO.stdOut);
fun report_of (_,(_,(r,_))) = r;
fun results_of (_,(_,(_,result))) = case result of SOME xs => map report_of xs
  | NONE => raise Fail "Native producer did not execute requests";
fun available rows = List.mapPartial (fn (index,(prepared,subjects,facets,q)) =>
  case q of NONE => NONE | SOME question => SOME (index,prepared,subjects,facets,question))
  (ListPair.zip (List.tabulate (length rows, fn i => i), rows));

val subject = native_stage_timed "actual_root_subject" (fn () => N.cause_root_subject ());
val root_prepared = native_stage_timed "original_root_observations" (fn () => N.cause_root_prepare subject);
val steering = native_stage_timed "steering_questions" (fn () => N.judgment_steering_questions ());
val original_questions = native_stage_timed "original_questions" (fn () =>
  [Option.valOf (N.judgment_bridge_question ()), Option.valOf (N.judgment_artifact_execution_question ()),
   Option.valOf (N.guard_representation_execution_question ()),
   Option.valOf (N.cause_root_prepared_question root_prepared N.cause_root_methods N.cause_root_facets)]);
val original_review = native_stage_timed "original_native_admission" (fn () =>
  N.native_steered_development steering original_questions);
val originals = results_of original_review;
val applications = native_stage_timed "original_selected_application" (fn () =>
  N.cause_root_apply_prepared root_prepared (List.nth (originals,3)));
val actual = case applications of SOME A => A | NONE => raise Fail "Original root refused";
val demands = native_stage_timed "actual_child_demands" (fn () => N.cause_child_demands actual);
val schema_subjects = native_stage_timed "actual_child_schemas" (fn () => N.cause_child_schema_subjects actual);
val certificate_prepared = []; (* Completed certificate scope remains in the original retained run. *)
val () = marker "CERTIFICATE_PROFILES" (jlist jmatrix (map N.cause_certificate_profiles certificate_prepared));
val indexed_subjects = ListPair.zip (List.tabulate (length schema_subjects,fn i => i), schema_subjects);
fun subject_site (a,(s,(d,(x,(c,S))))) = "[" ^ jnat s ^ "," ^ jnat d ^ "," ^ jnat c ^ "]";
val () = marker "ACTUAL_SUBJECT_SITES" (jlist (fn (i,s) => "[" ^ Int.toString i ^ "," ^ subject_site s ^ "]") indexed_subjects);
fun prepare_measured (i,s) = let
  val label = "material_subject_" ^ Int.toString i;
  val clock = Timer.startRealTimer ();
  val () = marker ("SUBJECT_STARTED_" ^ Int.toString i) (subject_site s);
  val result = (SOME (native_stage_timed label (fn () =>
    Timeout.apply_physical (Time.fromSeconds 90)
      (fn () => N.cause_child_application_prepare_family [s]) ()))
    handle Timeout.TIMEOUT _ => NONE);
  val () = marker ("SUBJECT_FINISHED_" ^ Int.toString i)
    ("[" ^ Bool.toString (Option.isSome result) ^ "," ^ Time.toString (Timer.checkRealTimer clock) ^ "]");
  in (i,result) end;
val measured_prepares = Par_List.map prepare_measured indexed_subjects;
val completed_indices = List.mapPartial (fn (i,p) => Option.map (fn _ => i) p) measured_prepares;
val unresolved_indices = List.mapPartial (fn (i,p) => if Option.isSome p then NONE else SOME i) measured_prepares;
val () = marker "COMPLETED_SUBJECTS" (jlist Int.toString completed_indices);
val () = marker "UNRESOLVED_SUBJECTS" (jlist Int.toString unresolved_indices);
val application_prepared = List.concat (List.mapPartial #2 measured_prepares);
val () = marker "APPLICATION_PROFILES" (jlist japp (map N.cause_child_application_profiles application_prepared));
val certificate_rows = native_stage_timed "certificate_questions" (fn () =>
  List.concat (map (fn p => map (fn (xs,fs) => (p,xs,fs,N.cause_certificate_question p xs fs))
    (N.cause_certificate_scopes (#1 (#2 p)))) certificate_prepared));
val application_rows = native_stage_timed "application_questions" (fn () =>
  List.concat (map (fn p => map (fn (xs,fs) => (p,xs,fs,N.cause_child_application_question p xs fs))
    [(N.cause_root_methods,N.cause_root_facets),(rev N.cause_root_methods,N.cause_root_facets),
     (N.cause_root_methods @ N.cause_root_methods,N.cause_root_facets),
     (N.cause_root_methods,[hd N.cause_root_facets]),(N.cause_root_methods,[List.nth (N.cause_root_facets,1)]),
     ([],N.cause_root_facets)]) application_prepared));
val certificates_available = available certificate_rows;
val applications_available = available application_rows;
val () = marker "QUESTION_AVAILABILITY" ("[" ^
  jlist jbool (map (fn (_,_,_,q) => Option.isSome q) certificate_rows) ^ "," ^
  jlist jbool (map (fn (_,_,_,q) => Option.isSome q) application_rows) ^ "]");
val questions = map #5 certificates_available @ map #5 applications_available;
val child_review = native_stage_timed "child_native_review" (fn () =>
  N.native_steered_development steering questions);
val reports = results_of child_review;
val certificate_reports = List.take (reports,length certificates_available);
val application_reports = List.drop (reports,length certificates_available);
val certificate_choices = native_stage_timed "certificate_admission" (fn () =>
  map (fn ((_,p,xs,fs,_),r) => N.cause_certificate_choice p xs fs r)
    (ListPair.zip (certificates_available,certificate_reports)));
val application_choices = native_stage_timed "application_admission" (fn () =>
  map (fn ((_,p,xs,fs,_),r) => N.cause_child_application_choice p xs fs r)
    (ListPair.zip (applications_available,application_reports)));
val absent_certificates = native_stage_timed "absent_certificate_reports" (fn () =>
  map (fn (_,p,xs,fs,_) => N.cause_certificate_choice p xs fs N.absent_development_report) certificates_available);
val absent_applications = native_stage_timed "absent_application_reports" (fn () =>
  map (fn (_,p,xs,fs,_) => N.cause_child_application_choice p xs fs N.absent_development_report) applications_available);
val wrong_certificates = native_stage_timed "wrong_certificate_reports" (fn () =>
  map (fn (_,p,xs,fs,_) => N.cause_certificate_choice p xs fs (hd originals)) certificates_available);
val wrong_applications = native_stage_timed "wrong_application_reports" (fn () =>
  map (fn (_,p,xs,fs,_) => N.cause_child_application_choice p xs fs (hd originals)) applications_available);
val () = marker "ORIGINAL_NATIVE_SUMMARY" (jsummary (N.context_execution_summary original_review));
val () = marker "CHILD_NATIVE_SUMMARY" (jsummary (N.context_execution_summary child_review));
val () = marker "CERTIFICATE_CHOICES" (jlist (joption (joption jnat)) (map N.cause_child_proof_summary certificate_choices));
val () = marker "APPLICATION_CHOICES" (jlist (joption jmethod) application_choices);
val () = marker "ABSENT_CERTIFICATES" (jlist (joption (joption jnat)) (map N.cause_child_proof_summary absent_certificates));
val () = marker "ABSENT_APPLICATIONS" (jlist (joption jmethod) absent_applications);
val () = marker "WRONG_CERTIFICATES" (jlist (joption (joption jnat)) (map N.cause_child_proof_summary wrong_certificates));
val () = marker "WRONG_APPLICATIONS" (jlist (joption jmethod) wrong_applications);
'''
    code = loading + body
    for name, expression in word_values.items():
        fragment = check_presented_report.program(engine, {
            'module': 'Native_Control_Child_Review', 'report': 'cause_child_proof_choices_value',
            'scope': 'runtime_result', 'selections': None}, output / (name + '.word'))
        assert fragment.count(loading) == 1
        fragment = fragment.replace(loading, '').replace(
            'N.cause_child_proof_choices_value N.runtime_result', 'report_value')
        code += 'val report_value = native_stage_timed "' + name + '_presentation" (fn () => ' + expression + ');\n' + fragment
    return code + 'val () = print "CHECKED_CHILD_REVIEW_COMPLETED\\n";\n'

def assess(inputs, log):
    text = gzip.open(log, 'rt').read()
    assert 'CHECKED_CHILD_REVIEW_COMPLETED' in text
    def block(name):
        return json.loads(text.split(name + '_BEGIN\n')[1].split('\n' + name + '_END')[0])
    words = {}
    for name in word_values:
        words[name] = check_presented_report.retain_word(output / (name + '.word'), output / (name + '.word.gz'))
        (output / (name + '.word')).unlink()
    fields = ['ACTUAL_SUBJECT_SITES','COMPLETED_SUBJECTS','UNRESOLVED_SUBJECTS','CERTIFICATE_PROFILES','APPLICATION_PROFILES','QUESTION_AVAILABILITY',
              'ORIGINAL_NATIVE_SUMMARY','CHILD_NATIVE_SUMMARY','CERTIFICATE_CHOICES',
              'APPLICATION_CHOICES','ABSENT_CERTIFICATES','ABSENT_APPLICATIONS',
              'WRONG_CERTIFICATES','WRONG_APPLICATIONS']
    return {'physical_completion': True, **{k.lower(): block(k) for k in fields}, 'words': words,
            'timings': [dict(zip(('stage','wall','user','system'), x)) for x in re.findall(
                r'Physicalstage ([a-z_0-9]+) wall=([0-9.]+) user=([0-9.]+) system=([0-9.]+)', text)],
            'scope': 'Physical per-subject attempt of EVERY actual original child schema. Every completed subject runs all original material-application facets and native criticism controls. Timed-out subjects remain UNRESOLVED: no observation, result, facet satisfaction or method selection is inferred for them. Certificate construction is not rerun. Complete words retain the original root application and every completed native review. No installed proof, policy cause, source optimization, or whole-goal admission.'}

r = isabelle_native_execution.checked_execution(proof, poly, output, workers=8, program=program,
    input_paths=[Path(__file__),presenter,Path(check_presented_report.__file__),Path(native_stage_timing.__file__)],
    required_theories=['Native_Control_Child_Review'],
    inputs={'originals': 'All body/adapter/target/root questions recomputed; root method consumed through original native admission.',
            'children': 'All retained application occurrences and all original source clauses. Full demand and each leaf kept separately.',
            'criticism': ['reversal','duplicate candidates','each omitted facet','empty scope','absent report','wrong original-body report'],
            'certificates': 'Not rerun here. Completed original certificate questions remain at segment9/certificate-review-v1; their unsolved full/projection/quotation scope is not discharged.'},
    assess=assess,
    question='For every actual original child schema, which available application constructions satisfy the requested result and complete original schema/material obligations? All unavailable computations remain unresolved.',
    boundary='certificate_observation_exact, certificate_result_choice_original, cause_child_occurrences_exact, cause_child_schema_subjects_exact, cause_child_application_choice_original. Installed source transport and cause remain outstanding.',
    timeout=180, project=source)
print(json.dumps({k:r[k] for k in ['status','error','error_type'] if k in r}))
raise SystemExit(0 if r['status']=='accepted' else 1)
