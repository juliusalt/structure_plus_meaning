val () = ML_Print_Depth.set_print_depth 0;
val print = fn text => TextIO.output (TextIO.stdOut, text);
structure N = Native_Control_Child_Review;

fun jnat n = Int.toString (N.integer_of_nat n);
fun jlist f xs = "[" ^ String.concatWith "," (map f xs) ^ "]";
fun joption f NONE = "null" | joption f (SOME x) = f x;
fun jtermword t = "\"" ^ String.implode (rev (N.finite_term_shared_word_fold
  (fn xs => fn b => (if b then #"1" else #"0") :: xs) t [])) ^ "\"";

fun jpair (a,b) = "[" ^ jnat a ^ "," ^ jnat b ^ "]";
fun jtriple (a,(b,c)) = "[" ^ jnat a ^ "," ^ jnat b ^ "," ^ jnat c ^ "]";
fun jquad (a,(b,(c,d))) = "[" ^ jnat a ^ "," ^ jnat b ^ "," ^ jnat c ^ "," ^ jnat d ^ "]";
fun jprofile (c,p) = "{\"candidate\":" ^ jnat c ^ ",\"profile\":" ^ jlist jpair p ^ "}";
fun jloss (c,(d,p)) = "{\"from\":" ^ jnat c ^ ",\"to\":" ^ jnat d ^ ",\"losses\":" ^ jlist jpair p ^ "}";
fun jbasis (formed,(residual,(profiles,losses))) =
  "{\"formed\":" ^ Bool.toString formed ^ ",\"residual\":" ^ jlist jpair residual ^
  ",\"profiles\":" ^ jlist jprofile profiles ^ ",\"losses\":" ^ jlist jloss losses ^ "}";
fun jrepairs (safe,(conflicts,(repairs,unrepairable))) =
  "{\"safe\":" ^ jlist jnat safe ^ ",\"conflicts\":" ^ jlist jquad conflicts ^
  ",\"repairs\":" ^ jlist jquad repairs ^ ",\"unrepairable\":" ^ jlist jpair unrepairable ^ "}";
fun jrevision (retained,(withdrawn,(repairs,(revised,residual)))) =
  "{\"retained\":" ^ jlist jnat retained ^ ",\"withdrawn\":" ^ jlist jnat withdrawn ^
  ",\"repairs\":" ^ jlist jquad repairs ^ ",\"selection\":" ^ jlist jnat revised ^
  ",\"residual\":" ^ jlist jpair residual ^ "}";
fun jcycle (selected,(initial,(repairs,(revision,followed)))) =
  "{\"selected\":" ^ jlist jnat selected ^ ",\"initial\":" ^ jbasis initial ^
  ",\"repairs\":" ^ jrepairs repairs ^ ",\"revision\":" ^ jrevision revision ^
  ",\"followed\":" ^ jbasis followed ^ "}";

fun jcomparison (rows,(relation,(selected,adequate))) =
 "{\"observations\":" ^ jlist jtriple rows ^ ",\"relation\":" ^ jlist jpair relation ^
 ",\"selected\":" ^ jlist jnat selected ^ ",\"adequate\":" ^ jlist jnat adequate ^ "}";
fun jcell (m,(a,(b,(c,(d,e))))) = "[" ^ jnat m ^ "," ^ jlist Bool.toString [a,b,c,d,e] ^ "]";
fun jcontext (w,cells) = "[" ^ jnat w ^ "," ^ jlist jcell cells ^ "]";
fun jresult (m,(claim,(admitted,(comparison,cycle)))) =
 "{\"method\":" ^ jnat m ^ ",\"claim_words\":" ^ joption (jlist jtermword) claim ^
 ",\"admitted_words\":" ^ joption (jlist jtermword) admitted ^
 ",\"comparison\":" ^ joption jcomparison comparison ^ ",\"cycle\":" ^ joption jcycle cycle ^ "}";
fun jsummary (chosen,(cells,results)) = "{\"chosen\":" ^ joption jnat chosen ^
 ",\"all_assessments\":" ^ jlist jcontext cells ^ ",\"results\":" ^ joption (jlist jresult) results ^ "}";
fun jreceived (i,flags) = "[" ^ jnat i ^ "," ^ joption (jlist Bool.toString) flags ^ "]";

fun native_stage_timed name action = let
  val elapsed = Timer.startRealTimer ();
  val cpu = Timer.startCPUTimer ();
  val result = action ();
  val {usr,sys} = Timer.checkCPUTimer cpu;
  val () = print ("Physicalstage " ^ name ^ " wall=" ^ Time.toString (Timer.checkRealTimer elapsed) ^
    " user=" ^ Time.toString usr ^ " system=" ^ Time.toString sys ^ "\n");
  in TextIO.flushOut TextIO.stdOut; result end;

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
val report_value = native_stage_timed "original_presentation" (fn () => N.judgment_artifact_value original_review);
val stream = BinIO.openOut "\047\104\111\109\101\047\106\117\108\105\117\115\047\115\116\114\117\099\116\117\114\101\095\097\110\100\095\115\101\109\097\110\116\105\099\115\047\046\098\117\105\108\100\047\111\118\101\114\110\105\103\104\116\045\050\048\050\054\048\057\049\056\047\109\097\116\101\114\105\097\108\115\045\118\050\047\111\114\105\103\105\110\097\108\046\119\111\114\100";
fun sink (acc, n) b =
  let val acc = acc * 2 + (if b then 1 else 0)
  in if n = 7 then (BinIO.output1 (stream, Word8.fromInt acc); (0, 0)) else (acc, n + 1) end;
fun pad (acc, n) = if n = 0 then () else pad (sink (acc, n) false);
val () = pad (sink (N.finite_term_shared_word_fold sink (report_value) (0, 0)) true);
val () = BinIO.closeOut stream;
val report_value = native_stage_timed "children_presentation" (fn () => N.judgment_artifact_value child_review);
val stream = BinIO.openOut "\047\104\111\109\101\047\106\117\108\105\117\115\047\115\116\114\117\099\116\117\114\101\095\097\110\100\095\115\101\109\097\110\116\105\099\115\047\046\098\117\105\108\100\047\111\118\101\114\110\105\103\104\116\045\050\048\050\054\048\057\049\056\047\109\097\116\101\114\105\097\108\115\045\118\050\047\099\104\105\108\100\114\101\110\046\119\111\114\100";
fun sink (acc, n) b =
  let val acc = acc * 2 + (if b then 1 else 0)
  in if n = 7 then (BinIO.output1 (stream, Word8.fromInt acc); (0, 0)) else (acc, n + 1) end;
fun pad (acc, n) = if n = 0 then () else pad (sink (acc, n) false);
val () = pad (sink (N.finite_term_shared_word_fold sink (report_value) (0, 0)) true);
val () = BinIO.closeOut stream;
val report_value = native_stage_timed "applications_presentation" (fn () => N.cause_root_results_value [applications]);
val stream = BinIO.openOut "\047\104\111\109\101\047\106\117\108\105\117\115\047\115\116\114\117\099\116\117\114\101\095\097\110\100\095\115\101\109\097\110\116\105\099\115\047\046\098\117\105\108\100\047\111\118\101\114\110\105\103\104\116\045\050\048\050\054\048\057\049\056\047\109\097\116\101\114\105\097\108\115\045\118\050\047\097\112\112\108\105\099\097\116\105\111\110\115\046\119\111\114\100";
fun sink (acc, n) b =
  let val acc = acc * 2 + (if b then 1 else 0)
  in if n = 7 then (BinIO.output1 (stream, Word8.fromInt acc); (0, 0)) else (acc, n + 1) end;
fun pad (acc, n) = if n = 0 then () else pad (sink (acc, n) false);
val () = pad (sink (N.finite_term_shared_word_fold sink (report_value) (0, 0)) true);
val () = BinIO.closeOut stream;
val report_value = native_stage_timed "certificates_presentation" (fn () => N.cause_child_proof_choices_value certificate_choices);
val stream = BinIO.openOut "\047\104\111\109\101\047\106\117\108\105\117\115\047\115\116\114\117\099\116\117\114\101\095\097\110\100\095\115\101\109\097\110\116\105\099\115\047\046\098\117\105\108\100\047\111\118\101\114\110\105\103\104\116\045\050\048\050\054\048\057\049\056\047\109\097\116\101\114\105\097\108\115\045\118\050\047\099\101\114\116\105\102\105\099\097\116\101\115\046\119\111\114\100";
fun sink (acc, n) b =
  let val acc = acc * 2 + (if b then 1 else 0)
  in if n = 7 then (BinIO.output1 (stream, Word8.fromInt acc); (0, 0)) else (acc, n + 1) end;
fun pad (acc, n) = if n = 0 then () else pad (sink (acc, n) false);
val () = pad (sink (N.finite_term_shared_word_fold sink (report_value) (0, 0)) true);
val () = BinIO.closeOut stream;
val () = print "CHECKED_CHILD_REVIEW_COMPLETED\n";

val () = TextIO.flushOut TextIO.stdOut;
val () = Future.shutdown ();
val () = OS.Process.exit OS.Process.success;
