theory Factor_Development_Cases
  imports Factor_Development_Admission Factor_Workflow_Cases
begin

definition development_formed_condition :: "native_development_condition" where
  "development_formed_condition=\<lparr>condition_source=finite_guard_source True,condition_source_use=None,
    condition_source_root=[0],condition_goals=[Existing_Admission (None,[1])]\<rparr>"

definition development_existing_condition where
  "development_existing_condition d F u=\<lparr>condition_source=F,condition_source_use=u,
    condition_source_root=[],condition_goals=[Existing_Admission d]\<rparr>"

lemma development_existing_condition_exact:
  assumes native: "native_package_at (decode_finite_environment F) u [] P"
  shows "development_condition_holds (development_existing_condition d F u) x y \<longleftrightarrow>
    (d,Pair_Term (decode_finite_term x) (decode_finite_term y))\<in>positive_meaning P"
proof -
  have present: "finite_native_source F u []\<noteq>None"
    using native by (simp only: finite_native_source_absent; blast)
  obtain N where finite: "native_package_at (decode_finite_environment F) u [] (decode_finite_system N)"
    using present by (cases "finite_native_source F u []") (auto simp only: finite_native_source_correct)
  have same: "decode_finite_system N=P" by (rule native_package_unique[OF finite native])
  have unique: "decode_finite_system M=P"
    if "native_package_at (decode_finite_environment F) u [] (decode_finite_system M)" for M
    by (rule native_package_unique[OF that native])
  let ?t="Pair_Term (decode_finite_term x) (decode_finite_term y)"
  have representation: "development_condition_holds (development_existing_condition d F u) x y \<longleftrightarrow>
    (\<exists>M. native_package_at (decode_finite_environment F) u [] (decode_finite_system M) \<and>
      term_formed ?t \<and> (d,?t)\<in>positive_meaning (decode_finite_system M))"
    by (simp add: development_condition_holds_def development_condition_requirement_def
      workflow_requirement_holds_def development_existing_condition_def admission_requirements_hold_def)
  show ?thesis
  proof
    assume holds: "development_condition_holds (development_existing_condition d F u) x y"
    obtain M where actual: "native_package_at (decode_finite_environment F) u [] (decode_finite_system M)"
      and positive: "(d,?t)\<in>positive_meaning (decode_finite_system M)"
      using holds by (simp only: representation; blast)
    show "(d,?t)\<in>positive_meaning P" using positive by (simp only: unique[OF actual])
  next
    assume positive: "(d,?t)\<in>positive_meaning P"
    have formed: "term_formed ?t"
      using schema_call_formed_target[OF positive_meaning_formed[OF positive]] by blast
    show "development_condition_holds (development_existing_condition d F u) x y"
      unfolding representation by (rule exI[of _ N]) (use finite formed positive in \<open>simp only: same; blast\<close>)
  qed
qed

section \<open>A condition is a native program installed at one of its entries\<close>

text \<open>
  A native question judges each candidate by a condition: a native program installed beside the
  guard source and read at one of its entries. The ground condition of a finite family and the scope
  critic are two programs installed this way; any program that extends the guard source's program
  is installed the same way, and its condition holds of a problem and a candidate exactly when the
  program's entry holds of their pair. A program that does not call the guard source is installed
  together with it, and its entry keeps its own meaning there.
\<close>

definition finite_program_condition ::
    "local_address option finite_native_system \<Rightarrow> local_address option definition_site \<Rightarrow>
      native_development_condition option" where
  "finite_program_condition Q e=map_option (\<lambda>(d,F,u). development_existing_condition d F u)
    (finite_install_source_entry (finite_guard_source True) None [0] Q e)"

theorem finite_program_condition_exact:
  assumes condition: "finite_program_condition Q e=Some C"
  shows "development_condition_holds C x y \<longleftrightarrow>
    (e,Pair_Term (decode_finite_term x) (decode_finite_term y))\<in>positive_meaning (decode_finite_system Q)"
proof -
  obtain d F u where installed: "finite_install_source_entry (finite_guard_source True) None [0] Q e=Some (d,F,u)"
    and actual: "C=development_existing_condition d F u"
    using condition by (auto simp: finite_program_condition_def)
  obtain P where extended: "finite_extend_source_native (finite_guard_source True) None [0] Q=Some (P,F,u)"
    using installed unfolding finite_install_source_entry_conditions by blast
  have ready_context: "finite_source_extension_context (finite_guard_source True) None [0] Q=Some P"
    using extended unfolding finite_extend_source_native_conditions by blast
  obtain T where native: "native_package_at (decode_finite_environment F) u [] T"
    and meaning: "\<forall>t. (d,t)\<in>positive_meaning T \<longleftrightarrow> (e,t)\<in>positive_meaning (decode_finite_system Q)"
    using finite_install_source_entry_correct[OF installed ready_context] by blast
  show ?thesis by (simp only: actual development_existing_condition_exact[OF native] meaning)
qed

theorem finite_program_condition_total:
  "(\<exists>C. finite_program_condition Q e=Some C) \<longleftrightarrow> e |\<in>| finite_system_definitions Q \<and>
    (\<exists>P. finite_source_extension_context (finite_guard_source True) None [0] Q=Some P)"
proof -
  have "(\<exists>C. finite_program_condition Q e=Some C) \<longleftrightarrow>
      (\<exists>d F u. finite_install_source_entry (finite_guard_source True) None [0] Q e=Some (d,F,u))"
    by (cases "finite_install_source_entry (finite_guard_source True) None [0] Q e")
      (auto simp: finite_program_condition_def)
  then show ?thesis by (simp only: finite_install_source_entry_total)
qed

definition development_scope_pattern :: "bool \<Rightarrow> local_address finite_term_pattern" where
  "development_scope_pattern nonempty=Finite_Pattern_Pair (Finite_Variable [0])
    (Finite_Pattern_Pair (if nonempty then Finite_Pattern_Pair (Finite_Variable [1]) (Finite_Variable [2])
      else Finite_Pattern_Payload []) (Finite_Pattern_Pair (Finite_Variable [3]) (Finite_Pattern_Payload [])))"

definition development_scope_condition :: "bool \<Rightarrow> native_development_condition" where
  "development_scope_condition nonempty=(let pattern=development_scope_pattern nonempty;
    rule=\<lparr>finite_schema_conclusion=Finite_Pattern_Pair pattern pattern,
      finite_schema_premises={||},finite_schema_materials={||}\<rparr> in
    case finite_program_condition (finite_add_view_definition (finite_guard_source_program True) (Some [],[])
      (Finite_Variable []) {|([],rule)|}) (Some [],[]) of
      None \<Rightarrow> development_formed_condition\<lparr>condition_source_root:=[255]\<rparr> | Some C \<Rightarrow> C)"

definition development_generated_question :: "bool \<Rightarrow> nat \<Rightarrow> native_development_question" where
  "development_generated_question b copies=(let S=(case workflow_generating_stage b copies of None \<Rightarrow>
    (workflow_guard_stage True Workflow_Input)\<lparr>workflow_source_root:=[255]\<rparr> | Some S \<Rightarrow> S) in
    \<lparr>development_source=workflow_source S,development_source_use=workflow_source_use S,
      development_source_root=workflow_source_root S,development_generator_entry=workflow_entry S,
      development_problem=Finite_Payload [],development_conditions=[development_formed_condition],
      development_scope_criticism=development_scope_condition True,development_selected_facets=[]\<rparr>)"

definition development_case_inputs :: "native_development_question list" where
  "development_case_inputs=(let Q=development_generated_question True 1;
    equality=development_formed_condition\<lparr>condition_source:=finite_guard_source False\<rparr>;
    missing=(development_scope_criticism Q)\<lparr>condition_source_root:=[255]\<rparr>;
    nested=development_formed_condition\<lparr>condition_goals:=[Paired_Admission
      (Existing_Admission (None,[1])) (Collected_Admission (Existing_Admission (None,[1])))]\<rparr> in
    [Q,development_generated_question True 2,Q\<lparr>development_conditions:=[equality]\<rparr>,
      development_generated_question False 1,Q\<lparr>development_scope_criticism:=missing\<rparr>,
      Q\<lparr>development_scope_criticism:=development_scope_condition False\<rparr>,
      Q\<lparr>development_problem:=Finite_Payload [256]\<rparr>,
      Q\<lparr>development_conditions:=[nested,development_formed_condition],development_selected_facets:=[0]\<rparr>])"

definition development_case_at where
  "development_case_at w=(if w<length development_case_inputs then development_case_inputs!w
    else development_generated_question True 1)"

definition development_remove_certificates :: "native_condition_execution \<Rightarrow> native_condition_execution" where
  "development_remove_certificates execution=(case execution of (S,P,D,A,T,ys) \<Rightarrow> (S,P,D,A,{||},ys))"

definition development_producer_from ::
    "nat \<Rightarrow> native_development_question \<Rightarrow> native_development_report \<Rightarrow> finite_factor_term list option \<Rightarrow> native_development_report\<times>finite_factor_term list option" where
  "development_producer_from m Q report decision=(
    if m=1 then (report\<lparr>development_scope_review:=None\<rparr>,decision)
    else if m=2 then (report\<lparr>development_observed_conditions:=map_option
      (map (map_option development_remove_certificates)) (development_observed_conditions report)\<rparr>,decision)
    else if m=3 then (report\<lparr>development_generation:=map_option (\<lambda>(P,D,A,rows). (P,D,A,drop 1 rows))
      (development_generation report)\<rparr>,decision)
    else if m=4 then (report\<lparr>development_compiled_conditions:=None\<rparr>,decision)
    else if m=5 then (report\<lparr>development_comparison:=None\<rparr>,decision)
    else if m=6 then (report\<lparr>development_revision:=None\<rparr>,decision)
    else if m=7 then (let other=Q\<lparr>development_problem:=Finite_Pair (development_problem Q) (development_problem Q)\<rparr>;
      altered=construct_native_development other in (altered,native_development_admission other altered))
    else if m=8 then (report,map_option (take 1) decision)
    else if m=9 then (let other=Q\<lparr>development_scope_criticism:=development_formed_condition\<rparr>;
      altered=construct_native_development other in (altered,native_development_admission other altered))
    else (report,decision))"

definition development_producer where
  "development_producer m Q=(let report=construct_native_development Q in
    development_producer_from m Q report (native_development_admission Q report))"

text \<open>
  The scope critic is an actual installed native clause. Its pattern inspects
  the whole candidate-list field of the complete review input, distinguishing
  a nonempty family from the empty family. The contrasting critic requires an
  empty family. Native execution, not a supplied outcome, decides each request.
  Other sources include equality, whole formed-term admission and nested goals.
  Producers remove complete operations or certificates, lose a generated row,
  change the original question, discard duplicate answers or replace the
  original native scope critic. Every complete subject is retained.
\<close>

end
