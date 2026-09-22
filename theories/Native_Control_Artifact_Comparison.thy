theory Native_Control_Artifact_Comparison
  imports Native_Control_Literal_Boundary Factor_Finite_Prepared_Data_Readings RRA_Data_Enumerations
begin

text \<open>The actual subject retains the complete submitted artifact, its proposed
  quotation root, and the complete context/proposition judgment. The original
  condition is complete quotation of that judgment and its established truth.
  A root is a presented witness, not authority for ignoring other material.\<close>

type_synonym judgment_artifact_subject =
  "finite_exact_artifact \<times> local_address \<times> syntax_judgment_subject"

definition judgment_artifact_condition :: "judgment_artifact_subject \<Rightarrow> bool" where
  "judgment_artifact_condition q=(case q of (R,r,s) \<Rightarrow>
    complete_data_quoted_at (decode_finite_object R) r
      (decode_finite_term (syntax_judgment_data s)) \<and> syntax_judgment_truth s)"

definition judgment_artifact_check :: "judgment_artifact_subject \<Rightarrow> bool" where
  "judgment_artifact_check q=(case q of (R,r,s) \<Rightarrow>
    syntax_judgment_data s |\<in>| finite_complete_data_readings_prepared R r \<and>
      syntax_judgment_check s)"

lemma judgment_artifact_check_exact:
  "judgment_artifact_check q=judgment_artifact_condition q"
  by (cases q) (simp only: judgment_artifact_check_def judgment_artifact_condition_def
    case_prod_conv finite_complete_data_readings_prepared_exact
    finite_complete_data_readings_exact syntax_judgment_check_exact)

datatype judgment_artifact_adapter = Direct_Body_Entry | Claimed_Body_Only |
  Canonical_Artifact_Only | Complete_Artifact_Body

fun judgment_artifact_result where
  "judgment_artifact_result Direct_Body_Entry q=False"
| "judgment_artifact_result Claimed_Body_Only (R,r,s)=syntax_judgment_check s"
| "judgment_artifact_result Canonical_Artifact_Only (R,r,s)=
    (R=finite_term_syntax (syntax_judgment_data s) \<and> r=[] \<and> syntax_judgment_check s)"
| "judgment_artifact_result Complete_Artifact_Body q=judgment_artifact_check q"

lemma direct_artifact_adapter_contract:
  assumes source: "judgment_bridge_source b=Some (d,F,u)"
    and package: "native_package_at (decode_finite_environment F) u [] P"
  shows "judgment_artifact_result Direct_Body_Entry (R,r,s) \<longleftrightarrow>
    (d,Target_Term (Whole_Artifact (decode_finite_object R)))\<in>positive_meaning P"
  using judgment_source_refuses_literal_target[OF source package] by simp

definition judgment_artifact_agreement where
  "judgment_artifact_agreement a subjects \<longleftrightarrow>
    (\<forall>q\<in>set subjects. judgment_artifact_result a q=judgment_artifact_condition q)"

definition judgment_artifact_observation where
  "judgment_artifact_observation a subjects=list_all
    (\<lambda>q. judgment_artifact_result a q=judgment_artifact_check q) subjects"

lemma judgment_artifact_observation_exact:
  "judgment_artifact_observation a subjects=judgment_artifact_agreement a subjects"
  by (simp only: judgment_artifact_observation_def judgment_artifact_agreement_def
    list_all_iff judgment_artifact_check_exact)

lemma complete_artifact_adapter_agrees:
  "judgment_artifact_agreement Complete_Artifact_Body subjects"
  by (simp add: judgment_artifact_agreement_def judgment_artifact_check_exact)

definition finite_artifact_readdress ::
  "(local_address \<Rightarrow> local_address) \<Rightarrow> finite_exact_artifact \<Rightarrow> finite_exact_artifact" where
  "finite_artifact_readdress f R=\<lparr>finite_structure=\<lparr>
    finite_carrier=fimage f (finite_carrier (finite_structure R)),
    finite_incidence=fimage (\<lambda>(a,p,x). (f a,f p,f x)) (finite_incidence (finite_structure R))\<rparr>,
    finite_data=\<lparr>finite_bag=image_mset (\<lambda>(a,v). (f a,v))
      (filter_mset (\<lambda>av. fst av |\<in>| finite_carrier (finite_structure R)) (finite_bag (finite_data R))),
      finite_bindings=fimage (\<lambda>(a,v). (f a,v)) (finite_bindings (finite_data R))\<rparr>\<rparr>"

lemma finite_attachment_push_count:
  assumes finite: "finite U"
  shows "count (image_mset (\<lambda>(a,v). (f a,v))
    (filter_mset (\<lambda>av. fst av\<in>U) B))=pushed_count U f (count B)"
proof -
  obtain xs where xs: "B=mset xs" using ex_mset[of B] by metis
  let ?ys="filter (\<lambda>av. fst av\<in>U) xs"
  have inside: "fst ` set ?ys\<subseteq>U" by auto
  have pushed: "count_list (pushed_attachment_list f ?ys)=pushed_count U f (count_list ?ys)"
    by (rule pushed_count_list[OF finite inside])
  have unchanged: "pushed_count U f (count_list ?ys)=pushed_count U f (count_list xs)"
    by (auto simp: pushed_count_def fun_eq_iff count_mset[symmetric] intro!: sum.cong)
  have target: "count (image_mset (\<lambda>(a,v). (f a,v))
      (filter_mset (\<lambda>av. fst av\<in>U) B)) = count_list (pushed_attachment_list f ?ys)"
    by (rule ext) (simp only: xs mset_filter[symmetric] mset_map[symmetric] count_mset)
  have counts: "count B=count_list xs" by (rule ext) (simp only: xs count_mset)
  show ?thesis by (simp only: target counts pushed unchanged)
qed

lemma finite_artifact_readdress_exact:
  "decode_finite_object (finite_artifact_readdress f R)=push_object f (decode_finite_object R)"
  by (simp add: finite_artifact_readdress_def decode_finite_object_def decode_finite_structure_def
    decode_finite_basis_def push_object_def push_structure_def push_basis_def fimage.rep_eq
    finite_attachment_push_count)

definition judgment_artifact_cases_for where
  "judgment_artifact_cases_for s=(let t=syntax_judgment_data s; R=finite_term_syntax t in
    [(R,[],s),(finite_artifact_readdress (Cons 7) R,[7],s),
      (finite_syntax_union R (finite_payload_syntax [9]),[2],s),
      (finite_term_syntax (Finite_Pair t (Finite_Payload [9])),[],s)])"

definition judgment_artifact_cases where
  "judgment_artifact_cases=concat (map judgment_artifact_cases_for syntax_judgment_cases)"

definition judgment_artifact_candidates where
  "judgment_artifact_candidates=[Direct_Body_Entry,Claimed_Body_Only,
    Canonical_Artifact_Only,Complete_Artifact_Body]"

definition judgment_artifact_question where
  "judgment_artifact_question subjects=keyed_development_question
    (first_occurrence_key judgment_artifact_candidates) judgment_artifact_candidates
    (\<lambda>a. judgment_artifact_observation a subjects)"

theorem judgment_artifact_admission:
  assumes question: "judgment_artifact_question subjects=Some Q"
    and admission: "native_development_admission Q report=Some accepted"
    and selected: "x\<in>set accepted"
  obtains a where "a\<in>set judgment_artifact_candidates"
    "x=finite_path (first_occurrence_key judgment_artifact_candidates a)"
    "judgment_artifact_agreement a subjects"
proof -
  obtain a where member: "a\<in>set judgment_artifact_candidates"
    and path: "x=finite_path (first_occurrence_key judgment_artifact_candidates a)"
    and observed: "judgment_artifact_observation a subjects"
    by (rule keyed_development_admission[OF question[unfolded judgment_artifact_question_def]
      admission selected])
  show thesis by (rule that[OF member path observed[unfolded judgment_artifact_observation_exact]])
qed

definition judgment_artifact_probe where
  "judgment_artifact_probe ignored=(finite_term_syntax
    (syntax_judgment_data (hd syntax_judgment_cases)),[],hd syntax_judgment_cases)"

definition judgment_artifact_execution_question where
  "judgment_artifact_execution_question ignored=judgment_artifact_question judgment_artifact_cases"

definition judgment_artifact_value where
  "judgment_artifact_value=finite_steered_development_value finite_development_question_value"

lemma judgment_artifact_value_injective: "inj judgment_artifact_value"
  unfolding judgment_artifact_value_def
  by (intro finite_development_values_injective finite_development_question_value_injective)

export_code judgment_artifact_probe judgment_artifact_check judgment_artifact_execution_question
  judgment_artifact_cases judgment_artifact_observation judgment_artifact_candidates judgment_steering_questions
  judgment_artifact_value context_execution_summary native_steered_development finite_term_shared_word_fold
  integer_of_nat fcard finite_carrier finite_structure syntax_judgment_data
  in Eval module_name Native_Control_Artifact file_prefix "native_control_artifact"

end
