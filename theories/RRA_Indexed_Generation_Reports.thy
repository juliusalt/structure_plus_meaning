theory RRA_Indexed_Generation_Reports
  imports RRA_Digit_Environment_Loading Finite_Prepared_Results Finite_Relation_Reader_Assessments
begin

type_synonym generation_reading_query = "local_address option definition_site\<times>finite_generation"
type_synonym generation_reading_fields =
  "finite_exact_target\<times>(local_address\<times>local_address) fset\<times>finite_exact_target\<times>finite_exact_target"
type_synonym generation_reading_value =
  "bool\<times>(local_address option definition_site\<times>finite_exact_artifact) list option\<times>
    (generation_reading_query\<times>generation_reading_fields fset\<times>bool\<times>finite_exact_artifact option) list"
type_synonym indexed_generation_subject =
  "digit_allocated_environment option\<times>finite_exact_target\<times>finite_exact_target\<times>finite_exact_target\<times>
    generation_reading_query list\<times>generation_reading_query list"

definition generation_reading_report where
  "generation_reading_report read_fields checked anchor ready l p c rows queries=(
    ready l p c rows,keyed_option_map anchor (map fst rows),
    map (\<lambda>(d,G). ((d,G),read_fields (fst d) (snd d),checked G (fst d) (snd d),anchor d)) queries)"

definition finite_generation_reading_report where
  "finite_generation_reading_report E=generation_reading_report (finite_generation_field_readings E)
    (\<lambda>G. finite_check_generation G E) (finite_anchor_artifact E) (finite_generation_record_ready E)"

definition digit_generation_reading_report where
  "digit_generation_reading_report q=generation_reading_report (digit_generation_fields q)
    (digit_check_generation q) (digit_generation_anchor q) (digit_generation_ready q)"

theorem digit_generation_report_exact:
  "digit_generation_reading_report q l p c rows queries=
    finite_generation_reading_report (snd (digit_allocated_view q)) l p c rows queries"
  by (simp add: digit_generation_reading_report_def finite_generation_reading_report_def
    generation_reading_report_def digit_generation_fields_exact digit_generation_check_exact
    digit_generation_anchor_exact[abs_def] digit_generation_readiness_exact)

definition indexed_generation_relation :: "indexed_generation_subject\<Rightarrow>generation_reading_value\<Rightarrow>bool" where
  "indexed_generation_relation X result=(case X of (input,l,p,c,rows,queries) \<Rightarrow>
    \<exists>q. input=Some q \<and>
      result=finite_generation_reading_report (snd (digit_allocated_view q)) l p c rows queries)"

definition indexed_generation_reference where
  "indexed_generation_reference X=(case X of (input,l,p,c,rows,queries) \<Rightarrow>
    finite_prepared_results (\<lambda>q. finite_generation_reading_report (snd (digit_allocated_view q)) l p c rows queries) input)"

theorem indexed_generation_reference_exact:
  "result |\<in>| indexed_generation_reference X \<longleftrightarrow> indexed_generation_relation X result"
  by (simp only: indexed_generation_reference_def indexed_generation_relation_def
    finite_prepared_results_exact case_prod_unfold)

lemma load_digit_environment_observation:
  "map_option (\<lambda>q. observe (snd (digit_allocated_view q))) (load_digit_environment E)=
    (if finite_environment_formed E then Some (observe E) else None)"
proof -
  have composed: "map_option (\<lambda>q. observe (snd (digit_allocated_view q))) (load_digit_environment E)=
    map_option (\<lambda>(n,F). observe F) (map_option digit_allocated_view (load_digit_environment E))"
    by (simp add: option.map_comp comp_def case_prod_unfold)
  show ?thesis by (simp add: composed load_digit_environment_exact)
qed

text \<open>
  The independently established original field, recursive-check, readiness and
  anchor operations determine the complete report. Actual digit lookup readers
  recover it on every closed input. The input retains all requested sites,
  generations and their order; unavailable loading has no result family.
\<close>

end
