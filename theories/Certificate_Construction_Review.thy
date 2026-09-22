theory Certificate_Construction_Review
  imports Faceted_Native_Questions Factor_Finite_Program_Proofs
    Factor_Finite_Proof_Checking "HOL-Library.Parallel"
begin

datatype certificate_constructor = Head_Proof_Closure | Head_Proof_Round | Unchecked_Leaves
datatype certificate_facet = Requested_Certificates | Checked_Certificates

fun certificate_constructor_run where
  "certificate_constructor_run Head_Proof_Closure P D =
    map_option snd (finite_program_proofs P D)"
| "certificate_constructor_run Head_Proof_Round P D =
    Some (finite_application_proofs (finite_program_applications P D) {||})"
| "certificate_constructor_run Unchecked_Leaves P D =
    Some (fimage (\<lambda>(d,c,t,V,H). ((d,t),Schema_Proof c V {||}))
      (finite_program_applications P D))"

fun certificate_observation where
  "certificate_observation P D None f = False"
| "certificate_observation P D (Some T) Requested_Certificates = (fimage fst T=D)"
| "certificate_observation P D (Some T) Checked_Certificates =
    fBall T (\<lambda>((d,t),p). finite_checks_schema_proof P p d t)"

fun certificate_requirement where
  "certificate_requirement P D None f = False"
| "certificate_requirement P D (Some T) Requested_Certificates =
    (image fst (fset T)=fset D)"
| "certificate_requirement P D (Some T) Checked_Certificates =
    (\<forall>((d,t),p)\<in>fset T. checks_schema_proof (decode_finite_system P)
      (decode_finite_proof p) d (decode_finite_term t))"

lemma certificate_observation_exact:
  "certificate_observation P D result f=certificate_requirement P D result f"
  by (cases result; cases f)
    (auto simp: fset_inject[symmetric] finite_checks_schema_proof_exact split: prod.splits)

definition certificate_constructor_family where
  "certificate_constructor_family methods P D =
    Parallel.map (\<lambda>m. certificate_constructor_run m P D) methods"

lemma certificate_constructor_family_exact:
  "certificate_constructor_family methods P D =
    map (\<lambda>m. certificate_constructor_run m P D) methods"
  by (simp only: certificate_constructor_family_def Parallel.map_def)

definition certificate_result_question where
  "certificate_result_question P D results facets =
    faceted_native_question results facets (certificate_observation P D)"

definition certificate_result_choice where
  "certificate_result_choice P D results facets report =
    keyed_admitted_choice (first_occurrence_key results) results
      (certificate_result_question P D results facets) report"

theorem certificate_result_choice_conditions:
  assumes chosen: "certificate_result_choice P D results facets report=Some result"
    and facet: "f\<in>set facets"
  shows "certificate_requirement P D result f"
  using keyed_admitted_choice_condition[OF first_occurrence_key_inj_on chosen[unfolded certificate_result_choice_def
    certificate_result_question_def] facet]
  by (simp only: certificate_observation_exact)

theorem certificate_result_choice_original:
  assumes chosen: "certificate_result_choice P D results facets report=Some (Some T)"
    and requested: "Requested_Certificates\<in>set facets"
    and checked: "Checked_Certificates\<in>set facets"
  shows "fimage fst T=D"
    "\<And>d t p. ((d,t),p) |\<in>| T \<Longrightarrow>
      checks_schema_proof (decode_finite_system P) (decode_finite_proof p) d (decode_finite_term t)"
    "\<And>d t. (d,t) |\<in>| D \<Longrightarrow> \<exists>p. ((d,t),p) |\<in>| T"
proof -
  have coverage: "image fst (fset T)=fset D"
    using certificate_result_choice_conditions[OF chosen requested] by simp
  show domain: "fimage fst T=D"
    using coverage by (simp only: fset_inject[symmetric] fimage.rep_eq)
  show "\<And>d t p. ((d,t),p) |\<in>| T \<Longrightarrow>
      checks_schema_proof (decode_finite_system P) (decode_finite_proof p) d (decode_finite_term t)"
    using certificate_result_choice_conditions[OF chosen checked] by auto
  show "\<And>d t. (d,t) |\<in>| D \<Longrightarrow> \<exists>p. ((d,t),p) |\<in>| T"
    by (simp only: domain[symmetric] finite_first_projection_member)
qed

lemma certificate_missing_refused:
  assumes chosen: "certificate_result_choice P D results facets report=Some result"
    and requested: "Requested_Certificates\<in>set facets"
  shows "result\<noteq>None"
  using certificate_result_choice_conditions[OF chosen requested] by (cases result) auto

text \<open>The independently stated requirements are exact coverage of the original
  demand and checking every returned proof in the original complete program.
  Candidate leaves that omit children are deliberately untrusted answers; they
  acquire no assertion merely by being constructed. Equal complete results are
  compared as values, so method names and duplicate occurrences confer no priority.
  Failure or ambiguity cannot authorize a constructor. Source placement, replay,
  owner policy and broader search completeness remain separate obligations.\<close>

ML \<open>val _ = (writeln "Certificate_Construction_Review_JOIN_BEGIN";
  Thm.consolidate @{thms certificate_observation_exact certificate_result_choice_conditions certificate_result_choice_original certificate_missing_refused};
  writeln "Certificate_Construction_Review_JOIN_END");\<close>

end
