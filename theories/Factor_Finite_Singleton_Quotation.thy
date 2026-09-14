theory Factor_Finite_Singleton_Quotation
  imports Factor_Finite_Complete_Quotation
begin

lemma finite_target_readings_without_bindings:
  assumes empty: "finite_environment_bindings E={||}"
  shows "finite_target_readings E u C r={||}"
proof -
  have each: "(if finite_citation_slots c={||} then {||}
      else fimage (\<lambda>T. (Finite_Target T,I,finite_citation_slots c)) (finite_citation_targets E u c))={||}"
    for c I
    by (cases c) (simp_all add: finite_bound_artifacts_def empty fset_inject[symmetric] ffilter.rep_eq)
  show ?thesis by (rule fset_inject[THEN iffD1])
    (auto simp: finite_target_readings_def each case_prod_unfold ffUnion.rep_eq fimage.rep_eq)
qed

lemma finite_singleton_artifacts:
  "finite_artifacts_at (finite_singleton_environment C) ()={|C|}"
  by (simp add: finite_singleton_environment_def finite_enumerated_environment_def finite_artifacts_at_def
    fset_inject[symmetric] fimage.rep_eq ffilter.rep_eq)

lemma finite_singleton_formed:
  "finite_environment_formed (finite_singleton_environment C) \<longleftrightarrow> finite_exact_formed C"
  by (simp add: finite_singleton_environment_def finite_enumerated_environment_def finite_environment_formed_def finite_relation_functional_def)

lemma finite_singleton_bound_readings_step:
  "finite_term_readings_bounded (Suc n) (finite_singleton_environment C) () r=
    (if finite_exact_formed C then finite_payload_readings C r |\<union>|
      finite_record_readings C r Finite_Pair {||}
        (finite_term_readings_bounded n (finite_singleton_environment C) ()) else {||})"
proof -
  have target: "finite_target_readings (finite_singleton_environment C) () C r={||}"
    by (rule finite_target_readings_without_bindings) (simp add: finite_singleton_environment_def finite_enumerated_environment_def)
  show ?thesis by (simp add: finite_term_readings_bounded.simps finite_singleton_formed
    finite_singleton_artifacts target)
qed

lemma finite_singleton_bound_readings:
  "finite_term_readings (finite_singleton_environment C) () r=
    finite_term_readings_bounded (fcard (finite_carrier (finite_structure C))) (finite_singleton_environment C) () r"
  by (simp add: finite_term_readings_def finite_singleton_artifacts)

end
