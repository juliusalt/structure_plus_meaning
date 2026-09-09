theory Factor_Construction_Invariance
  imports Factor_Construction_Contracts Factor_Construction_Order_Audit Presentation_Generators Factor_Permission_Invariance
begin

section \<open>One complete unordered field changes at each step\<close>

definition construction_presentation_step :: "factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "construction_presentation_step p q \<longleftrightarrow>
    presentation_transport construction_account_presents construction_account_presents p q \<and>
    (\<exists>fs i v. i\<in>{1::nat,2,3} \<and> p=enumeration_term fs \<and>
      q=enumeration_term (fs[i:=v]))"

lemma construction_presentations_three_steps:
  assumes first: "construction_account_presents a p" and second: "construction_account_presents a q"
  shows "\<exists>u v. construction_presentation_step p u \<and>
    construction_presentation_step u v \<and> construction_presentation_step v q"
proof -
  let ?xs="fst (fst a)" and ?B="snd (fst a)" and ?W="snd a"
  let ?R="construction_account_output a"
  let ?x="artifact_list_term ?xs" and ?y="Target_Term (Whole_Artifact ?R)"
  have domain: "construction_account_domain a" using first by (simp add: construction_account_presents_def)
  obtain b s orig where left:
    "finite_table_presents Payload_Term (\<lambda>T u. u=Target_Term (Whole_Artifact T)) ?B b"
    "finite_table_presents Payload_Term construction_selection_presents (construction_selections ?W) s"
    "finite_table_presents construction_atom_term (\<lambda>a u. u=Payload_Term a) (construction_origins ?W) orig"
    and p: "p=enumeration_term [?x,b,s,orig,?y]"
    using first by (auto simp: construction_account_presents_def construction_claim_presents_def)
  obtain b' s' orig' where right:
    "finite_table_presents Payload_Term (\<lambda>T u. u=Target_Term (Whole_Artifact T)) ?B b'"
    "finite_table_presents Payload_Term construction_selection_presents (construction_selections ?W) s'"
    "finite_table_presents construction_atom_term (\<lambda>a u. u=Payload_Term a) (construction_origins ?W) orig'"
    and q: "q=enumeration_term [?x,b',s',orig',?y]"
    using second by (auto simp: construction_account_presents_def construction_claim_presents_def)
  let ?u="enumeration_term [?x,b',s,orig,?y]"
  let ?v="enumeration_term [?x,b',s',orig,?y]"
  have u: "construction_account_presents a ?u"
    using domain right(1) left(2,3)
    by (auto simp: construction_account_presents_def construction_claim_presents_def)
  have v: "construction_account_presents a ?v"
    using domain right(1,2) left(3)
    by (auto simp: construction_account_presents_def construction_claim_presents_def)
  have one: "construction_presentation_step p ?u"
  proof (unfold construction_presentation_step_def, rule conjI)
    show "presentation_transport construction_account_presents construction_account_presents p ?u"
      unfolding presentation_transport_def by (rule exI[of _ a]) (use first u in blast)
    show "\<exists>fs i w. i\<in>{1::nat,2,3} \<and> p=enumeration_term fs \<and> ?u=enumeration_term (fs[i:=w])"
      by (rule exI[of _ "[?x,b,s,orig,?y]"], rule exI[of _ 1], rule exI[of _ b']) (simp add: p)
  qed
  have two: "construction_presentation_step ?u ?v"
  proof (unfold construction_presentation_step_def, rule conjI)
    show "presentation_transport construction_account_presents construction_account_presents ?u ?v"
      unfolding presentation_transport_def by (rule exI[of _ a]) (use u v in blast)
    show "\<exists>fs i w. i\<in>{1::nat,2,3} \<and> ?u=enumeration_term fs \<and> ?v=enumeration_term (fs[i:=w])"
      by (rule exI[of _ "[?x,b',s,orig,?y]"], rule exI[of _ 2], rule exI[of _ s']) simp
  qed
  have three: "construction_presentation_step ?v q"
  proof (unfold construction_presentation_step_def, rule conjI)
    show "presentation_transport construction_account_presents construction_account_presents ?v q"
      unfolding presentation_transport_def by (rule exI[of _ a]) (use v second in blast)
    show "\<exists>fs i w. i\<in>{1::nat,2,3} \<and> ?v=enumeration_term fs \<and> q=enumeration_term (fs[i:=w])"
      by (rule exI[of _ "[?x,b',s',orig,?y]"], rule exI[of _ 3], rule exI[of _ orig']) (simp add: q)
  qed
  show ?thesis using one two three by blast
qed

interpretation construction_generators: presentation_generators construction_account_presents
  construction_account_domain "\<lambda>p. \<exists>a. construction_account_presents a p" construction_presentation_step
proof (rule presentation_generators.intro[OF construction_account_presentation_class]; unfold_locales)
  fix p q assume "construction_presentation_step p q"
  then show "presentation_transport construction_account_presents construction_account_presents p q"
    by (simp add: construction_presentation_step_def)
next
  fix p q assume "presentation_transport construction_account_presents construction_account_presents p q"
  then obtain a where read: "construction_account_presents a p" "construction_account_presents a q"
    by (auto simp: presentation_transport_def)
  obtain u v where steps: "construction_presentation_step p u" "construction_presentation_step u v"
    "construction_presentation_step v q" using construction_presentations_three_steps[OF read] by blast
  have one: "rtranclp construction_presentation_step p u"
    by (rule r_into_rtranclp) (rule steps(1))
  have two: "rtranclp construction_presentation_step p v"
    by (rule rtranclp.rtrancl_into_rtrancl) (rule one, rule steps(2))
  show "rtranclp construction_presentation_step p q"
    by (rule rtranclp.rtrancl_into_rtrancl) (rule two, rule steps(3))
qed

section \<open>Formation and truth use the same exact local criterion\<close>

theorem construction_permission_observations:
  "construction_permission_invariant P d \<longleftrightarrow>
    rel_fun (presentation_transport construction_account_presents construction_account_presents) (=)
      (schema_call_formed P d) (schema_call_formed P d) \<and>
    rel_fun (presentation_transport construction_account_presents construction_account_presents) (=)
      (\<lambda>t. (d,t)\<in>positive_meaning P) (\<lambda>t. (d,t)\<in>positive_meaning P)"
proof
  assume invariant: "construction_permission_invariant P d"
  have same: "(schema_call_formed P d t \<longleftrightarrow> schema_call_formed P d u) \<and>
      ((d,t)\<in>positive_meaning P \<longleftrightarrow> (d,u)\<in>positive_meaning P)"
    if related: "presentation_transport construction_account_presents construction_account_presents t u" for t u
  proof -
    obtain a where read: "construction_account_presents a t" "construction_account_presents a u"
      using related by (auto simp: presentation_transport_def)
    have built: "source_constructs (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a)"
      and coords: "construction_coordinates_formed (snd (fst a)) (snd a)"
      and first: "construction_claim_presents (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a) t"
      and second: "construction_claim_presents (fst (fst a)) (snd (fst a)) (snd a) (construction_account_output a) u"
      using read by (auto simp: construction_account_presents_def)
    show ?thesis using construction_permission_invariantD[OF invariant built coords first second] by blast
  qed
  show "rel_fun (presentation_transport construction_account_presents construction_account_presents) (=)
      (schema_call_formed P d) (schema_call_formed P d) \<and>
    rel_fun (presentation_transport construction_account_presents construction_account_presents) (=)
      (\<lambda>t. (d,t)\<in>positive_meaning P) (\<lambda>t. (d,t)\<in>positive_meaning P)"
    using same by (auto simp: rel_fun_def)
next
  assume both: "rel_fun (presentation_transport construction_account_presents construction_account_presents) (=)
      (schema_call_formed P d) (schema_call_formed P d) \<and>
    rel_fun (presentation_transport construction_account_presents construction_account_presents) (=)
      (\<lambda>t. (d,t)\<in>positive_meaning P) (\<lambda>t. (d,t)\<in>positive_meaning P)"
  show "construction_permission_invariant P d"
    unfolding construction_permission_invariant_def
  proof (intro allI impI)
    fix xs B W R t u assume built: "source_constructs xs B W R" and coords: "construction_coordinates_formed B W"
      and first: "construction_claim_presents xs B W R t" and second: "construction_claim_presents xs B W R u"
    have read: "construction_account_presents ((xs,B),W) t" "construction_account_presents ((xs,B),W) u"
      using built coords by (simp_all only: construction_account_at_claim[OF first] construction_account_at_claim[OF second])
    have related: "presentation_transport construction_account_presents construction_account_presents t u"
      using read by (auto simp: presentation_transport_def)
    show "(schema_call_formed P d t \<longleftrightarrow> schema_call_formed P d u) \<and>
      ((d,t)\<in>positive_meaning P \<longleftrightarrow> (d,u)\<in>positive_meaning P)"
      using both related by (auto simp: rel_fun_def)
  qed
qed

theorem construction_permission_local_iff:
  "construction_permission_invariant P d \<longleftrightarrow>
    rel_fun construction_presentation_step (=) (schema_call_formed P d) (schema_call_formed P d) \<and>
    rel_fun construction_presentation_step (=)
      (\<lambda>t. (d,t)\<in>positive_meaning P) (\<lambda>t. (d,t)\<in>positive_meaning P)"
  by (simp only: construction_permission_observations construction_generators.generator_observation_iff)

definition construction_permission_obligations where
  "construction_permission_obligations P d = obligation_substitution
    {(False,schema_call_formed P d),(True,\<lambda>t. (d,t)\<in>positive_meaning P)}
    (observation_obligations construction_presentation_step)"

theorem construction_permission_obligations_exact:
  "rel_ran (construction_permission_obligations P d)\<subseteq>{c. observation_condition c} \<longleftrightarrow>
    construction_permission_invariant P d"
  by (simp only: construction_permission_local_iff program_invariance_obligations_exact[symmetric]
    program_invariance_obligations_def construction_permission_obligations_def)

theorem construction_permission_reduction:
  "exact_obligation_reduction UNIV (\<lambda>z. construction_permission_invariant (fst z) (snd z))
    observation_condition (\<lambda>z. construction_permission_obligations (fst z) (snd z))"
  by (simp add: exact_obligation_reduction_def construction_permission_obligations_exact)

theorem construction_permission_residual_exact:
  assumes "K\<subseteq>{c. observation_condition c}"
  shows "construction_permission_invariant P d \<longleftrightarrow>
    rel_ran (remaining_obligations K (construction_permission_obligations P d))\<subseteq>{c. observation_condition c}"
  using exact_obligation_reduction_residual[OF construction_permission_reduction assms,
    unfolded exact_obligation_reduction_def, rule_format, where a="(P,d)"] by simp

theorem construction_permission_local_discharge:
  assumes "\<And>i c. (i,c)\<in>construction_permission_obligations P d \<Longrightarrow> observation_condition c"
  shows "construction_permission_invariant P d"
proof -
  have candidate: "construction_permission_invariant (fst (P,d)) (snd (P,d))"
  proof (rule obligation_reduction_discharge[where D=UNIV and a="(P,d)"
      and P="\<lambda>z. construction_permission_invariant (fst z) (snd z)"
      and Q=observation_condition and F="\<lambda>z. construction_permission_obligations (fst z) (snd z)"])
    show "obligation_reduction UNIV (\<lambda>z. construction_permission_invariant (fst z) (snd z))
      observation_condition (\<lambda>z. construction_permission_obligations (fst z) (snd z))"
      by (rule exact_obligation_reduction_sound[OF construction_permission_reduction])
    show "(P,d)\<in>UNIV" by simp
    fix i c assume "(i,c)\<in>(\<lambda>z. construction_permission_obligations (fst z) (snd z)) (P,d)"
    then show "observation_condition c" using assms by simp
  qed
  show ?thesis using candidate by simp
qed

theorem structural_permission_conditions_settled:
  "remaining_obligations {c. observation_condition c}
    (construction_permission_obligations construction_admission_system 250)={}"
  by (simp only: remaining_obligations_empty construction_permission_obligations_exact
    construction_structural_permission_invariant)

theorem order_sensitive_permission_has_a_residual:
  "remaining_obligations {c. observation_condition c}
    (construction_permission_obligations order_sensitive_construction_program ())\<noteq>{}"
  by (simp only: remaining_obligations_empty construction_permission_obligations_exact
    order_sensitive_construction_not_admitted; simp)

theorem completing_order_sensitive_truth_changes_the_answer:
  "saturate_observation construction_account_presents
      (\<lambda>t. ((),t)\<in>positive_meaning order_sensitive_construction_program) reversed_base_claim \<and>
    ((),reversed_base_claim)\<notin>positive_meaning order_sensitive_construction_program \<and>
    \<not>construction_permission_invariant order_sensitive_construction_program ()"
proof -
  have first: "construction_account_presents (([],order_audit_bases),empty_source_construction) order_audit_claim"
    using construction_account_at_claim[OF construction_claim_term_presents[OF order_audit_construction]]
      order_audit_construction order_audit_coordinates by blast
  have second: "construction_account_presents (([],order_audit_bases),empty_source_construction) reversed_base_claim"
    using construction_account_at_claim[OF reversed_base_claim_presents]
      order_audit_construction order_audit_coordinates by blast
  have completed: "saturate_observation construction_account_presents
      (\<lambda>t. ((),t)\<in>positive_meaning order_sensitive_construction_program) reversed_base_claim"
    using first second order_sensitive_construction_meaning(1)
    by (auto simp: saturate_observation_def presentation_transport_def)
  show ?thesis using completed order_sensitive_construction_meaning(2) order_sensitive_construction_not_admitted by blast
qed

text \<open>
  Every pair of complete presentations is connected by changing the base,
  selection, and origin fields in turn. All intermediate terms still present
  exactly the same complete valid account. Ordered inputs and the exact output
  remain fixed. A selection-field change includes its nested selected-set
  presentations. This is a three-field decomposition, not a claim that all
  internal checking work has constant size or has been reduced to atom swaps.

  The general generator theorem makes these local formation and truth
  obligations exactly the original global permission condition. The two roles
  retain separate occurrence keys, each qualified by its compared terms.
  The concrete structural checker discharges every condition; the existing
  order-sensitive program has a residual. Completing its truth would accept a
  previously rejected term and still would not admit the original program.
  No original program, permission judgment, or complete class is changed.
\<close>

end
