theory Development_Policy
  imports Isabelle_Acceptance Factor_Finite_Required_Causes
begin

section \<open>The first loop admits only what the checked context accepted\<close>

text \<open>
  The policy of the first loop states one original requirement over the ground program of
  the state's entities: an admitted payload is the presentation of an accepted entity. The
  requirement is stated at the entry of that program, so its site is a definition of the
  source it is constructed over, and the constructed policy is supported rather than
  assumed. Acceptance is consumed as the member reading of that entry, not re-derived
  here. The policy is not a permission: what it admits is fixed by the entities the
  checked context supplied, so a policy built from a different entity list admits a
  different family, and a payload those entities do not contain is refused.
\<close>

definition development_policy_source where
  "development_policy_source es=(case isabelle_acceptance_source es of
     None \<Rightarrow> None
   | Some (d,F,u) \<Rightarrow> finite_construct_source_requirements F u [] [Existing_Admission d])"

theorem development_policy_admits_accepted:
  assumes policy: "development_policy_source es=Some (p,K,pu)"
    and package: "native_package_at (decode_finite_environment K) pu [] T"
    and admitted: "(p,t)\<in>positive_meaning T"
  shows "\<exists>e\<in>set es. t=decode_finite_term (isabelle_entity_data e)"
proof -
  obtain d F u where source: "isabelle_acceptance_source es=Some (d,F,u)"
    using isabelle_acceptance_source_total by blast
  have built: "finite_construct_source_requirements F u [] [Existing_Admission d]=Some (p,K,pu)"
    using policy by (simp only: development_policy_source_def source option.case prod.case)
  obtain P Q e' T' where ground: "native_package_at (decode_finite_environment F) u [] (decode_finite_system P)"
    and installed: "native_package_at (decode_finite_environment K) pu [] T'"
    and meaning: "\<forall>t. (p,t)\<in>positive_meaning T' \<longleftrightarrow>
      admission_requirements_hold (positive_meaning (decode_finite_system P)) [Existing_Admission d] t"
    using finite_construct_source_requirements_correct[OF built] by blast
  have entry: "T=T'" by (rule native_package_unique[OF package installed])
  have held: "admission_requirements_hold (positive_meaning (decode_finite_system P)) [Existing_Admission d] t"
    using admitted meaning entry by simp
  then have member: "(d,t)\<in>positive_meaning (decode_finite_system P)"
    by (simp add: admission_requirements_hold_def)
  show ?thesis using member by (simp only: isabelle_acceptance_members[OF source ground])
qed

theorem development_policy_admits_member:
  assumes policy: "development_policy_source es=Some (p,K,pu)"
    and package: "native_package_at (decode_finite_environment K) pu [] T"
    and member: "e\<in>set es"
  shows "(p,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning T"
proof -
  obtain d F u where source: "isabelle_acceptance_source es=Some (d,F,u)"
    using isabelle_acceptance_source_total by blast
  have built: "finite_construct_source_requirements F u [] [Existing_Admission d]=Some (p,K,pu)"
    using policy by (simp only: development_policy_source_def source option.case prod.case)
  obtain P Q e' T' where ground: "native_package_at (decode_finite_environment F) u [] (decode_finite_system P)"
    and installed: "native_package_at (decode_finite_environment K) pu [] T'"
    and meaning: "\<forall>t. (p,t)\<in>positive_meaning T' \<longleftrightarrow>
      admission_requirements_hold (positive_meaning (decode_finite_system P)) [Existing_Admission d] t"
    using finite_construct_source_requirements_correct[OF built] by blast
  have entry: "T=T'" by (rule native_package_unique[OF package installed])
  have "(d,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning (decode_finite_system P)"
    using member by (simp only: isabelle_acceptance_members[OF source ground]) blast
  moreover have "term_formed (decode_finite_term (isabelle_entity_data e))"
    using isabelle_entity_data_formed[of e] by (simp only: finite_term_formed_correct)
  ultimately have "admission_requirements_hold (positive_meaning (decode_finite_system P)) [Existing_Admission d]
      (decode_finite_term (isabelle_entity_data e))"
    by (simp add: admission_requirements_hold_def)
  then show ?thesis using meaning entry by simp
qed

text \<open>
  The admitted family is exactly the accepted entities: nothing else satisfies the
  requirement, so a permissive substitute cannot be slipped in under the same entry.
\<close>

theorem development_policy_refuses_absent:
  assumes policy: "development_policy_source es=Some (p,K,pu)"
    and package: "native_package_at (decode_finite_environment K) pu [] T"
    and absent: "e\<notin>set es"
  shows "(p,decode_finite_term (isabelle_entity_data e))\<notin>positive_meaning T"
proof
  assume "(p,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning T"
  then obtain g where member: "g\<in>set es"
    and same: "decode_finite_term (isabelle_entity_data e)=decode_finite_term (isabelle_entity_data g)"
    using development_policy_admits_accepted[OF policy package] by blast
  have "e=g" using same by (simp add: inj_eq[OF isabelle_entity_data_injective])
  then show False using member absent by simp
qed

end
