theory Development_Policy
  imports Isabelle_Acceptance Factor_Finite_Required_Causes
begin

section \<open>A policy admits exactly the presentations it lists\<close>

text \<open>
  A policy of the first loop states one original requirement over a ground program: an admitted
  payload is one of the presentations the program lists. The requirement is stated at the entry of
  that program, so its site is a definition of the source it is constructed over, and the
  constructed policy is supported rather than assumed. What a policy admits is fixed by the list it
  is constructed from, so a policy built from a different list admits a different family and a
  payload the list does not contain is refused. The list is computed by whoever constructs the
  policy; the policy's contract states exactly what it admits and nothing about why the list was
  chosen, which is the constructor's own contract.
\<close>

definition development_policy_source_with :: "finite_factor_term list \<Rightarrow>
    (local_address option definition_site\<times>local_address option finite_artifact_environment\<times>local_address option) option" where
  "development_policy_source_with xs=(case finite_ground_source xs of
     None \<Rightarrow> None
   | Some (d,F,u) \<Rightarrow> finite_construct_source_requirements F u [] [Existing_Admission d])"

theorem development_policy_with_exact:
  assumes policy: "development_policy_source_with xs=Some (p,K,pu)"
    and package: "native_package_at (decode_finite_environment K) pu [] T"
  shows "(p,t)\<in>positive_meaning T \<longleftrightarrow> t\<in>decode_finite_term ` set xs"
proof -
  obtain d F u where source: "finite_ground_source xs=Some (d,F,u)"
    using policy by (auto simp: development_policy_source_with_def split: option.splits)
  have built: "finite_construct_source_requirements F u [] [Existing_Admission d]=Some (p,K,pu)"
    using policy by (simp only: development_policy_source_with_def source option.case prod.case)
  obtain P Q e' T' where ground: "native_package_at (decode_finite_environment F) u [] (decode_finite_system P)"
    and installed: "native_package_at (decode_finite_environment K) pu [] T'"
    and meaning: "\<forall>t. (p,t)\<in>positive_meaning T' \<longleftrightarrow>
      admission_requirements_hold (positive_meaning (decode_finite_system P)) [Existing_Admission d] t"
    using finite_construct_source_requirements_correct[OF built] by blast
  obtain P' where ground': "native_package_at (decode_finite_environment F) u [] P'"
    and listed: "\<forall>t. (d,t)\<in>positive_meaning P' \<longleftrightarrow> t\<in>decode_finite_term ` set xs"
    by (rule finite_ground_source_meaning[OF source])
  have same: "decode_finite_system P=P'" by (rule native_package_unique[OF ground ground'])
  have entry: "T=T'" by (rule native_package_unique[OF package installed])
  have formed: "list_all finite_term_formed xs"
    using source by (auto simp: finite_ground_source_def split: if_splits)
  have listed_formed: "term_formed t" if "t\<in>decode_finite_term ` set xs" for t
    using that formed by (auto simp: list_all_iff finite_term_formed_correct)
  show ?thesis
    using meaning entry listed same listed_formed by (auto simp: admission_requirements_hold_def)
qed

lemma development_policy_with_package:
  assumes policy: "development_policy_source_with xs=Some (p,K,pu)"
  obtains T where "native_package_at (decode_finite_environment K) pu [] T"
proof -
  obtain d F u where source: "finite_ground_source xs=Some (d,F,u)"
    using policy by (auto simp: development_policy_source_with_def split: option.splits)
  have built: "finite_construct_source_requirements F u [] [Existing_Admission d]=Some (p,K,pu)"
    using policy by (simp only: development_policy_source_with_def source option.case prod.case)
  show thesis using finite_construct_source_requirements_correct[OF built] that by blast
qed

section \<open>The first loop admits only what the checked context accepted\<close>

text \<open>
  The entity policy lists the presentations of the checked context's entities, which is exactly
  the ground program of acceptance: acceptance is consumed as the member reading of that entry,
  not re-derived here.
\<close>

definition development_policy_source where
  "development_policy_source es=(case isabelle_acceptance_source es of
     None \<Rightarrow> None
   | Some (d,F,u) \<Rightarrow> finite_construct_source_requirements F u [] [Existing_Admission d])"

lemma development_policy_source_listed:
  "development_policy_source es=development_policy_source_with (map isabelle_entity_data es)"
  by (simp add: development_policy_source_def development_policy_source_with_def isabelle_acceptance_source_def)

theorem development_policy_admits_accepted:
  assumes policy: "development_policy_source es=Some (p,K,pu)"
    and package: "native_package_at (decode_finite_environment K) pu [] T"
    and admitted: "(p,t)\<in>positive_meaning T"
  shows "\<exists>e\<in>set es. t=decode_finite_term (isabelle_entity_data e)"
  using development_policy_with_exact[OF policy[unfolded development_policy_source_listed] package] admitted
  by auto

theorem development_policy_admits_member:
  assumes policy: "development_policy_source es=Some (p,K,pu)"
    and package: "native_package_at (decode_finite_environment K) pu [] T"
    and member: "e\<in>set es"
  shows "(p,decode_finite_term (isabelle_entity_data e))\<in>positive_meaning T"
  using development_policy_with_exact[OF policy[unfolded development_policy_source_listed] package] member
  by auto

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
