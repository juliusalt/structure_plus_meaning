theory Factor_Requirement_Installation
  imports Factor_Requirement_Guards Factor_View_Definitions
begin

definition install_requirement_guard ::
  "(nat,nat,nat,nat) schema_system \<Rightarrow> nat \<Rightarrow> (nat\<times>nat) set \<Rightarrow>
    (nat,nat,nat,nat) schema_system" where
  "install_requirement_guard P entry R=add_view_definition P entry data_x
    {(0,requirement_guard_schema R)}"

locale requirement_guard_extension =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry :: nat
    and requirements :: "(nat\<times>nat) set"
  assumes source_formed: "schema_system_formed P"
    and fresh: "entry\<notin>system_definitions P"
    and finite_requirements: "finite requirements"
    and functional_requirements: "single_valued requirements"
    and supported: "rel_ran requirements\<subseteq>system_definitions P"
begin

sublocale installed: positive_view P entry data_x "{(0,requirement_guard_schema requirements)}"
  by (rule positive_view.intro[OF source_formed fresh])
    (use requirement_guard_formed[OF finite_requirements functional_requirements] supported in
      \<open>auto simp: single_valued_def\<close>)

abbreviation guarded where
  "guarded \<equiv> install_requirement_guard P entry requirements"

lemma guarded_formed: "schema_system_formed guarded"
  using installed.formed by (simp only: install_requirement_guard_def)

lemma guarded_old_agreement:
  "systems_agree_on P guarded (system_definitions P)"
  using installed.old_agreement by (simp only: install_requirement_guard_def)

lemma guarded_call:
  "schema_call_formed guarded entry t \<longleftrightarrow> term_formed t"
  by (simp only: install_requirement_guard_def installed.view_call; simp)

lemma guarded_clauses:
  "((entry,c),S)\<in>system_clauses guarded \<longleftrightarrow>
    c=0 \<and> S=requirement_guard_schema requirements"
  using installed.no_old_clause by (auto simp: install_requirement_guard_def)

sublocale guard: requirement_guard_profile guarded entry requirements
  by (rule requirement_guard_profile.intro[OF guarded_formed guarded_clauses guarded_call])

theorem guarded_meaning:
  "(entry,t)\<in>positive_meaning guarded \<longleftrightarrow>
    term_formed t \<and> (\<forall>(s,d)\<in>requirements. (d,t)\<in>positive_meaning P)"
proof -
  have old: "(d,t)\<in>positive_meaning guarded \<longleftrightarrow> (d,t)\<in>positive_meaning P"
    if "(s,d)\<in>requirements" for s d
    using installed.old_meaning[of d t] supported that
    by (auto simp: install_requirement_guard_def rel_ran_def)
  show ?thesis by (simp only: guard.exact) (use old in blast)
qed

theorem no_self_requirement:
  "(s,entry)\<notin>requirements"
  using fresh supported by (auto simp: rel_ran_def)

theorem unchanged_original_meaning:
  assumes "d\<in>system_definitions P"
  shows "(d,t)\<in>positive_meaning guarded \<longleftrightarrow> (d,t)\<in>positive_meaning P"
  using installed.old_meaning[OF assms] by (simp only: install_requirement_guard_def)

text \<open>
  Installation happens over the actual already formed source program, with a
  fresh entry and complete dependency support. The source predicates keep
  their original meanings, and the new conclusion cannot be its own premise.
  The inherited native compilation exists before future subject arguments.
\<close>

end

end
