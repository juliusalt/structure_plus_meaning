theory Factor_Composition_Investigation
  imports Candidate_Observations Factor_Component_Agreement Factor_System_Alpha
begin

section \<open>A fixed definition boundary has complete structural observations\<close>

definition definition_observations ::
  "'d \<Rightarrow> ('a,'s,'d,'c) schema_system \<Rightarrow>
    ('a term_pattern set\<times>('c\<times>('a,'s,'d) factor_schema) set) set" where
  "definition_observations d P={({p. (d,p)\<in>system_interfaces P},system_clause_family P d)}"

theorem definition_observation_comparison:
  "candidate_profile U definition_observations P\<subseteq>candidate_profile U definition_observations Q
    \<longleftrightarrow> systems_agree_on P Q U"
  by (auto simp: candidate_profile_comparison definition_observations_def systems_agree_on_def
    set_eq_iff; blast)

theorem definition_observation_basis:
  "comparison_basis C (\<lambda>P Q. systems_agree_on P Q U) U definition_observations"
  by (simp add: comparison_basis_def definition_observation_comparison)

theorem definition_observation_loss:
  "(d,w)\<in>candidate_losses U definition_observations P Q \<longleftrightarrow>
    d\<in>U \<and> w=({p. (d,p)\<in>system_interfaces P},system_clause_family P d) \<and>
    \<not>systems_agree_on P Q {d}"
  by (auto simp: definition_observations_def systems_agree_on_def set_eq_iff; blast)

theorem definition_agreement_reduction:
  "exact_obligation_reduction UNIV (\<lambda>z. systems_agree_on (fst z) (snd z) U)
    (profile_condition definition_observations)
    (\<lambda>z. profile_obligations U definition_observations (fst z) (snd z))"
  using profile_comparison_reduction[where F=U and observe=definition_observations]
  by (simp only: definition_observation_comparison)

section \<open>Calls and consequences can miss a material difference that prevents sharing\<close>

abbreviation variable_interface_system :: "nat \<Rightarrow> (nat,nat,nat,nat) schema_system" where
  "variable_interface_system i \<equiv>
    \<lparr>system_interfaces={(0,Pattern_Variable i)},system_clauses={}\<rparr>"

lemma variable_interface_formed:
  "schema_system_formed (variable_interface_system i)"
  by (auto simp: schema_system_formed_def single_valued_def)

lemma variable_interface_calls:
  "schema_call_formed (variable_interface_system i) d t \<longleftrightarrow> d=0 \<and> term_formed t"
  by (simp add: schema_call_formed_def variable_interface_formed)

lemma variable_interface_consequences:
  "schema_consequences (variable_interface_system i) X={}"
  by (auto simp: schema_consequences_def admitted_schema_instance_def)

lemma variable_interface_meaning:
  "positive_meaning (variable_interface_system i)={}"
  using positive_meaning_least[where P="variable_interface_system i" and X="{}"]
  by (simp add: variable_interface_consequences)

theorem semantic_equality_can_miss_an_incompatible_interface:
  assumes "i\<noteq>j"
  shows "(\<forall>d t. schema_call_formed (variable_interface_system i) d t \<longleftrightarrow>
      schema_call_formed (variable_interface_system j) d t)"
    and "schema_consequences (variable_interface_system i)=schema_consequences (variable_interface_system j)"
    and "positive_meaning (variable_interface_system i)=positive_meaning (variable_interface_system j)"
    and "\<not>systems_agree_on (variable_interface_system i) (variable_interface_system j) {0}"
    and "\<not>schema_system_formed (system_union (variable_interface_system i) (variable_interface_system j))"
  using assms by (auto simp: variable_interface_calls variable_interface_consequences
    variable_interface_meaning systems_agree_on_def schema_system_formed_def single_valued_def
    fun_eq_iff)

theorem every_semantics_only_observation_misses_this_interface:
  fixes observe :: "'f \<Rightarrow> (nat,nat,nat,nat) schema_system \<Rightarrow> 'w set"
  assumes different: "i\<noteq>j"
    and invariant: "\<And>P Q f. schema_system_formed P \<Longrightarrow> schema_system_formed Q \<Longrightarrow>
      (\<And>d t. schema_call_formed P d t \<longleftrightarrow> schema_call_formed Q d t) \<Longrightarrow>
      schema_consequences P=schema_consequences Q \<Longrightarrow> positive_meaning P=positive_meaning Q \<Longrightarrow>
      observe f P=observe f Q"
  shows "(variable_interface_system i,variable_interface_system j)\<in>
    comparison_failures {P. schema_system_formed P}
      (\<lambda>P Q. systems_agree_on P Q {0}) F observe"
proof -
  have equal: "observe f (variable_interface_system i)=observe f (variable_interface_system j)" for f
    by (rule invariant[OF variable_interface_formed variable_interface_formed])
      (use semantic_equality_can_miss_an_incompatible_interface(1-3)[OF different] in auto)
  show ?thesis using semantic_equality_can_miss_an_incompatible_interface(4)[OF different]
    by (simp add: comparison_failures_def variable_interface_formed candidate_profile_comparison equal)
qed

section \<open>Changing overlap is an obligation and need not be a candidate order\<close>

theorem overlap_agreement_is_not_transitive:
  "\<exists>P Q T :: (nat,nat,nat,nat) schema_system.
    schema_system_formed P \<and> schema_system_formed Q \<and> schema_system_formed T \<and>
    systems_agree_on P Q (system_definitions P\<inter>system_definitions Q) \<and>
    systems_agree_on Q T (system_definitions Q\<inter>system_definitions T) \<and>
    \<not>systems_agree_on P T (system_definitions P\<inter>system_definitions T)"
proof -
  let ?P="variable_interface_system 0"
  let ?Q="\<lparr>system_interfaces={},system_clauses={}\<rparr> :: (nat,nat,nat,nat) schema_system"
  let ?T="variable_interface_system 1"
  show ?thesis by (rule exI[of _ ?P], rule exI[of _ ?Q], rule exI[of _ ?T])
    (auto simp: variable_interface_formed schema_system_formed_def single_valued_def
      systems_agree_on_def system_definitions_def rel_dom_def)
qed

theorem overlap_compatibility_has_no_exact_inclusion_basis:
  fixes observe :: "'f \<Rightarrow> (nat,nat,nat,nat) schema_system \<Rightarrow> 'w set"
  shows "\<not>comparison_basis {P. schema_system_formed P}
    (\<lambda>P Q. systems_agree_on P Q (system_definitions P\<inter>system_definitions Q)) F observe"
proof
  assume basis: "comparison_basis {P. schema_system_formed P}
    (\<lambda>P Q. systems_agree_on P Q (system_definitions P\<inter>system_definitions Q)) F observe"
  obtain P Q T :: "(nat,nat,nat,nat) schema_system" where formed:
    "schema_system_formed P" "schema_system_formed Q" "schema_system_formed T"
    and first: "systems_agree_on P Q (system_definitions P\<inter>system_definitions Q)"
    and second: "systems_agree_on Q T (system_definitions Q\<inter>system_definitions T)"
    and different: "\<not>systems_agree_on P T (system_definitions P\<inter>system_definitions T)"
    using overlap_agreement_is_not_transitive by blast
  have "systems_agree_on P T (system_definitions P\<inter>system_definitions T)"
    by (rule comparison_basis_requires_transitivity[OF basis _ _ _ first second])
      (use formed in auto)
  then show False using different by contradiction
qed

section \<open>Whole clause occurrences remain material even when their meanings agree\<close>

theorem equal_consequences_do_not_identify_clause_occurrences:
  fixes S :: "(nat,nat,nat) factor_schema"
  assumes formed: "schema_formed S" and closed: "schema_dependencies S\<subseteq>{0}"
    and different: "i\<noteq>j"
  defines "P \<equiv> \<lparr>system_interfaces={(0,Pattern_Variable 0)},system_clauses={((0,i),S)}\<rparr>"
    and "Q \<equiv> \<lparr>system_interfaces={(0,Pattern_Variable 0)},system_clauses={((0,j),S)}\<rparr>"
  shows "schema_system_formed P \<and> schema_system_formed Q"
    and "(\<forall>d t. schema_call_formed P d t \<longleftrightarrow> schema_call_formed Q d t)"
    and "schema_consequences P=schema_consequences Q"
    and "positive_meaning P=positive_meaning Q"
    and "\<not>systems_agree_on P Q {0}"
    and "schema_system_formed (system_union P Q)"
proof -
  have pf: "schema_system_formed P" and qf: "schema_system_formed Q"
    using formed closed by (auto simp: P_def Q_def schema_system_formed_def
      system_definitions_def rel_dom_def single_valued_def)
  have calls: "schema_call_formed P d t \<longleftrightarrow> schema_call_formed Q d t" for d t
    by (simp add: schema_call_formed_def P_def Q_def pf[unfolded P_def] qf[unfolded Q_def])
  have rules: "schema_consequences P=schema_consequences Q"
    by (rule ext, rule set_eqI)
      (auto simp: schema_consequence_rule P_def Q_def calls[unfolded P_def Q_def])
  show "schema_system_formed P \<and> schema_system_formed Q" using pf qf by blast
  show "\<forall>d t. schema_call_formed P d t \<longleftrightarrow> schema_call_formed Q d t"
    using calls by blast
  show "schema_consequences P=schema_consequences Q" by (rule rules)
  show "positive_meaning P=positive_meaning Q" by (simp only: positive_meaning_def rules)
  show "\<not>systems_agree_on P Q {0}"
    using different by (auto simp: systems_agree_on_def P_def Q_def)
  show "schema_system_formed (system_union P Q)"
    using formed closed different by (auto simp: P_def Q_def system_union_def schema_system_formed_def
      system_definitions_def rel_dom_def single_valued_def)
qed

text \<open>
  The requested physical composition retains the actual complete definitions.
  Matching calls, complete consequence operators, and least positive meanings
  does not establish that requirement. An independently changed interface
  binder can prevent the union from being formed. A different clause occurrence
  can preserve the same meaning and even permit a formed union while changing
  the material. Literal agreement is therefore a sufficient composition
  condition for the required preservation, not a characterization of every
  possible union that preserves meaning.

  A fixed boundary has an exact structural observation basis. Each observation
  is the complete interface fibre and identified clause family at one head,
  including empty fibres. Its loss reports the actual omitted material.
  The existing exact reduction consumes these observations. A lookup whose
  value is unspecified at an absent head could not supply this whole-domain
  account.

  Pairwise overlap changes with its arguments. It is not transitive even on
  formed programs, so no observation language can turn it into an exact
  profile-inclusion order on that whole domain. Fixing the relevant boundary
  yields the proved basis; checking the actual overlap remains a separate
  obligation. The common-component rule consequently requires a proof that
  the common boundary covers every shared head, and the union rule retains
  the separate component boundaries. Those rules now replace repeated
  agreement proofs in construction, related-test admission, and recorded-cause
  composition. They guide sharing of actual definitions before native clauses
  are assembled, without treating equivalent implementations as one material.
\<close>

end
