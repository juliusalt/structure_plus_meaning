theory Factor_Native_Requirement_Plans
  imports Factor_Checked_Requirement_Plans Factor_Native_System_Extensions
begin

section \<open>The admitted requirement plan extends its actual native source\<close>

theorem native_checked_requirement_package_total:
  fixes E :: "local_address option artifact_environment"
    and P :: "(nat,nat,nat,nat) schema_system"
    and g :: "nat\<Rightarrow>local_address option definition_site"
  assumes native: "native_package_at E pu pr N"
    and source: "schema_system_formed P" and injective: "inj_on g (system_definitions P)"
    and source_variant: "system_alpha_variant (rename_system g P) N"
    and plan: "(367,admission_plan_argument (data_list_term (map admission_goal_value gs)) (admission_counter n)
      (data_list_term (map admission_counter ds)) (admission_counter k)
      (data_list_term (map admission_instruction_value cs)))
        \<in>positive_meaning (admission_request_system (system_definitions P))"
  shows "\<exists>F h v T. environment_formed F \<and> environment_included E F \<and>
    native_package_at F pu pr N \<and> native_package_at F v [] T \<and>
    inj_on h (system_definitions (required_admission_system P ds k cs)) \<and>
    (\<forall>d\<in>system_definitions P. h d=g d) \<and>
    system_definitions T=h ` system_definitions (required_admission_system P ds k cs) \<and>
    system_alpha_variant (rename_system h (required_admission_system P ds k cs)) T \<and>
    positive_meaning T=map_prod h id ` positive_meaning (required_admission_system P ds k cs) \<and>
    h k\<in>system_definitions T \<and> fst (h k)\<notin>environment_uses E \<and> snd (h k)=[] \<and>
    (\<forall>t. schema_call_formed T (h k) t \<longleftrightarrow> term_formed t) \<and>
    (\<forall>t. (h k,t)\<in>positive_meaning T \<longleftrightarrow> term_formed t \<and>
      (\<forall>q\<in>set gs. admission_goal_holds
        {(d,x). d\<in>system_definitions P \<and> (g d,x)\<in>positive_meaning N} q t)) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A) \<and>
    (\<forall>w\<in>environment_uses E. \<forall>s z. binds_slot F w s z \<longleftrightarrow> binds_slot E w s z)"
proof -
  let ?Q="required_admission_system P ds k cs"
  have extension: "admission_extension P ?Q"
    by (rule checked_native_requirement_installation(2)[OF source plan])
  have formed: "schema_system_formed ?Q" and agreement: "systems_agree_on P ?Q (system_definitions P)"
    using extension by (auto simp: admission_extension_def)
  have entry: "k\<in>system_definitions ?Q" by simp
  have new: "k\<notin>system_definitions P"
    by (rule checked_native_requirement_installation(5)[OF source plan])
  obtain F h v T where installed: "environment_formed F" "environment_included E F"
    "native_package_at F pu pr N" "native_package_at F v [] T"
    "inj_on h (system_definitions ?Q)" "\<forall>d\<in>system_definitions P. h d=g d"
    "system_definitions T=h ` system_definitions ?Q"
    "system_alpha_variant (rename_system h ?Q) T"
    "positive_meaning T=map_prod h id ` positive_meaning ?Q"
    "\<forall>d\<in>system_definitions ?Q. \<forall>t.
      schema_call_formed T (h d) t \<longleftrightarrow> schema_call_formed ?Q d t"
    "\<forall>d\<in>system_definitions ?Q-system_definitions P.
      fst (h d)\<notin>environment_uses E \<and> snd (h d)=[]"
    "\<forall>w\<in>environment_uses E. \<forall>A. artifact_at F w A \<longleftrightarrow> artifact_at E w A"
    "\<forall>w\<in>environment_uses E. \<forall>s z. binds_slot F w s z \<longleftrightarrow> binds_slot E w s z"
    using native_mapped_extension_total[OF native source formed agreement injective source_variant]
    by (elim exE conjE) blast
  have member: "h k\<in>system_definitions T" using entry installed(7) by simp
  have fresh: "fst (h k)\<notin>environment_uses E" "snd (h k)=[]"
    using installed(11) entry new by blast+
  have calls: "\<forall>t. schema_call_formed T (h k) t \<longleftrightarrow> term_formed t"
    using installed(10) entry checked_native_requirement_installation(4)[OF source plan] by blast
  have source_meaning: "positive_meaning P=
    {(d,x). d\<in>system_definitions P \<and> (g d,x)\<in>positive_meaning N}"
    by (rule system_variant_renamed_meaning_source[OF source injective source_variant])
  have meaning: "\<forall>t. (h k,t)\<in>positive_meaning T \<longleftrightarrow> term_formed t \<and>
    (\<forall>q\<in>set gs. admission_goal_holds
      {(d,x). d\<in>system_definitions P \<and> (g d,x)\<in>positive_meaning N} q t)"
    by (simp only: system_variant_renamed_meaning_at[OF formed installed(5,8) entry]
      checked_native_requirement_installation(3)[OF source plan] source_meaning; simp)
  show ?thesis by (rule exI[of _ F], rule exI[of _ h], rule exI[of _ v], rule exI[of _ T])
    (use installed(1-9,12,13) member fresh calls meaning in blast)
qed

text \<open>
  The native planning verdict supplies the checked allocation and complete
  instruction sequence. The independent whole-program correspondence binds
  that plan to the actual retained source, including its interface and every
  clause. The existing pair, recursive list and conjunction contracts then
  determine the installed entry's meaning on every term. Every leaf queries
  the original native package at its unchanged mapped source address.

  This is the bootstrap construction and meaning theorem. The theorem does
  not turn its existential witnesses into an executed runtime constructor or
  admit a complete development record without its remaining native operations.
\<close>

end
