theory Factor_Amendment_Interpretations
  imports Factor_Historical_Programs Factor_Current_Entries Factor_Interpretation_Support
begin

section \<open>The current and candidate scopes fix the historical interpretation\<close>

definition amendment_interpretation_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "amendment_interpretation_at C q H M mu mr \<longleftrightarrow>
    (\<exists>A l G p E pu pr P d F qu qr Q a b N nu nr.
      current_entry_scope_quoted_at C q A l G p E pu pr P d \<and>
      generation_program_scope H F qu qr Q \<and>
      interpretation_support_at M mu mr a b N nu nr \<and> program_interpretation P Q a b)"

theorem amendment_interpretation_with_scopes:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
    and support: "interpretation_support_at M mu mr a b N nu nr"
  shows "amendment_interpretation_at C q H M mu mr \<longleftrightarrow> program_interpretation P Q a b"
proof
  assume interpreted: "amendment_interpretation_at C q H M mu mr"
  obtain A' l' G' p' E' pu' pr' P' d' F' qu' qr' Q' a' b' N' nu' nr' where other:
    "current_entry_scope_quoted_at C q A' l' G' p' E' pu' pr' P' d'"
    "generation_program_scope H F' qu' qr' Q'" "interpretation_support_at M mu mr a' b' N' nu' nr'"
    "program_interpretation P' Q' a' b'"
    using interpreted unfolding amendment_interpretation_at_def by blast
  have before: "P=P'" using current_entry_scope_unique[OF current other(1)] by blast
  have after: "Q=Q'" using generation_program_scope_unique[OF candidate other(2) refl] by blast
  have entries: "a=a' \<and> b=b'" using interpretation_support_at_unique[OF support other(3)] by blast
  show "program_interpretation P Q a b" using other(4) before after entries by simp
next
  assume "program_interpretation P Q a b"
  then show "amendment_interpretation_at C q H M mu mr"
    using current candidate support unfolding amendment_interpretation_at_def by blast
qed

theorem amendment_interpretation_entries:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
    and support: "interpretation_support_at M mu mr a b N nu nr"
    and interpreted: "amendment_interpretation_at C q H M mu mr"
  shows "{a,b}\<subseteq>system_definitions Q \<and> {a,b}\<subseteq>environment_positions F"
proof -
  have bridge: "program_interpretation P Q a b"
    using interpreted by (simp only: amendment_interpretation_with_scopes[OF current candidate support])
  have members: "a\<in>system_definitions Q" "b\<in>system_definitions Q"
    using bridge by (auto simp: program_interpretation_def)
  have package: "native_package_at F qu qr Q"
    using generation_program_scope_closed[OF candidate] by (simp add: closed_native_package_at_def)
  show ?thesis using members native_package_entry_position[OF package members(1)]
    native_package_entry_position[OF package members(2)] by blast
qed

theorem amendment_interpretation_missing_entry_rejected:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
    and support: "interpretation_support_at M mu mr a b N nu nr"
    and missing: "a\<notin>system_definitions Q \<or> b\<notin>system_definitions Q"
  shows "\<not>amendment_interpretation_at C q H M mu mr"
  using amendment_interpretation_entries[OF current candidate support] missing by blast

theorem amendment_interpretation_all_calls:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
    and support: "interpretation_support_at M mu mr a b N nu nr"
    and interpreted: "amendment_interpretation_at C q H M mu mr"
  shows "(a,Pair_Term (site_data_term (fst e) (snd e)) t)\<in>positive_meaning Q \<longleftrightarrow>
      schema_call_formed P e t"
    and "(b,Pair_Term (site_data_term (fst e) (snd e)) t)\<in>positive_meaning Q \<longleftrightarrow>
      (e,t)\<in>positive_meaning P"
proof -
  have bridge: "program_interpretation P Q a b"
    using interpreted by (simp only: amendment_interpretation_with_scopes[OF current candidate support])
  show "(a,Pair_Term (site_data_term (fst e) (snd e)) t)\<in>positive_meaning Q \<longleftrightarrow>
      schema_call_formed P e t"
    "(b,Pair_Term (site_data_term (fst e) (snd e)) t)\<in>positive_meaning Q \<longleftrightarrow>
      (e,t)\<in>positive_meaning P"
    by (rule program_interpretation_at_call[OF bridge])+
qed

theorem amendment_interpretation_total:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
    and bridge: "program_interpretation P Q a b"
    and remainder: "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>M. interpretation_support_at M None [] a b N nu nr \<and>
    amendment_interpretation_at C q H M None []"
proof -
  have package: "native_package_at F qu qr Q"
    using generation_program_scope_closed[OF candidate] by (simp add: closed_native_package_at_def)
  have formed: "environment_formed F"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have members: "a\<in>system_definitions Q" "b\<in>system_definitions Q"
    using bridge by (auto simp: program_interpretation_def)
  have addresses: "octets_formed (snd a)" "octets_formed (snd b)"
    using environment_position_address[OF formed native_package_entry_position[OF package members(1)]]
      environment_position_address[OF formed native_package_entry_position[OF package members(2)]] by auto
  obtain M where support: "interpretation_support_at M None [] a b N nu nr"
    using interpretation_support_total[OF addresses remainder] by blast
  have interpreted: "amendment_interpretation_at C q H M None []"
    using bridge by (simp only: amendment_interpretation_with_scopes[OF current candidate support])
  show ?thesis using support interpreted by blast
qed

section \<open>One constructed interpreter and value precede every candidate presentation\<close>

theorem current_interpretation_material_total:
  fixes Q :: "local_address option native_system"
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and other: "schema_system_formed Q"
    and remainder: "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>F v T a b M f g.
    closed_native_package_at F v [] T \<and> native_package_environment F v []=F \<and>
    program_interpretation P T a b \<and> a\<noteq>b \<and> interpretation_support_at M None [] a b N nu nr \<and>
    inj_on f (system_definitions P) \<and> inj_on g (system_definitions Q) \<and>
    f ` system_definitions P \<inter> g ` system_definitions Q={} \<and>
    {a,b} \<inter> (f ` system_definitions P \<union> g ` system_definitions Q)={} \<and>
    system_definitions T=insert b (insert a (f ` system_definitions P \<union> g ` system_definitions Q)) \<and>
    (\<forall>d\<in>system_definitions P. \<forall>t.
      (schema_call_formed T (f d) t \<longleftrightarrow> schema_call_formed P d t) \<and>
      ((f d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning P)) \<and>
    (\<forall>d\<in>system_definitions Q. \<forall>t.
      (schema_call_formed T (g d) t \<longleftrightarrow> schema_call_formed Q d t) \<and>
      ((g d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning Q)) \<and>
    (\<forall>H. generation_program_scope H F v [] T \<longrightarrow> amendment_interpretation_at C q H M None []) \<and>
    native_package_roots F v []=system_definitions T"
proof -
  have old: "closed_native_package_at E pu pr P" using current_entry_scope_closed[OF current] by blast
  obtain F v T a b f g Z where full:
    "closed_native_package_at F v [] T \<and> native_package_environment F v []=F \<and>
    program_scope_quoted_at Z [] E pu pr P \<and> program_interpretation P T a b \<and>
    a\<noteq>b \<and> inj_on f (system_definitions P) \<and> inj_on g (system_definitions Q) \<and>
    f ` system_definitions P \<inter> g ` system_definitions Q={} \<and>
    {a,b} \<inter> (f ` system_definitions P \<union> g ` system_definitions Q)={} \<and>
    system_definitions T=insert b (insert a (f ` system_definitions P \<union> g ` system_definitions Q)) \<and>
    (\<forall>d\<in>system_definitions P. \<forall>t.
      (schema_call_formed T (f d) t \<longleftrightarrow> schema_call_formed P d t) \<and>
      ((f d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning P)) \<and>
    (\<forall>d\<in>system_definitions Q. \<forall>t.
      (schema_call_formed T (g d) t \<longleftrightarrow> schema_call_formed Q d t) \<and>
      ((g d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning Q)) \<and>
    native_package_roots F v []=system_definitions T"
    using native_historical_program_total_with_roots[OF old other] by metis
  have compiled: "closed_native_package_at F v [] T"
    "native_package_environment F v []=F" "program_interpretation P T a b" "a\<noteq>b"
    "inj_on f (system_definitions P)" "inj_on g (system_definitions Q)"
    "f ` system_definitions P \<inter> g ` system_definitions Q={}"
    "{a,b} \<inter> (f ` system_definitions P \<union> g ` system_definitions Q)={}"
    "system_definitions T=insert b (insert a (f ` system_definitions P \<union> g ` system_definitions Q))"
    "\<forall>d\<in>system_definitions P. \<forall>t.
      (schema_call_formed T (f d) t \<longleftrightarrow> schema_call_formed P d t) \<and>
      ((f d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning P)"
    "\<forall>d\<in>system_definitions Q. \<forall>t.
      (schema_call_formed T (g d) t \<longleftrightarrow> schema_call_formed Q d t) \<and>
      ((g d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning Q)"
    "native_package_roots F v []=system_definitions T"
    using full by blast+
  have package: "native_package_at F v [] T" using compiled(1) by (simp add: closed_native_package_at_def)
  have formed: "environment_formed F"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have members: "a\<in>system_definitions T" "b\<in>system_definitions T"
    using compiled(3) by (auto simp: program_interpretation_def)
  have addresses: "octets_formed (snd a)" "octets_formed (snd b)"
    using environment_position_address[OF formed native_package_entry_position[OF package members(1)]]
      environment_position_address[OF formed native_package_entry_position[OF package members(2)]] by auto
  obtain M where support: "interpretation_support_at M None [] a b N nu nr"
    using interpretation_support_total[OF addresses remainder] by blast
  have future: "amendment_interpretation_at C q H M None []" if scope: "generation_program_scope H F v [] T" for H
    using compiled(3) by (simp only: amendment_interpretation_with_scopes[OF current scope support])
  show ?thesis by (rule exI[of _ F], rule exI[of _ v], rule exI[of _ T], rule exI[of _ a],
      rule exI[of _ b], rule exI[of _ M], rule exI[of _ f], rule exI[of _ g])
    (use compiled support future in blast)
qed

theorem amendment_interpretation_native_application:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H F qu qr Q"
    and support: "interpretation_support_at M mu mr a b N nu nr"
    and interpreted: "amendment_interpretation_at C q H M mu mr"
    and entry: "e\<in>{a,b}" and argument: "term_formed z"
  shows "\<exists>L au I K. environment_formed L \<and> environment_included F L \<and>
    native_package_at L qu qr Q \<and> native_package_environment L qu qr=F \<and>
    native_application_at L au [] e z I K \<and> native_application_formed L qu qr au [] \<and>
    (e=a \<longrightarrow> (native_positive_holds L qu qr au [] \<longleftrightarrow>
      (\<exists>c t. schema_call_formed P c t \<and> z=Pair_Term (site_data_term (fst c) (snd c)) t))) \<and>
    (e=b \<longrightarrow> (native_positive_holds L qu qr au [] \<longleftrightarrow>
      (\<exists>c t. (c,t)\<in>positive_meaning P \<and> z=Pair_Term (site_data_term (fst c) (snd c)) t)))"
proof -
  have package: "closed_native_package_at F qu qr Q" using generation_program_scope_closed[OF candidate] by blast
  have bridge: "program_interpretation P Q a b"
    using interpreted by (simp only: amendment_interpretation_with_scopes[OF current candidate support])
  show ?thesis by (rule program_interpretation_native_application[OF package bridge entry argument])
qed

text \<open>
  The old context is the complete exact scope already retained by the current
  frame. The candidate payload supplies its own complete exact scope. The
  interpreter value repeats neither. Its entries must belong to that actual
  candidate program, and their meanings cover every old definition and every
  argument, independently of any comparison or affected-definition boundary.

  A finite interpreter and complete supporting value can be constructed before
  the candidate's cause, history, or adoption presentation. Every later formed
  generation carrying that exact program scope has the same interpretation.
  The constructed package selects every resulting definition as an actual root.
  Future native calls extend the candidate scope and retain its canonical
  environment while preserving the original call and truth equations.

  This profile binds an independently specified semantic contract. Native
  admission of a submitted interpreter's finite correctness evidence remains
  separate; the data reader does not establish that contract by itself.
\<close>

end
