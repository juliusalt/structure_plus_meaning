theory Factor_Historical_Programs
  imports Factor_Historical_Views Factor_Program_Scopes
begin

section \<open>Two ordinary entries preserve the exact historical call boundary\<close>

definition program_interpretation ::
  "local_address option native_system \<Rightarrow> local_address option native_system \<Rightarrow>
    local_address option definition_site \<Rightarrow> local_address option definition_site \<Rightarrow> bool" where
  "program_interpretation P Q a b \<longleftrightarrow>
    schema_system_formed P \<and> schema_system_formed Q \<and>
    a\<in>system_definitions Q \<and> b\<in>system_definitions Q \<and>
    (\<forall>z. schema_call_formed Q a z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. schema_call_formed Q b z \<longleftrightarrow> term_formed z) \<and>
    (\<forall>z. (a,z)\<in>positive_meaning Q \<longleftrightarrow>
      (\<exists>d t. schema_call_formed P d t \<and> z=Pair_Term (site_data_term (fst d) (snd d)) t)) \<and>
    (\<forall>z. (b,z)\<in>positive_meaning Q \<longleftrightarrow>
      (\<exists>d t. (d,t)\<in>positive_meaning P \<and> z=Pair_Term (site_data_term (fst d) (snd d)) t))"

theorem program_interpretation_at_call:
  assumes bridge: "program_interpretation P Q a b"
  shows "(a,Pair_Term (site_data_term (fst d) (snd d)) t)\<in>positive_meaning Q \<longleftrightarrow>
      schema_call_formed P d t"
    and "(b,Pair_Term (site_data_term (fst d) (snd d)) t)\<in>positive_meaning Q \<longleftrightarrow>
      (d,t)\<in>positive_meaning P"
  using bridge by (auto simp: program_interpretation_def prod_eq_iff)

theorem program_interpretation_no_extra:
  assumes bridge: "program_interpretation P Q a b"
  shows "{z. (a,z)\<in>positive_meaning Q} =
      (\<lambda>(d,t). Pair_Term (site_data_term (fst d) (snd d)) t) `
        {(d,t). schema_call_formed P d t}"
    and "{z. (b,z)\<in>positive_meaning Q} =
      (\<lambda>(d,t). Pair_Term (site_data_term (fst d) (snd d)) t) ` positive_meaning P"
proof -
  let ?f="\<lambda>(d,t). Pair_Term (site_data_term (fst d) (snd d)) t"
  have projection: "?f ` S = {z. \<exists>d t. (d,t)\<in>S \<and> z=Pair_Term (site_data_term (fst d) (snd d)) t}" for S
  proof (rule set_eqI)
    fix z
    show "z\<in>?f ` S \<longleftrightarrow>
      z\<in>{z. \<exists>d t. (d,t)\<in>S \<and> z=Pair_Term (site_data_term (fst d) (snd d)) t}"
    proof
      assume "z\<in>?f ` S"
      then show "z\<in>{z. \<exists>d t. (d,t)\<in>S \<and> z=Pair_Term (site_data_term (fst d) (snd d)) t}"
        by auto
    next
      assume "z\<in>{z. \<exists>d t. (d,t)\<in>S \<and> z=Pair_Term (site_data_term (fst d) (snd d)) t}"
      then obtain d t where parts: "(d,t)\<in>S" "z=Pair_Term (site_data_term (fst d) (snd d)) t" by blast
      show "z\<in>?f ` S" by (rule rev_image_eqI[OF parts(1)]) (simp add: parts(2))
    qed
  qed
  show "{z. (a,z)\<in>positive_meaning Q}=?f ` {(d,t). schema_call_formed P d t}"
    using bridge by (auto simp: projection program_interpretation_def)
  show "{z. (b,z)\<in>positive_meaning Q}=?f ` positive_meaning P"
    using bridge by (auto simp: projection program_interpretation_def)
qed

theorem program_interpretation_composition:
  assumes first: "program_interpretation P Q a b"
    and second: "program_interpretation Q R c d"
  shows "(d,Pair_Term (site_data_term (fst a) (snd a)) z)\<in>positive_meaning R \<longleftrightarrow>
      (\<exists>e t. schema_call_formed P e t \<and> z=Pair_Term (site_data_term (fst e) (snd e)) t)"
    and "(d,Pair_Term (site_data_term (fst b) (snd b)) z)\<in>positive_meaning R \<longleftrightarrow>
      (\<exists>e t. (e,t)\<in>positive_meaning P \<and> z=Pair_Term (site_data_term (fst e) (snd e)) t)"
  using first program_interpretation_at_call(2)[OF second, of a z]
    program_interpretation_at_call(2)[OF second, of b z]
  by (auto simp: program_interpretation_def)

section \<open>Every closed old program and arbitrary new program have such a bridge\<close>

theorem native_historical_program_total:
  fixes E :: "local_address option artifact_environment"
    and Q :: "local_address option native_system"
  assumes old: "closed_native_package_at E pu pr P" and other: "schema_system_formed Q"
  shows "\<exists>F v T a b f g C.
    closed_native_package_at F v [] T \<and> native_package_environment F v []=F \<and>
    program_scope_quoted_at C [] E pu pr P \<and> program_interpretation P T a b \<and>
    a\<noteq>b \<and> inj_on f (system_definitions P) \<and> inj_on g (system_definitions Q) \<and>
    f ` system_definitions P \<inter> g ` system_definitions Q={} \<and>
    {a,b} \<inter> (f ` system_definitions P \<union> g ` system_definitions Q)={} \<and>
    system_definitions T=insert b (insert a (f ` system_definitions P \<union> g ` system_definitions Q)) \<and>
    (\<forall>d\<in>system_definitions P. \<forall>t.
      (schema_call_formed T (f d) t \<longleftrightarrow> schema_call_formed P d t) \<and>
      ((f d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning P)) \<and>
    (\<forall>d\<in>system_definitions Q. \<forall>t.
      (schema_call_formed T (g d) t \<longleftrightarrow> schema_call_formed Q d t) \<and>
      ((g d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning Q))"
proof -
  have package: "native_package_at E pu pr P" using old by (simp add: closed_native_package_at_def)
  have pf: "schema_system_formed P" by (rule native_package_system_formed[OF package])
  have ef: "environment_formed E"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have labels: "\<forall>d\<in>system_definitions P. term_formed (site_data_term (fst d) (snd d))"
  proof (intro ballI)
    fix d assume member: "d\<in>system_definitions P"
    have position: "d\<in>environment_positions E" by (rule native_package_entry_position[OF package member])
    show "term_formed (site_data_term (fst d) (snd d))"
      using environment_position_address[OF ef position] by simp
  qed
  obtain key :: "local_address option definition_site \<Rightarrow> local_address" where
    addressing: "finite_addressing (system_definitions P) key"
    using finite_addressing_exists[OF system_definitions_finite[OF pf]] by blast
  have keys: "inj_on key (system_definitions P)" using addressing by (simp add: finite_addressing_def)
  interpret hist: historical_views P Q "\<lambda>d. site_data_term (fst d) (snd d)" key
    "[] :: local_address" "[] :: local_address"
    by (rule historical_views.intro[OF pf other labels keys])
  let ?H="hist.extended"
  obtain h :: "((local_address option definition_site + local_address option definition_site)+bool)
      \<Rightarrow> local_address option definition_site"
    and F :: "local_address option artifact_environment" and v T where compiled:
    "inj_on h (system_definitions ?H)" "closed_native_package_at F v [] T"
    "native_package_environment F v []=F" "system_alpha_variant (rename_system h ?H) T"
    "positive_meaning T=map_prod h id ` positive_meaning ?H"
    using program_compilation_total[OF hist.formed] by blast
  let ?f="\<lambda>d. h (Inl (Inl d))"
  let ?g="\<lambda>d. h (Inl (Inr d))"
  let ?a="h (Inr False)"
  let ?b="h (Inr True)"
  have af: "Inr False\<in>system_definitions ?H" and bf: "Inr True\<in>system_definitions ?H"
    by (simp_all add: hist.definitions)
  have old_site: "Inl (Inl d)\<in>system_definitions ?H" if "d\<in>system_definitions P" for d
    using that by (auto simp: hist.definitions)
  have other_site: "Inl (Inr d)\<in>system_definitions ?H" if "d\<in>system_definitions Q" for d
    using that by (auto simp: hist.definitions)
  have unique: "x=y" if "x\<in>system_definitions ?H" "y\<in>system_definitions ?H" "h x=h y" for x y
    by (rule inj_onD[OF compiled(1) that(3,1,2)])
  have distinct: "?a\<noteq>?b" using unique[OF af bf] by auto
  have fi: "inj_on ?f (system_definitions P)"
    using unique old_site by (auto simp: inj_on_def)
  have gi: "inj_on ?g (system_definitions Q)"
    using unique other_site by (auto simp: inj_on_def)
  have different: "?f d\<noteq>?g e" if "d\<in>system_definitions P" "e\<in>system_definitions Q" for d e
    using unique[OF old_site[OF that(1)] other_site[OF that(2)]] by auto
  have separate: "?f ` system_definitions P \<inter> ?g ` system_definitions Q={}"
  proof (rule equals0I)
    fix z assume member: "z\<in>?f ` system_definitions P \<inter> ?g ` system_definitions Q"
    obtain d where left: "d\<in>system_definitions P" "z=?f d" using member by blast
    obtain e where right: "e\<in>system_definitions Q" "z=?g e" using member by blast
    show False using different[OF left(1) right(1)] left(2) right(2) by blast
  qed
  have old_fresh: "?a\<noteq>?f d \<and> ?b\<noteq>?f d" if "d\<in>system_definitions P" for d
    using unique[OF af old_site[OF that]] unique[OF bf old_site[OF that]] by auto
  have other_fresh: "?a\<noteq>?g d \<and> ?b\<noteq>?g d" if "d\<in>system_definitions Q" for d
    using unique[OF af other_site[OF that]] unique[OF bf other_site[OF that]] by auto
  have fresh: "{?a,?b} \<inter> (?f ` system_definitions P \<union> ?g ` system_definitions Q)={}"
  proof (rule equals0I)
    fix z assume member: "z\<in>{?a,?b} \<inter> (?f ` system_definitions P \<union> ?g ` system_definitions Q)"
    have root: "z=?a \<or> z=?b" using member by auto
    have range: "z\<in>?f ` system_definitions P \<or> z\<in>?g ` system_definitions Q"
      using member by auto
    then show False
    proof
      assume "z\<in>?f ` system_definitions P"
      then obtain d where parts: "d\<in>system_definitions P" "z=?f d" by blast
      show False using old_fresh[OF parts(1)] parts(2) root by auto
    next
      assume "z\<in>?g ` system_definitions Q"
      then obtain d where parts: "d\<in>system_definitions Q" "z=?g d" by blast
      show False using other_fresh[OF parts(1)] parts(2) root by auto
    qed
  qed
  have target_defs: "system_definitions T=h ` system_definitions ?H"
    using compiled(4) by (simp add: system_alpha_variant_def renamed_system_definitions)
  have all_defs: "system_definitions T=insert ?b (insert ?a
    (?f ` system_definitions P \<union> ?g ` system_definitions Q))"
    by (simp only: target_defs hist.definitions image_insert image_Un image_image)
  have tf: "schema_system_formed T" using compiled(4) by (simp add: system_alpha_variant_def)
  have ac: "schema_call_formed T ?a z \<longleftrightarrow> term_formed z" for z
    by (simp only: compiled_system_call_boundary[OF hist.formed compiled(1,4) af] hist.admission_call)
  have bc: "schema_call_formed T ?b z \<longleftrightarrow> term_formed z" for z
    by (simp only: compiled_system_call_boundary[OF hist.formed compiled(1,4) bf] hist.truth_call)
  have call_member: "d\<in>system_definitions P" if "schema_call_formed P d t" for d t
    using schema_call_formed_target[OF that] by blast
  have positive_member: "d\<in>system_definitions P" if "(d,t)\<in>positive_meaning P" for d t
  proof -
    have call: "schema_call_formed P d t" by (rule positive_meaning_formed[OF that])
    show ?thesis by (rule call_member[OF call])
  qed
  have am: "(?a,z)\<in>positive_meaning T \<longleftrightarrow>
    (\<exists>d t. schema_call_formed P d t \<and> z=Pair_Term (site_data_term (fst d) (snd d)) t)" for z
  proof -
    have copied: "(?a,z)\<in>positive_meaning T \<longleftrightarrow> (Inr False,z)\<in>positive_meaning ?H"
      by (rule compiled_system_meaning_at[OF compiled(1) af compiled(5)])
    have view: "(Inr False,z)\<in>positive_meaning ?H \<longleftrightarrow>
      (\<exists>d\<in>system_definitions P. \<exists>t. schema_call_formed P d t \<and>
        z=Pair_Term (site_data_term (fst d) (snd d)) t)"
      by (rule hist.admission_meaning)
    have domain: "(\<exists>d\<in>system_definitions P. \<exists>t. schema_call_formed P d t \<and>
        z=Pair_Term (site_data_term (fst d) (snd d)) t) \<longleftrightarrow>
      (\<exists>d t. schema_call_formed P d t \<and> z=Pair_Term (site_data_term (fst d) (snd d)) t)"
      using call_member by blast
    show ?thesis using copied view domain by blast
  qed
  have bm: "(?b,z)\<in>positive_meaning T \<longleftrightarrow>
    (\<exists>d t. (d,t)\<in>positive_meaning P \<and> z=Pair_Term (site_data_term (fst d) (snd d)) t)" for z
  proof -
    have copied: "(?b,z)\<in>positive_meaning T \<longleftrightarrow> (Inr True,z)\<in>positive_meaning ?H"
      by (rule compiled_system_meaning_at[OF compiled(1) bf compiled(5)])
    have view: "(Inr True,z)\<in>positive_meaning ?H \<longleftrightarrow>
      (\<exists>d\<in>system_definitions P. \<exists>t. (d,t)\<in>positive_meaning P \<and>
        z=Pair_Term (site_data_term (fst d) (snd d)) t)"
      by (rule hist.truth_meaning)
    have domain: "(\<exists>d\<in>system_definitions P. \<exists>t. (d,t)\<in>positive_meaning P \<and>
        z=Pair_Term (site_data_term (fst d) (snd d)) t) \<longleftrightarrow>
      (\<exists>d t. (d,t)\<in>positive_meaning P \<and> z=Pair_Term (site_data_term (fst d) (snd d)) t)"
      using positive_member by blast
    show ?thesis using copied view domain by blast
  qed
  have bridge: "program_interpretation P T ?a ?b"
    using pf tf all_defs ac bc am bm by (auto simp: program_interpretation_def)
  have original_calls: "\<forall>d\<in>system_definitions P. \<forall>t.
    (schema_call_formed T (?f d) t \<longleftrightarrow> schema_call_formed P d t) \<and>
    ((?f d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning P)"
  proof (intro ballI allI)
    fix d t assume member: "d\<in>system_definitions P"
    have inside: "Inl (Inl d)\<in>system_definitions ?H" by (rule old_site[OF member])
    have calls: "schema_call_formed T (?f d) t \<longleftrightarrow> schema_call_formed P d t"
      by (simp only: compiled_system_call_boundary[OF hist.formed compiled(1,4) inside] hist.source_calls[OF member])
    have truth: "(?f d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning P"
      by (simp only: compiled_system_meaning_at[OF compiled(1) inside compiled(5)] hist.source_meaning[OF member])
    show "(schema_call_formed T (?f d) t \<longleftrightarrow> schema_call_formed P d t) \<and>
      ((?f d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning P)"
      using calls truth by blast
  qed
  have other_calls: "\<forall>d\<in>system_definitions Q. \<forall>t.
    (schema_call_formed T (?g d) t \<longleftrightarrow> schema_call_formed Q d t) \<and>
    ((?g d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning Q)"
  proof (intro ballI allI)
    fix d t assume member: "d\<in>system_definitions Q"
    have inside: "Inl (Inr d)\<in>system_definitions ?H" by (rule other_site[OF member])
    have calls: "schema_call_formed T (?g d) t \<longleftrightarrow> schema_call_formed Q d t"
      by (simp only: compiled_system_call_boundary[OF hist.formed compiled(1,4) inside] hist.other_calls[OF member])
    have truth: "(?g d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning Q"
      by (simp only: compiled_system_meaning_at[OF compiled(1) inside compiled(5)] hist.other_meaning[OF member])
    show "(schema_call_formed T (?g d) t \<longleftrightarrow> schema_call_formed Q d t) \<and>
      ((?g d,t)\<in>positive_meaning T \<longleftrightarrow> (d,t)\<in>positive_meaning Q)"
      using calls truth by blast
  qed
  obtain C where quotation: "program_scope_quoted_at C [] (native_package_environment E pu pr) pu pr P"
    using program_scope_quoted_total[OF package] by blast
  have retained: "program_scope_quoted_at C [] E pu pr P"
    using quotation native_package_closed_environment_fixed[OF old] by simp
  show ?thesis
    by (rule exI[of _ F], rule exI[of _ v], rule exI[of _ T], rule exI[of _ ?a], rule exI[of _ ?b],
        rule exI[of _ ?f], rule exI[of _ ?g], rule exI[of _ C])
      (use compiled(2,3) retained bridge distinct fi gi separate fresh all_defs original_calls other_calls in blast)
qed

section \<open>Future native bridge invocations keep the compiled scope\<close>

theorem program_interpretation_native_application:
  fixes F :: "local_address option artifact_environment"
  assumes package: "closed_native_package_at F pu pr Q" and bridge: "program_interpretation P Q a b"
    and entry: "e\<in>{a,b}" and argument: "term_formed z"
  shows "\<exists>G au I K. environment_formed G \<and> environment_included F G \<and>
    native_package_at G pu pr Q \<and> native_package_environment G pu pr=F \<and>
    native_application_at G au [] e z I K \<and> native_application_formed G pu pr au [] \<and>
    (e=a \<longrightarrow> (native_positive_holds G pu pr au [] \<longleftrightarrow>
      (\<exists>d t. schema_call_formed P d t \<and> z=Pair_Term (site_data_term (fst d) (snd d)) t))) \<and>
    (e=b \<longrightarrow> (native_positive_holds G pu pr au [] \<longleftrightarrow>
      (\<exists>d t. (d,t)\<in>positive_meaning P \<and> z=Pair_Term (site_data_term (fst d) (snd d)) t)))"
proof -
  have native: "native_package_at F pu pr Q" using package by (simp add: closed_native_package_at_def)
  have member: "e\<in>system_definitions Q" using bridge entry by (auto simp: program_interpretation_def)
  obtain G au I K where app: "environment_formed G" "environment_included F G"
    "native_package_at G pu pr Q" "native_package_environment G pu pr=native_package_environment F pu pr"
    "native_application_at G au [] e z I K"
    "native_application_formed G pu pr au [] \<longleftrightarrow> schema_call_formed Q e z"
    "native_positive_holds G pu pr au [] \<longleftrightarrow> (e,z)\<in>positive_meaning Q"
    using native_application_extension_total[OF native member argument] by blast
  have canonical: "native_package_environment G pu pr=F"
    using app(4) native_package_closed_environment_fixed[OF package] by simp
  have formed: "native_application_formed G pu pr au []"
    using app(6) entry argument bridge by (auto simp: program_interpretation_def)
  show ?thesis by (rule exI[of _ G], rule exI[of _ au], rule exI[of _ I], rule exI[of _ K])
    (use app(1-3,5,7) canonical formed bridge in \<open>auto simp: program_interpretation_def\<close>)
qed

text \<open>
  This is an independently specified interpretation contract and a uniform
  construction proving it. Every actual closed earlier native program has
  a complete exact scope quotation and an ordinary compiled interpreter,
  together with any supplied formed other program. Source labels retain the
  original use and occurrence coordinates. The quotation retains the original
  environment and program site; relocation does not identify it with the
  newly compiled environment. Every term, including an exact literal target,
  stays unchanged as the second field of a historical query.

  The two entry roles may coincide in the contract when their meanings permit
  it. The construction supplies distinct ordinary definitions and keeps both
  source copies disjoint. Across another bridge, the entire previous query
  becomes ordinary argument data, giving the proved exact nested interpretation.

  The contract does not itself check a submitted program by native rules.
  The construction supplies one sufficient class of exact bridges; it imposes
  no global rule that every possible successor must be a syntactic copy.
  Later interpretation-support theories bind its entries into accepted
  transitions. Finite native admission of its correctness and the complete
  genesis mechanism remain separate work.
\<close>

end
