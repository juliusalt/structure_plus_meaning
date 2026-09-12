theory Factor_Transported_Readings
  imports Factor_Constrained_Readings Factor_Quoted_Artifacts
begin

section \<open>The actual returned body is compared with the expected report\<close>

definition transported_reading_schema ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "transported_reading_schema reader comparison =
    data_rule (Pattern_Pair data_x data_w)
      {(0,reader,Pattern_Pair data_x (Pattern_Pair data_y data_z)),
       (1,comparison,Pattern_Pair data_z data_w)}"

lemma transported_reading_schema_formed [simp]:
  "schema_formed (transported_reading_schema reader comparison)"
  by (auto simp: transported_reading_schema_def schema_formed_def single_valued_def)

lemma transported_reading_schema_dependencies [simp]:
  "schema_dependencies (transported_reading_schema reader comparison)={reader,comparison}"
proof -
  have rows: "rel_ran (schema_premises (transported_reading_schema reader comparison))=
      {(reader,Pattern_Pair data_x (Pattern_Pair data_y data_z)),(comparison,Pattern_Pair data_z data_w)}"
    by (auto simp: transported_reading_schema_def rel_ran_def)
  show ?thesis by (simp add: schema_dependencies_def rows)
qed

lemma transported_reading_schema_ordinary [simp]:
  "schema_material_premises (transported_reading_schema reader comparison)={}"
  by (simp add: transported_reading_schema_def)

locale transported_reading_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry reader comparison :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>{(0,transported_reading_schema reader comparison)}"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,z)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>a\<in>{0,1,2,3}. term_formed (h a)) \<and>
      z=Pair_Term (h 0) (h 3) \<and>
      (reader,Pair_Term (h 0) (Pair_Term (h 1) (h 2)))\<in>positive_meaning P \<and>
      (comparison,Pair_Term (h 2) (h 3))\<in>positive_meaning P)"
proof -
  have clauses: "((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      c=0 \<and> S=transported_reading_schema reader comparison" for c S
    by (simp only: family) auto
  have accepts: "schema_call_formed P entry
      (evaluate_pattern h (schema_conclusion (transported_reading_schema reader comparison)))"
    if "\<forall>a\<in>schema_variables (transported_reading_schema reader comparison). term_formed (h a)" for h
    using that by (auto simp: call transported_reading_schema_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF clauses transported_reading_schema_ordinary])
     apply (fact accepts)
    apply (rule ex_cong1)
    apply (simp add: transported_reading_schema_def schema_variables_def conj_ac all_conj_distrib imp_conjL)
    done
qed

theorem step:
  assumes source: "(reader,Pair_Term p (Pair_Term q t))\<in>positive_meaning P"
    and compared: "(comparison,Pair_Term t v)\<in>positive_meaning P"
  shows "(entry,Pair_Term p v)\<in>positive_meaning P"
proof -
  have formed: "term_formed p" "term_formed q" "term_formed t" "term_formed v"
    using schema_call_formed_target[OF positive_meaning_formed[OF source]]
      schema_call_formed_target[OF positive_meaning_formed[OF compared]] by auto
  let ?h="\<lambda>a::nat. if a=0 then p else if a=1 then q else if a=2 then t else v"
  show ?thesis by (simp only: valuation; rule exI[of _ ?h]) (use assms formed in auto)
qed

theorem exact:
  "(entry,z)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>p q t v. z=Pair_Term p v \<and>
      (reader,Pair_Term p (Pair_Term q t))\<in>positive_meaning P \<and>
      (comparison,Pair_Term t v)\<in>positive_meaning P)"
  using valuation step by blast

corollary at_pair:
  "(entry,Pair_Term p v)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>q t. (reader,Pair_Term p (Pair_Term q t))\<in>positive_meaning P \<and>
      (comparison,Pair_Term t v)\<in>positive_meaning P)"
  by (auto simp: exact)

theorem composition_transport:
  assumes read: "\<And>p t. (\<exists>q. (reader,Pair_Term p (Pair_Term q t))\<in>positive_meaning P) \<longleftrightarrow> material t p"
    and compare: "\<And>t v. (comparison,Pair_Term t v)\<in>positive_meaning P \<longleftrightarrow>
      presentation_transport R S t v"
  shows "(entry,Pair_Term p v)\<in>positive_meaning P \<longleftrightarrow>
    presentation_transport (composed_presentation R material) S p v"
proof -
  have actual: "(\<exists>q t. (reader,Pair_Term p (Pair_Term q t))\<in>positive_meaning P \<and>
      (comparison,Pair_Term t v)\<in>positive_meaning P) \<longleftrightarrow>
      (\<exists>t. material t p \<and> presentation_transport R S t v)"
    by (simp only: compare) (use read in blast)
  show ?thesis by (simp only: at_pair actual)
    (auto simp: presentation_transport_def composed_presentation_def)
qed

theorem identity_function_contract:
  assumes source: "presentation_class (composed_presentation R material) D A"
    and target: "presentation_class S D B"
    and read: "\<And>p t. (\<exists>q. (reader,Pair_Term p (Pair_Term q t))\<in>positive_meaning P) \<longleftrightarrow> material t p"
    and compare: "\<And>t v. (comparison,Pair_Term t v)\<in>positive_meaning P \<longleftrightarrow>
      presentation_transport R S t v"
  shows "presented_function_contract (composed_presentation R material) D A S D B id
    (\<lambda>p v. (entry,Pair_Term p v)\<in>positive_meaning P)"
proof -
  have operation: "(\<lambda>p v. (entry,Pair_Term p v)\<in>positive_meaning P)=
      presentation_transport (composed_presentation R material) S"
    by (intro ext; rule composition_transport[OF read compare])
  show ?thesis by (simp only: operation; rule presentation_identity_function[OF source target])
qed

end

section \<open>A fresh instance preserves both actual callees\<close>

theorem transported_reading_view:
  assumes formed: "schema_system_formed P" and fresh: "entry\<notin>system_definitions P"
    and dependencies: "reader\<in>system_definitions P" "comparison\<in>system_definitions P"
  shows "positive_view P entry data_x {(0,transported_reading_schema reader comparison)}"
  by (rule positive_view.intro[OF formed fresh])
    (use dependencies in \<open>auto simp: single_valued_def\<close>)

theorem transported_reading_view_profile:
  assumes view: "positive_view P entry data_x {(0,transported_reading_schema reader comparison)}"
  shows "transported_reading_profile
    (add_view_definition P entry data_x {(0,transported_reading_schema reader comparison)})
    entry reader comparison"
proof -
  interpret view: positive_view P entry data_x "{(0,transported_reading_schema reader comparison)}" by (rule view)
  show ?thesis by (unfold_locales)
    (use view.formed view.view_call view.no_old_clause in auto)
qed

text \<open>
  A reader returns its actual body with an explicit private witness. A second
  ordinary premise compares that same body with the supplied report. Both
  occurrences and callees are part of the complete schema. Their actual calls
  supply formation of every private and public term.

  When the locally owned comparison realizes canonical correspondence, the
  resulting reader realizes the same correspondence from the composed source
  class to the report class. Its generic function contract then supplies every
  compatible output and uniform invariance. The underlying body is retained
  through composition; an expected presentation does not replace stored data.
  Both quotation instances below consume this contract without a new semantic
  primitive, an arbitrary truth callback, or a selected representative.
\<close>

end
