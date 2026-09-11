theory Factor_Constrained_Readings
  imports Factor_Presentation_Classes Factor_View_Definitions
begin

section \<open>One reader and one constraint share the actual returned body\<close>

definition constrained_reading_schema ::
  "nat \<Rightarrow> nat \<Rightarrow> (nat,nat,nat) factor_schema" where
  "constrained_reading_schema reader constraint =
    data_rule (Pattern_Pair data_x data_z)
      {(0,reader,Pattern_Pair data_x (Pattern_Pair data_y data_z)),(1,constraint,data_z)}"

lemma constrained_reading_schema_formed [simp]:
  "schema_formed (constrained_reading_schema reader constraint)"
  by (auto simp: constrained_reading_schema_def schema_formed_def single_valued_def)

lemma constrained_reading_schema_dependencies [simp]:
  "schema_dependencies (constrained_reading_schema reader constraint)={reader,constraint}"
proof -
  have rows: "rel_ran (schema_premises (constrained_reading_schema reader constraint)) =
    {(reader,Pattern_Pair data_x (Pattern_Pair data_y data_z)),(constraint,data_z)}"
    by (auto simp: constrained_reading_schema_def rel_ran_def)
  show ?thesis by (simp add: schema_dependencies_def rows)
qed

lemma constrained_reading_schema_ordinary [simp]:
  "schema_material_premises (constrained_reading_schema reader constraint)={}"
  by (simp add: constrained_reading_schema_def)

locale constrained_reading_profile =
  fixes P :: "(nat,nat,nat,nat) schema_system" and entry reader constraint :: nat
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
      (c,S)\<in>{(0,constrained_reading_schema reader constraint)}"
    and call: "\<And>t. schema_call_formed P entry t \<longleftrightarrow> term_formed t"
begin

lemma valuation:
  "(entry,z)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>a\<in>{0,1,2}. term_formed (h a)) \<and>
      z=Pair_Term (h 0) (h 2) \<and>
      (reader,Pair_Term (h 0) (Pair_Term (h 1) (h 2)))\<in>positive_meaning P \<and>
      (constraint,h 2)\<in>positive_meaning P)"
proof -
  have clauses: "((entry,c),S)\<in>system_clauses P \<longleftrightarrow>
    c=0 \<and> S=constrained_reading_schema reader constraint" for c S
    by (simp only: family) auto
  have accepts: "schema_call_formed P entry
      (evaluate_pattern h (schema_conclusion (constrained_reading_schema reader constraint)))"
    if "\<forall>a\<in>schema_variables (constrained_reading_schema reader constraint). term_formed (h a)" for h
    using that by (auto simp: call constrained_reading_schema_def schema_variables_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF clauses constrained_reading_schema_ordinary])
     apply (fact accepts)
    apply (rule ex_cong1)
    apply (simp add: constrained_reading_schema_def schema_variables_def conj_ac all_conj_distrib imp_conjL)
    done
qed

theorem step:
  assumes source: "(reader,Pair_Term p (Pair_Term q t))\<in>positive_meaning P"
    and body: "(constraint,t)\<in>positive_meaning P"
  shows "(entry,Pair_Term p t)\<in>positive_meaning P"
proof -
  have formed: "term_formed p" "term_formed q" "term_formed t"
    using schema_call_formed_target[OF positive_meaning_formed[OF source]] by auto
  let ?h="\<lambda>a::nat. if a=0 then p else if a=1 then q else t"
  show ?thesis by (simp only: valuation; rule exI[of _ ?h]) (use assms formed in auto)
qed

theorem exact:
  "(entry,z)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>p q t. z=Pair_Term p t \<and>
      (reader,Pair_Term p (Pair_Term q t))\<in>positive_meaning P \<and>
      (constraint,t)\<in>positive_meaning P)"
  using valuation step by blast

corollary at_pair:
  "(entry,Pair_Term p t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>q. (reader,Pair_Term p (Pair_Term q t))\<in>positive_meaning P \<and>
      (constraint,t)\<in>positive_meaning P)"
  by (auto simp: exact)

theorem relation_exact:
  assumes read: "\<And>p q t. (reader,Pair_Term p (Pair_Term q t))\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>a. presents a p \<and> reading a q t)"
    and check: "\<And>t. (constraint,t)\<in>positive_meaning P \<longleftrightarrow> accepts t"
  shows "(entry,Pair_Term p t)\<in>positive_meaning P \<longleftrightarrow>
    presented_relation presents (=) (\<lambda>a t. \<exists>q. reading a q t \<and> accepts t) p t"
  by (simp only: at_pair read check) (auto simp: presented_relation_def)

theorem at_subject:
  assumes presentation: "presentation_class presents D A" and source: "presents a p"
    and read: "\<And>p q t. (reader,Pair_Term p (Pair_Term q t))\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>a. presents a p \<and> reading a q t)"
    and check: "\<And>t. (constraint,t)\<in>positive_meaning P \<longleftrightarrow> accepts t"
  shows "(entry,Pair_Term p t)\<in>positive_meaning P \<longleftrightarrow>
    (\<exists>q. reading a q t \<and> accepts t)"
proof -
  interpret source: presentation_class presents D A by (rule presentation)
  show ?thesis using source source.recovery
    by (simp only: at_pair read check) blast
qed

corollary presentation_invariance:
  assumes presentation: "presentation_class presents D A"
    and first: "presents a p" and second: "presents a q"
    and read: "\<And>p q t. (reader,Pair_Term p (Pair_Term q t))\<in>positive_meaning P \<longleftrightarrow>
      (\<exists>a. presents a p \<and> reading a q t)"
  shows "(entry,Pair_Term p t)\<in>positive_meaning P \<longleftrightarrow>
    (entry,Pair_Term q t)\<in>positive_meaning P"
proof -
  interpret source: presentation_class presents D A by (rule presentation)
  show ?thesis using first second source.recovery
    by (simp only: at_pair read) blast
qed

end

section \<open>The composition is an ordinary finite native definition\<close>

theorem constrained_reading_view:
  assumes formed: "schema_system_formed P" and fresh: "entry\<notin>system_definitions P"
    and dependencies: "reader\<in>system_definitions P" "constraint\<in>system_definitions P"
  shows "positive_view P entry data_x {(0,constrained_reading_schema reader constraint)}"
  by (rule positive_view.intro[OF formed fresh])
    (use dependencies in \<open>auto simp: single_valued_def\<close>)

theorem constrained_reading_view_exists:
  assumes formed: "schema_system_formed P"
    and dependencies: "reader\<in>system_definitions P" "constraint\<in>system_definitions P"
  shows "\<exists>entry. positive_view P entry data_x {(0,constrained_reading_schema reader constraint)}"
  by (rule positive_view_exists[OF formed])
    (use dependencies in \<open>auto simp: single_valued_def\<close>)

theorem constrained_reading_view_profile:
  assumes view: "positive_view P entry data_x {(0,constrained_reading_schema reader constraint)}"
  shows "constrained_reading_profile
    (add_view_definition P entry data_x {(0,constrained_reading_schema reader constraint)})
    entry reader constraint"
proof -
  interpret view: positive_view P entry data_x "{(0,constrained_reading_schema reader constraint)}" by (rule view)
  show ?thesis by (unfold_locales)
    (use view.formed view.view_call view.no_old_clause in auto)
qed

theorem constrained_reading_native_total:
  assumes view: "positive_view P entry data_x {(0,constrained_reading_schema reader constraint)}"
  shows "\<exists>g :: nat\<Rightarrow>local_address option definition_site. \<exists>E u Q.
    inj_on g (insert entry (system_definitions P)) \<and> closed_native_package_at E u [] Q \<and>
    native_package_environment E u []=E \<and>
    system_alpha_variant (rename_system g
      (add_view_definition P entry data_x {(0,constrained_reading_schema reader constraint)})) Q \<and>
    positive_meaning Q= image (map_prod g id)
      (positive_meaning (add_view_definition P entry data_x {(0,constrained_reading_schema reader constraint)}))"
  using positive_view.native_total[OF view] .

text \<open>
  The reader receives the actual source, a private witness, and the returned
  body. The second premise checks that identical body. Both premise occurrences
  remain explicit even when their callees coincide. Formation of every private
  field follows from the actual reader call.

  The class and relation theorems require exact contracts for those existing
  callees. They do not turn their mathematical specifications into callbacks.
  A fresh instance is an ordinary view of a formed program; its dependencies,
  full clause family, and native compilation are supplied by the existing
  program theory. The constructor itself therefore has a complete native
  schema and program presentation under the same rules as its applications.

  A reader may expose representation structure. Invariance in the source class
  follows only from the stated source-reading contract. The returned term is
  the actual stored body, so a different presentation of its semantic subject
  cannot silently replace it in the constraint premise.
\<close>

end
