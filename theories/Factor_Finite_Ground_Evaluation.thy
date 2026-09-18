theory Factor_Finite_Ground_Evaluation
  imports Factor_Finite_Ground_Source Factor_Finite_Native_Evaluation
begin

section \<open>Every clause an installed ground source places at its entry is ground\<close>

text \<open>
  The installation contract states the package at the returned root only up to an alpha
  variant of the placed program. That is enough: every clause at the entry is a variant of
  a placed exact recognizer, and renaming neither adds a premise nor a variable to a
  recognizer of an exact term.
\<close>

lemma finite_ground_source_entry_clauses:
  assumes installed: "finite_ground_source xs=Some (d,F,u)"
  obtains T where "native_package_at (decode_finite_environment F) u [] T"
    "\<forall>c S. (c,S)\<in>system_clause_family T d \<longrightarrow> schema_premises S={} \<and> schema_variables S={}"
proof -
  let ?E="finite_guard_source True"
  let ?Q="finite_ground_program xs"
  let ?e="(Some [],[]) :: local_address option definition_site"
  have formed: "list_all finite_term_formed xs"
    using installed by (cases "list_all finite_term_formed xs") (simp_all add: finite_ground_source_def)
  have entry: "finite_install_source_entry ?E None [0] ?Q ?e=Some (d,F,u)"
    using installed formed by (simp add: finite_ground_source_def)
  obtain P where run: "finite_extend_source_native ?E None [0] ?Q=Some (P,F,u)"
    and member: "?e |\<in>| finite_system_definitions ?Q"
    and site: "d=finite_program_coordinates ?E (finite_system_definitions P) (finite_system_definitions ?Q) id ?e"
    using finite_install_source_entry_conditions[THEN iffD1, OF entry] by blast
  interpret run: finite_source_native_run ?E F None u "[0]" P ?Q
    by (rule finite_source_native_run.intro[OF run])
  let ?h="finite_program_coordinates ?E (finite_system_definitions P) (finite_system_definitions ?Q) id"
  obtain T where package: "native_package_at (decode_finite_environment F) u [] T"
    and variant: "system_alpha_variant (rename_system ?h (decode_finite_system ?Q)) T"
    and injective: "inj_on ?h (fset (finite_system_definitions ?Q))"
    using run.correct by (elim conjE exE) (rule that; assumption)
  interpret view: positive_view "decode_finite_system (finite_guard_source_program True)" ?e
      "Pattern_Variable []" "ground_clause_family xs"
    by (rule ground_program_view[OF formed])
  have system: "schema_system_formed (decode_finite_system ?Q)"
    unfolding finite_ground_program_correct by (rule view.formed)
  have family: "system_clause_family (decode_finite_system ?Q) ?e=ground_clause_family xs"
    unfolding finite_ground_program_correct by (rule view.view_clause_family)
  have defined: "?e\<in>system_definitions (decode_finite_system ?Q)"
    using member by (simp only: finite_system_definitions_correct)
  have inj: "inj_on ?h (system_definitions (decode_finite_system ?Q))"
    using injective by (simp only: finite_system_definitions_correct)
  have placed: "d\<in>system_definitions (rename_system ?h (decode_finite_system ?Q))"
    unfolding site renamed_system_definitions by (rule imageI[OF defined])
  obtain g where variants: "schema_family_variant g
      (system_clause_family (rename_system ?h (decode_finite_system ?Q)) d) (system_clause_family T d)"
    using variant placed unfolding system_alpha_variant_def by blast
  have ground: "schema_premises S={} \<and> schema_variables S={}"
    if clause: "(c,S)\<in>system_clause_family T d" for c S
  proof -
    obtain s R where origin: "(s,R)\<in>system_clause_family (rename_system ?h (decode_finite_system ?Q)) d"
      and alpha: "schema_alpha_variant R S"
      using schema_family_variant_origin[OF variants clause] by blast
    obtain R0 where source: "(s,R0)\<in>system_clause_family (decode_finite_system ?Q) ?e"
      and renamed: "R=rename_schema id id ?h R0"
      using renamed_system_clause_at[OF system inj defined, THEN iffD1, OF origin[unfolded site]] by blast
    obtain x where recognizer: "R0=recognizer_schema (exact_term_pattern x)"
      using source by (auto simp: family ground_clause_family_def)
    obtain f k where shape: "S=rename_schema f k id R"
      using alpha by (auto simp: schema_alpha_variant_def)
    show ?thesis
      by (simp add: shape renamed recognizer rename_schema_def recognizer_schema_def
        map_socket_graph_def schema_variables_def rename_pattern_variables)
  qed
  show thesis by (rule that[OF package]) (use ground in blast)
qed

section \<open>Native evaluation of a ground source answers every entry demand\<close>

text \<open>
  A demand made only at the entry meets clauses without premises and without variables, so
  its heads are covered and it is closed. The installed package is read back because the
  installation contract supplies one, and the checked evaluator then answers. No demand is
  decided here; the existing exact evaluation contract states what the answer is.
\<close>

theorem finite_ground_source_evaluation_total:
  assumes installed: "finite_ground_source xs=Some (d,F,u)"
    and entry: "\<And>q. q |\<in>| D \<Longrightarrow> fst q=d"
  obtains P A where "finite_native_program_evaluation F u [] D=Some (P,A)"
proof -
  obtain T where package: "native_package_at (decode_finite_environment F) u [] T"
    and clauses: "\<forall>c S. (c,S)\<in>system_clause_family T d \<longrightarrow> schema_premises S={} \<and> schema_variables S={}"
    by (rule finite_ground_source_entry_clauses[OF installed])
  obtain P where read: "finite_native_source F u []=Some P"
  proof (cases "finite_native_source F u []")
    case None
    then have "\<not>(\<exists>N. native_package_at (decode_finite_environment F) u [] N)"
      by (simp add: finite_native_source_absent)
    then show ?thesis using package by blast
  next
    case (Some P)
    then show ?thesis by (rule that)
  qed
  have native: "native_package_at (decode_finite_environment F) u [] (decode_finite_system P)"
    using read by (simp only: finite_native_source_correct)
  have same: "decode_finite_system P=T" by (rule native_package_unique[OF native package])
  have entry_clause: "schema_premises S={} \<and> schema_variables S={}"
    if member: "((d,c),S)\<in>system_clauses (decode_finite_system P)" for c S
  proof -
    have "(c,S)\<in>system_clause_family T d"
      unfolding system_clause_family_def same[symmetric]
      by (rule image_eqI[of _ _ "((d,c),S)"]) (use member in simp_all)
    then show ?thesis using clauses by blast
  qed
  have finite_entry: "finite_schema_variables S={||}"
    if member: "((d,c),S) |\<in>| finite_system_clauses P" for c S
  proof -
    have "((d,c),decode_finite_schema S)\<in>system_clauses (decode_finite_system P)"
      unfolding decode_finite_system_fields map_relation_values_def
      by (rule image_eqI[of _ _ "((d,c),S)"]) (use member in simp_all)
    then have "fset (finite_schema_variables S)={}"
      using entry_clause by (simp only: finite_schema_variables_correct)
    then show ?thesis by (simp only: fset_inject[symmetric] bot_fset.rep_eq)
  qed
  have head: "finite_schema_head_missing S={||}"
    if member: "((e,c),S) |\<in>| finite_system_clauses P" and demanded: "e |\<in>| fimage fst D" for e c S
  proof -
    have "e=d" using demanded entry by auto
    then have "finite_schema_variables S={||}" using finite_entry member by blast
    then show ?thesis by (simp add: finite_schema_head_missing_def)
  qed
  have covered: "finite_program_head_covered P D"
    unfolding finite_program_head_covered_def
  proof (rule fBallI)
    fix x assume member: "x |\<in>| finite_system_clauses P"
    obtain e c S where shape: "x=((e,c),S)" by (metis surj_pair)
    have "e |\<in>| fimage fst D \<longrightarrow> finite_schema_head_missing S={||}"
      using head member by (simp only: shape) blast
    then show "(\<lambda>((e,c),S). e |\<in>| fimage fst D \<longrightarrow> finite_schema_head_missing S={||}) x"
      by (simp only: shape prod.case)
  qed
  have closed: "finite_program_demand_closed P D"
  proof -
    have "program_demand_closed (decode_finite_system P) (decode_finite_call_term ` fset D)"
      unfolding program_demand_closed_def
    proof (intro allI impI)
      fix q H
      assume demanded: "q\<in>decode_finite_call_term ` fset D"
        and inferred: "schema_inference_rules (decode_finite_system P) q H"
      obtain r where r: "r |\<in>| D" and call: "q=decode_finite_call_term r" using demanded by blast
      have at: "fst q=d" using entry[OF r] by (simp add: call decode_finite_call_term_def)
      obtain c V where admitted: "admitted_schema_instance (decode_finite_system P) (fst q) c V (snd q) H"
        using inferred by (auto simp: schema_inference_rules_def)
      obtain S where member: "((fst q,c),S)\<in>system_clauses (decode_finite_system P)"
        and instantiated: "schema_instance S V (snd q) H"
        using admitted by (auto simp: admitted_schema_instance_def)
      have none: "schema_premises S={}" using entry_clause[of c S] member at by simp
      have premised: "schema_premise_instance S V H" using instantiated by (simp add: schema_instance_def)
      have empty: "H={}"
      proof (rule equals0I)
        fix y assume y: "y\<in>H"
        obtain s e t where shape: "y=(s,e,t)" by (metis prod.collapse)
        obtain p where "(s,e,p)\<in>schema_premises S"
          using schema_premise_instance_origin[OF premised y[unfolded shape]] by blast
        then show False by (simp add: none)
      qed
      show "rel_ran H\<subseteq>decode_finite_call_term ` fset D" by (simp add: empty rel_ran_def)
    qed
    then show ?thesis by (simp only: finite_program_demand_closed_correct[OF covered])
  qed
  have formed: "finite_system_formed P"
    by (simp only: finite_system_formed_correct; rule native_package_system_formed[OF native])
  obtain A where evaluated: "finite_program_evaluation P D=Some A"
    using finite_program_evaluation_conditions[of P D] formed covered closed by blast
  have "finite_native_program_evaluation F u [] D=Some (P,A)"
    by (simp only: finite_native_program_evaluation_conditions) (rule conjI[OF native evaluated])
  then show thesis by (rule that)
qed

text \<open>
  The theorem concerns the operation, not its cost: it states that the checked evaluator
  answers every demand at the entry of any installed ground source, so a notion that
  decides membership through such a source never meets an unanswered case. What the answer
  contains remains the exact evaluation contract and the ground source's meaning.
\<close>

end
