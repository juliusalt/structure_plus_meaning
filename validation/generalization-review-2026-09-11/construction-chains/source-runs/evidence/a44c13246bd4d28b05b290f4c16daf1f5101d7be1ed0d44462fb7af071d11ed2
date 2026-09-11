theory Factor_Inference_Specialization_Clauses
  imports Factor_Inference_Specialization_Base
begin

section \<open>The actual node and actual program use the same environment\<close>

abbreviation inference_specialization_argument where
  "inference_specialization_argument e pu pr nu nr du dr c f v r q b report ds ni nk ri rk \<equiv>
    data_list_term [source_root_argument e pu pr,source_root_argument e nu nr,Pair_Term du dr,c,
      source_root_argument f v r,q,Pair_Term b report,ds,ni,nk,ri,rk]"

abbreviation inference_specialization_pattern where
  "inference_specialization_pattern e pu pr nu nr du dr c f v r q b report ds ni nk ri rk \<equiv>
    data_list_pattern [source_root_pattern e pu pr,source_root_pattern e nu nr,Pattern_Pair du dr,c,
      source_root_pattern f v r,q,Pattern_Pair b report,ds,ni,nk,ri,rk]"

definition inference_specialization_schema :: "(nat,nat,nat) factor_schema" where
  "inference_specialization_schema=data_rule
    (inference_specialization_pattern data_x data_y data_z data_w (Pattern_Variable 4)
      (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8)
      (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12)
      (Pattern_Variable 13) (Pattern_Variable 14) (Pattern_Variable 15) (Pattern_Variable 16)
      (Pattern_Variable 17) (Pattern_Variable 18))
    {(0,94,term_quotation_pattern data_x data_w (Pattern_Variable 4)
       (data_list_pattern [Pattern_Pair (Pattern_Variable 5) (Pattern_Variable 7),
         Pattern_Variable 19,Pattern_Variable 14]) (Pattern_Variable 15) (Pattern_Variable 16)),
     (1,349,specialization_binding_pattern (source_root_pattern data_x data_y data_z)
       (Pattern_Variable 5) (Pattern_Variable 6) (Pattern_Variable 7) (Pattern_Variable 8)
       (Pattern_Variable 9) (Pattern_Variable 10) (Pattern_Variable 11) (Pattern_Variable 12)
       (Pattern_Variable 13) (Pattern_Variable 19) (Pattern_Variable 17) (Pattern_Variable 18))}"

definition inference_specialization_system :: "(nat,nat,nat,nat) schema_system" where
  "inference_specialization_system=add_view_definition inference_specialization_base_system 350 data_x
    {(0,inference_specialization_schema)}"

interpretation inference_specialization_view:
  positive_view inference_specialization_base_system 350 data_x "{(0,inference_specialization_schema)}"
  by (rule positive_view.intro)
    (auto simp: inference_specialization_schema_def schema_formed_def schema_dependencies_def
      single_valued_def rel_dom_def rel_ran_def octets_formed_def)

lemma inference_specialization_formed [simp]: "schema_system_formed inference_specialization_system"
  using inference_specialization_view.formed by (simp only: inference_specialization_system_def)

lemma inference_specialization_definitions [simp]:
  "system_definitions inference_specialization_system=insert 350 (system_definitions inference_specialization_base_system)"
  by (simp add: inference_specialization_system_def)

lemma inference_specialization_call:
  "schema_call_formed inference_specialization_system d t \<longleftrightarrow>
    d\<in>system_definitions inference_specialization_system \<and> term_formed t"
  using added_variable_calls[OF inference_specialization_base_formed
    inference_specialization_formed[unfolded inference_specialization_system_def] inference_specialization_base_call]
  by (simp only: inference_specialization_system_def[symmetric])

lemma inference_specialization_old_meaning:
  assumes "d\<in>system_definitions inference_specialization_base_system"
  shows "(d,t)\<in>positive_meaning inference_specialization_system \<longleftrightarrow>
    (d,t)\<in>positive_meaning inference_specialization_base_system"
  using inference_specialization_view.old_meaning[OF assms] by (simp only: inference_specialization_system_def)

lemma inference_specialization_clause [simp]:
  "((350,c),S)\<in>system_clauses inference_specialization_system \<longleftrightarrow>
    c=0 \<and> S=inference_specialization_schema"
  using inference_specialization_view.no_old_clause by (auto simp: inference_specialization_system_def)

lemma inference_specialization_readers:
  "(94,t)\<in>positive_meaning inference_specialization_system \<longleftrightarrow>
    (94,t)\<in>positive_meaning proof_node_reading_system"
  "(349,t)\<in>positive_meaning inference_specialization_system \<longleftrightarrow>
    (349,t)\<in>positive_meaning specialization_binding_system"
  using inference_specialization_old_meaning[of 94 t] inference_specialization_base_node[of 94 t]
    inference_specialization_old_meaning[of 349 t] inference_specialization_base_binding[of 349 t] by auto

lemma inference_specialization_valuation:
  "(350,z)\<in>positive_meaning inference_specialization_system \<longleftrightarrow>
    (\<exists>h::nat\<Rightarrow>factor_term. (\<forall>j\<in>{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19}. term_formed (h j)) \<and>
      z=inference_specialization_argument (h 0) (h 1) (h 2) (h 3) (h 4) (h 5) (h 6) (h 7)
        (h 8) (h 9) (h 10) (h 11) (h 12) (h 13) (h 14) (h 15) (h 16) (h 17) (h 18) \<and>
      (94,term_quotation_argument (h 0) (h 3) (h 4)
        (data_list_term [Pair_Term (h 5) (h 7),h 19,h 14]) (h 15) (h 16))\<in>positive_meaning proof_node_reading_system \<and>
      (349,specialization_binding_argument (source_root_argument (h 0) (h 1) (h 2))
        (h 5) (h 6) (h 7) (h 8) (h 9) (h 10) (h 11) (h 12) (h 13) (h 19) (h 17) (h 18))
        \<in>positive_meaning specialization_binding_system)"
proof -
  have ordinary: "schema_material_premises inference_specialization_schema={}"
    by (simp add: inference_specialization_schema_def)
  have accepts: "schema_call_formed inference_specialization_system 350
      (evaluate_pattern h (schema_conclusion inference_specialization_schema))"
    if "\<forall>a\<in>schema_variables inference_specialization_schema. term_formed (h a)" for h
    using that by (auto simp: inference_specialization_call inference_specialization_schema_def
      schema_variables_def octets_formed_def)
  show ?thesis
    apply (subst ordinary_single_clause_valuation[OF inference_specialization_clause ordinary])
    apply (rule accepts)
    apply assumption
    apply (rule ex_cong1)
    apply (simp add: inference_specialization_schema_def schema_variables_def inference_specialization_readers
      conj_ac all_conj_distrib imp_conjL)
    done
qed

definition inference_specialization_calls where
  "inference_specialization_calls e pu pr nu nr du dr c f v r q b report ds ni nk ri rk \<longleftrightarrow>
    (\<exists>bs. (94,term_quotation_argument e nu nr (data_list_term [Pair_Term du c,bs,ds]) ni nk)
        \<in>positive_meaning proof_node_reading_system \<and>
      (349,specialization_binding_argument (source_root_argument e pu pr) du dr c f v r q b report bs ri rk)
        \<in>positive_meaning specialization_binding_system)"

theorem inference_specialization_at_arguments:
  "(350,inference_specialization_argument e pu pr nu nr du dr c f v r q b report ds ni nk ri rk)
      \<in>positive_meaning inference_specialization_system \<longleftrightarrow>
    inference_specialization_calls e pu pr nu nr du dr c f v r q b report ds ni nk ri rk"
proof
  assume "(350,inference_specialization_argument e pu pr nu nr du dr c f v r q b report ds ni nk ri rk)
    \<in>positive_meaning inference_specialization_system"
  then show "inference_specialization_calls e pu pr nu nr du dr c f v r q b report ds ni nk ri rk"
    by (simp only: inference_specialization_valuation data_list_term.simps factor_term.inject
      inference_specialization_calls_def) blast
next
  assume "inference_specialization_calls e pu pr nu nr du dr c f v r q b report ds ni nk ri rk"
  then obtain bs where reads:
    "(94,term_quotation_argument e nu nr (data_list_term [Pair_Term du c,bs,ds]) ni nk)
      \<in>positive_meaning proof_node_reading_system"
    "(349,specialization_binding_argument (source_root_argument e pu pr) du dr c f v r q b report bs ri rk)
      \<in>positive_meaning specialization_binding_system"
    by (auto simp: inference_specialization_calls_def)
  let ?h="\<lambda>j::nat. if j=0 then e else if j=1 then pu else if j=2 then pr else if j=3 then nu
    else if j=4 then nr else if j=5 then du else if j=6 then dr else if j=7 then c else if j=8 then f
    else if j=9 then v else if j=10 then r else if j=11 then q else if j=12 then b
    else if j=13 then report else if j=14 then ds else if j=15 then ni else if j=16 then nk
    else if j=17 then ri else if j=18 then rk else bs"
  have formed: "term_formed (term_quotation_argument e nu nr (data_list_term [Pair_Term du c,bs,ds]) ni nk)"
    "term_formed (specialization_binding_argument (source_root_argument e pu pr) du dr c f v r q b report bs ri rk)"
    using schema_call_formed_target[OF positive_meaning_formed[OF reads(1)]]
      schema_call_formed_target[OF positive_meaning_formed[OF reads(2)]] by auto
  show "(350,inference_specialization_argument e pu pr nu nr du dr c f v r q b report ds ni nk ri rk)
    \<in>positive_meaning inference_specialization_system"
    by (simp only: inference_specialization_valuation; rule exI[of _ ?h]) (use reads formed in auto)
qed

text \<open>
  The complete binding-row enumeration is private to the two premises.
  The physical node table can therefore use the record's order without
  imposing an additional order on the submitted node. The owning use and
  clause socket are shared with its actual citation. Discharges and both
  supports remain explicit. Child claims and whole-graph conditions are
  separate conditions to be checked by the surrounding argument reader.
\<close>

end
