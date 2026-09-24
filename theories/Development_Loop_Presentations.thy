theory Development_Loop_Presentations
  imports Development_Successor Development_Row_Data
begin

section \<open>The loop presents its problems as their rows in context\<close>

text \<open>
  The presenters of the loop's values, over the rows of @{text Development_Row_Data}: a repair, whose
  definition problems cite the repaired problem, and a loop's dependencies, generations, records and the
  loop itself, each taking its context's four parameters and exact on the values whose problems form a
  domain of that context. They stand above the constructions they present, which keep their imports.
\<close>

text \<open>
  A repair is a context. Its definition problems cite what posed them: the problem of the repaired
  request, at that problem's locus, which the extension keeps. Their grant is absent, every definition
  problem being generated. The request it issues again is presented in the context that carries the
  repair, as every request is.
\<close>

definition development_repair_citation ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> development_request \<Rightarrow> development_problem \<Rightarrow> bool list option" where
  "development_repair_citation key r p=Some (development_located_at key Development_Problem_Role (fst r))"

definition development_refinement_repair_data ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_request \<Rightarrow> development_refinement_repair \<Rightarrow> finite_factor_term option" where
  "development_refinement_repair_data key inert origin grant r=
    finite_partial_pair (Some \<circ> development_extension_verdict_data)
      (finite_partial_pair (development_problems_data key inert (development_repair_citation key r) (\<lambda>_. None))
        (finite_partial_pair (development_request_data key inert origin grant)
          (Some \<circ> finite_pair_presentation development_verdict_data finite_boolean_data)))"

corollary development_refinement_repair_data_presented [intro]:
  assumes definitions: "development_row_domain key (development_repair_citation key r) (\<lambda>_. None) P"
    and requests: "development_request_domain key origin grant R"
  shows "finite_presented_on (development_refinement_repair_data key inert origin grant r) (UNIV\<times>lists P\<times>R\<times>UNIV)"
  unfolding development_refinement_repair_data_def
  by (intro finite_partial_pair_presented finite_presented_total development_extension_verdict_data_injective
    development_problems_data_presented development_request_data_presented finite_pair_presentation_injective
    development_verdict_data_injective finite_boolean_data_injective definitions requests)

text \<open>
  The development's presenters present its problems in the context that holds them, with the context's
  four parameters: the loop's, read from its history, for a loop and its records. Each is exact on the
  values whose problems form a domain of that context.
\<close>

definition development_dependencies_data ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_dependencies \<Rightarrow> finite_factor_term option" where
  "development_dependencies_data key inert origin grant=finite_partial_collection
    (finite_partial_pair (development_problem_row_data key inert origin grant)
      (finite_partial_collection (finite_partial_pair (Some \<circ> isabelle_position_data)
        (development_problem_row_data key inert origin grant))))"

lemma development_dependencies_data_presented [intro]:
  assumes domain: "development_row_domain key origin grant P"
  shows "finite_presented_on (development_dependencies_data key inert origin grant)
    {D. fset D\<subseteq>P\<times>{X. fset X\<subseteq>UNIV\<times>P}}"
  unfolding development_dependencies_data_def
  by (intro finite_partial_collection_presented finite_partial_pair_presented development_problem_row_data_presented
    finite_presented_total isabelle_position_data_injective domain)

definition development_generation_data ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_generation \<Rightarrow> finite_factor_term option" where
  "development_generation_data key inert origin grant=finite_partial_pair (development_problem_row_data key inert origin grant)
    (Some \<circ> finite_pair_presentation isabelle_entities_data
      (finite_pair_presentation (finite_sequence_presentation isabelle_entity_data) development_verdict_data))"

lemma development_generation_data_presented [intro]:
  assumes domain: "development_row_domain key origin grant P"
  shows "finite_presented_on (development_generation_data key inert origin grant) (P\<times>UNIV)"
  unfolding development_generation_data_def
  by (intro finite_partial_pair_presented development_problem_row_data_presented finite_presented_total
    finite_pair_presentation_injective isabelle_collections_injective finite_sequence_presentation_injective
    isabelle_entity_data_injective development_verdict_data_injective domain)

text \<open>
  A record is presented through a presentation of the executed packet it may carry, supplied by
  the use: it is read as the one of its three parts it has, and presented by the existing option
  and pair presentations, so it is injective whenever the packet's presentation is.
\<close>

text \<open>
  A repair record carries the repaired request and the repair, whose definitions cite that request's
  problem: its presentation reads the repair in the context of the request it carries.
\<close>

definition development_repair_record_data ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_request\<times>development_refinement_repair \<Rightarrow> finite_factor_term option" where
  "development_repair_record_data key inert origin grant z=finite_partial_pair
    (development_request_data key inert origin grant) (development_refinement_repair_data key inert origin grant (fst z)) z"

lemma development_repair_record_data_presented [intro]:
  assumes requests: "development_request_domain key origin grant R"
    and repairs: "\<And>r. r\<in>R \<Longrightarrow> finite_presented_on (development_refinement_repair_data key inert origin grant r) (RR r)"
  shows "finite_presented_on (development_repair_record_data key inert origin grant) (SIGMA r:R. RR r)"
proof (rule finite_presented_onI)
  fix z assume z: "z\<in>(SIGMA r:R. RR r)"
  then obtain r R' where Z: "z=(r,R')" "r\<in>R" "R'\<in>RR r" by blast
  obtain x where x: "development_request_data key inert origin grant r=Some x"
    by (rule finite_presented_on_some[OF development_request_data_presented[OF requests, of inert] Z(2)])
  obtain y where y: "development_refinement_repair_data key inert origin grant r R'=Some y"
    by (rule finite_presented_on_some[OF repairs[OF Z(2)] Z(3)])
  show "development_repair_record_data key inert origin grant z\<noteq>None"
    by (simp add: development_repair_record_data_def finite_partial_pair_def Z(1) x y)
next
  fix z w t assume z: "z\<in>(SIGMA r:R. RR r)" and w: "w\<in>(SIGMA r:R. RR r)"
    and fz: "development_repair_record_data key inert origin grant z=Some t"
    and fw: "development_repair_record_data key inert origin grant w=Some t"
  obtain r R1 where Z: "z=(r,R1)" "r\<in>R" "R1\<in>RR r" using z by blast
  obtain r' R2 where W: "w=(r',R2)" "r'\<in>R" "R2\<in>RR r'" using w by blast
  obtain x y where x: "development_request_data key inert origin grant r=Some x"
      and y: "development_refinement_repair_data key inert origin grant r R1=Some y" and t: "t=Finite_Pair x y"
    using fz by (auto simp: development_repair_record_data_def finite_partial_pair_def Z(1) split: option.splits)
  obtain x' y' where x': "development_request_data key inert origin grant r'=Some x'"
      and y': "development_refinement_repair_data key inert origin grant r' R2=Some y'" and t': "t=Finite_Pair x' y'"
    using fw by (auto simp: development_repair_record_data_def finite_partial_pair_def W(1) split: option.splits)
  have rr: "r=r'"
    by (rule finite_presented_on_eq[OF development_request_data_presented[OF requests, of inert] Z(2) W(2)]) (use x x' t t' in simp)
  have "R1=R2"
    by (rule finite_presented_on_eq[OF repairs[OF Z(2)] Z(3)]) (use W(3) y y' t t' rr in simp_all)
  then show "z=w" using rr by (simp add: Z(1) W(1))
qed

definition development_record_parts_data ::
    "(development_packet \<Rightarrow> finite_factor_term) \<Rightarrow> (nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      (development_packet\<times>development_problem list) option\<times>
      (development_request\<times>(nat\<times>development_problem) fset fset) option\<times>development_generation option\<times>
      (development_request\<times>development_refinement_repair) option \<Rightarrow> finite_factor_term option" where
  "development_record_parts_data packet key inert origin grant=finite_partial_pair
    (finite_partial_option (finite_partial_pair (Some \<circ> packet) (development_problems_data key inert origin grant)))
    (finite_partial_pair (finite_partial_option (finite_partial_pair (development_request_data key inert origin grant)
        (finite_partial_collection (finite_partial_collection
          (finite_partial_pair (Some \<circ> isabelle_position_data) (development_problem_row_data key inert origin grant))))))
      (finite_partial_pair (finite_partial_option (development_generation_data key inert origin grant))
        (finite_partial_option (development_repair_record_data key inert origin grant))))"

definition development_record_data ::
    "(development_packet \<Rightarrow> finite_factor_term) \<Rightarrow> (nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_record \<Rightarrow> finite_factor_term option" where
  "development_record_data packet key inert origin grant=
    development_record_parts_data packet key inert origin grant \<circ> development_record_parts"

definition development_record_parts_domain ::
    "development_problem set \<Rightarrow> development_request set \<Rightarrow> (development_request \<Rightarrow> development_refinement_repair set) \<Rightarrow>
      ((development_packet\<times>development_problem list) option\<times>
      (development_request\<times>(nat\<times>development_problem) fset fset) option\<times>development_generation option\<times>
      (development_request\<times>development_refinement_repair) option) set" where
  "development_record_parts_domain P R RR={a. set_option a\<subseteq>UNIV\<times>lists P}\<times>
    {a. set_option a\<subseteq>R\<times>{X. fset X\<subseteq>{Y. fset Y\<subseteq>UNIV\<times>P}}}\<times>{a. set_option a\<subseteq>P\<times>UNIV}\<times>
    {a. set_option a\<subseteq>(SIGMA r:R. RR r)}"

definition development_record_domain ::
    "development_problem set \<Rightarrow> development_request set \<Rightarrow> (development_request \<Rightarrow> development_refinement_repair set) \<Rightarrow>
      development_record set" where
  "development_record_domain P R RR=development_record_parts -` development_record_parts_domain P R RR"

lemma development_record_parts_data_presented:
  assumes packet: "inj packet" and domain: "development_row_domain key origin grant P"
    and requests: "development_request_domain key origin grant R"
    and repairs: "\<And>r. r\<in>R \<Longrightarrow> finite_presented_on (development_refinement_repair_data key inert origin grant r) (RR r)"
  shows "finite_presented_on (development_record_parts_data packet key inert origin grant)
    (development_record_parts_domain P R RR)"
  unfolding development_record_parts_data_def development_record_parts_domain_def
  by (intro finite_partial_pair_presented finite_partial_option_presented finite_presented_total packet
    development_problems_data_presented domain development_request_data_presented requests
    finite_partial_collection_presented development_problem_row_data_presented isabelle_position_data_injective
    development_generation_data_presented development_repair_record_data_presented repairs)

theorem development_record_data_presented [intro]:
  assumes packet: "inj packet" and domain: "development_row_domain key origin grant P"
    and requests: "development_request_domain key origin grant R"
    and repairs: "\<And>r. r\<in>R \<Longrightarrow> finite_presented_on (development_refinement_repair_data key inert origin grant r) (RR r)"
  shows "finite_presented_on (development_record_data packet key inert origin grant) (development_record_domain P R RR)"
  unfolding development_record_data_def development_record_domain_def
  by (rule finite_presented_on_comp[OF development_record_parts_data_presented[OF packet domain requests repairs]])
    (auto intro: inj_on_subset[OF development_record_parts_injective])

definition development_loop_data ::
    "(development_packet \<Rightarrow> finite_factor_term) \<Rightarrow> (nat \<Rightarrow> bool list) \<Rightarrow> (isabelle_term \<Rightarrow> finite_factor_term) \<Rightarrow>
      (development_problem \<Rightarrow> bool list option) \<Rightarrow> (development_problem \<Rightarrow> bool list option) \<Rightarrow>
      development_loop \<Rightarrow> finite_factor_term option" where
  "development_loop_data packet key inert origin grant=finite_partial_pair (Some \<circ> isabelle_rooted_context_data)
    (finite_partial_pair (development_problems_data key inert origin grant)
      (finite_partial_pair (development_dependencies_data key inert origin grant)
        (finite_partial_pair (development_problems_table key inert origin grant)
          (finite_partial_sequence (development_record_data packet key inert origin grant)))))"

theorem development_loop_data_presented:
  assumes packet: "inj packet" and domain: "development_row_domain key origin grant P"
    and requests: "development_request_domain key origin grant R"
    and repairs: "\<And>r. r\<in>R \<Longrightarrow> finite_presented_on (development_refinement_repair_data key inert origin grant r) (RR r)"
  shows "finite_presented_on (development_loop_data packet key inert origin grant)
    (UNIV\<times>lists P\<times>{D. fset D\<subseteq>P\<times>{X. fset X\<subseteq>UNIV\<times>P}}\<times>{A. fset A\<subseteq>P}\<times>lists (development_record_domain P R RR))"
  unfolding development_loop_data_def
  by (intro finite_partial_pair_presented finite_presented_total isabelle_rooted_context_data_injective
    development_problems_data_presented development_dependencies_data_presented development_problems_table_presented
    finite_partial_sequence_presented development_record_data_presented packet domain requests repairs)

end
