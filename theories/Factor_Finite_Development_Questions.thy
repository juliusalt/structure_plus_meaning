theory Factor_Finite_Development_Questions
  imports Factor_Development_Criterion_Sources Finite_Binary_Values
begin

definition finite_development_rows where
  "finite_development_rows xs=map (Finite_Pair (Finite_Payload [])) xs"

definition finite_development_source where
  "finite_development_source xs=finite_ground_source (finite_development_rows xs)"

definition finite_development_question where
  "finite_development_question xs facets=(let source=finite_development_source xs;
    cs=map (\<lambda>ys. finite_ground_condition (finite_development_rows ys)) facets in
    if xs=[] \<or> facets=[] \<or> \<not>list_all (\<lambda>C. C\<noteq>None) cs then None else
      case source of None \<Rightarrow> None | Some (d,F,u) \<Rightarrow>
        Some \<lparr>development_source=F,development_source_use=u,development_source_root=[],
          development_generator_entry=d,development_problem=Finite_Payload [],
          development_conditions=map the cs,development_scope_criticism=development_scope_condition True,
          development_selected_facets=[]\<rparr>)"

lemma finite_development_question_source:
  assumes "finite_development_question xs facets=Some Q"
  obtains d F u where "finite_development_source xs=Some (d,F,u)"
    "development_source Q=F" "development_source_use Q=u" "development_source_root Q=[]"
    "development_generator_entry Q=d" "development_problem Q=Finite_Payload []"
  using assms by (auto simp: finite_development_question_def Let_def split: if_splits option.splits prod.splits)

lemma finite_development_original_criterion:
  assumes constructed: "finite_development_question xs facets=Some Q" and facet: "ys\<in>set facets"
  obtains C where "C\<in>set (development_conditions Q)" "development_problem Q=Finite_Payload []"
    "finite_ground_condition (finite_development_rows ys)=Some C"
proof -
  let ?cs="map (\<lambda>ys. finite_ground_condition (finite_development_rows ys)) facets"
  have complete: "list_all (\<lambda>C. C\<noteq>None) ?cs"
    and conditions: "development_conditions Q=map the ?cs"
    and problem: "development_problem Q=Finite_Payload []"
    using constructed by (auto simp: finite_development_question_def Let_def
      split: if_splits option.splits prod.splits)
  have present: "finite_ground_condition (finite_development_rows ys)\<noteq>None"
    using complete facet by (auto simp: list_all_iff)
  obtain C where actual: "finite_ground_condition (finite_development_rows ys)=Some C"
    using present by auto
  have member: "Some C\<in>set ?cs" using facet by (metis imageI set_map actual)
  have "C\<in>set (development_conditions Q)"
    using imageI[OF member, of the] by (simp only: conditions set_map option.sel)
  then show thesis by (rule that[OF _ problem actual])
qed

theorem finite_development_original_conditions:
  assumes constructed: "finite_development_question xs facets=Some Q"
    and admitted: "native_development_admission Q report=Some accepted"
    and selected: "x\<in>set accepted" and facet: "ys\<in>set facets"
  shows "x\<in>set ys"
proof -
  obtain C where member: "C\<in>set (development_conditions Q)" and problem: "development_problem Q=Finite_Payload []"
    and condition: "finite_ground_condition (finite_development_rows ys)=Some C"
    by (rule finite_development_original_criterion[OF constructed facet]) blast
  have holds: "development_condition_holds C (development_problem Q) x"
    by (rule native_development_original_conditions[OF admitted selected member])
  show ?thesis using holds
    by (simp only: problem finite_ground_condition_exact[OF condition])
      (auto simp: finite_development_rows_def)
qed

definition finite_development_generated where
  "finite_development_generated xs=(case finite_development_source xs of None \<Rightarrow> None
    | Some (d,F,u) \<Rightarrow> map_option (\<lambda>(P,D,A,rows). finite_generated_outputs d (Finite_Payload []) rows)
      (finite_native_generation F u [] (Finite_Payload [])))"

definition finite_development_scope_complete where
  "finite_development_scope_complete xs=(case finite_development_generated xs of None \<Rightarrow> False
    | Some actual \<Rightarrow> list_all (\<lambda>x. x\<in>set actual) xs)"

lemma finite_development_question_generated:
  assumes constructed: "finite_development_question xs facets=Some Q"
  shows "map_option (development_generated_values Q)
      (finite_native_generation (development_source Q) (development_source_use Q)
        (development_source_root Q) (development_problem Q))=finite_development_generated xs"
proof -
  obtain d F u where source: "finite_development_source xs=Some (d,F,u)"
    and fields: "development_source Q=F" "development_source_use Q=u" "development_source_root Q=[]"
      "development_generator_entry Q=d" "development_problem Q=Finite_Payload []"
    by (rule finite_development_question_source[OF constructed]) blast
  show ?thesis by (cases "finite_native_generation F u [] (Finite_Payload [])")
    (auto simp: fields finite_development_generated_def source development_generated_values_def
      split: prod.splits)
qed

theorem finite_development_complete_scope:
  assumes question: "finite_development_question xs facets=Some Q"
    and complete: "finite_development_scope_complete xs"
    and generation: "finite_native_generation (development_source Q) (development_source_use Q)
      (development_source_root Q) (development_problem Q)=Some G"
  shows "set xs\<subseteq>set (development_generated_values Q G)"
proof -
  have actual: "finite_development_generated xs=Some (development_generated_values Q G)"
    using finite_development_question_generated[OF question] by (simp add: generation)
  show ?thesis using complete
    by (simp add: finite_development_scope_complete_def actual list_all_iff subset_iff)
qed

definition finite_development_index where
  "finite_development_index n=finite_binary_natural_value n"

lemma finite_development_index_decode [simp]:
  "decode_finite_term (finite_development_index n)=Payload_Term (map (\<lambda>b. if b then 1 else 0) (natural_binary_digits n))"
  by (simp add: finite_development_index_def finite_binary_natural_value_def finite_storage_path_value_def)

lemma finite_development_index_formed [simp]: "finite_term_formed (finite_development_index n)"
  by (simp add: finite_development_index_def)

lemma finite_development_index_eq [simp]:
  "finite_development_index m=finite_development_index n \<longleftrightarrow> m=n"
  by (simp add: finite_development_index_def inj_eq[OF finite_binary_natural_value_injective])

text \<open>
  This reusable constructor reflects finite value families into ordinary native
  source clauses and instantiates the existing complete development cycle.
  Membership alone asserts no condition about another subject. Each caller must
  establish how every facet family was computed from its complete original
  subjects. The scope observation compares the actual native generation with
  every supplied candidate value; it is not a proposed coverage flag.
  A candidate's index is the binary presentation of its natural: one payload of its digits,
  without the byte bound of a single octet, whose size grows with the number of digits rather
  than with the index, so a question over n candidates has a source of O(n log n) addresses.
\<close>

end
