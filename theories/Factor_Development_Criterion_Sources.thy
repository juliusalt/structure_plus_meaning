theory Factor_Development_Criterion_Sources
  imports Factor_Development_Cases Factor_Finite_Ground_Source Factor_Finite_System_Unions
begin

definition finite_ground_condition where
  "finite_ground_condition xs=map_option (\<lambda>(d,F,u). development_existing_condition d F u) (finite_ground_source xs)"

lemma finite_ground_condition_program:
  "finite_ground_condition xs=(if list_all finite_term_formed xs
    then finite_program_condition (finite_ground_program xs) (Some [],[]) else None)"
  by (simp add: finite_ground_condition_def finite_ground_source_def finite_program_condition_def)

lemma finite_ground_condition_exact:
  assumes source: "finite_ground_condition xs=Some C"
  shows "development_condition_holds C x y \<longleftrightarrow> Finite_Pair x y\<in>set xs"
proof -
  obtain d F u where installed: "finite_ground_source xs=Some (d,F,u)"
    and condition: "C=development_existing_condition d F u"
    using source by (auto simp: finite_ground_condition_def split: option.splits prod.splits)
  obtain P where native: "native_package_at (decode_finite_environment F) u [] P"
    and exact: "\<forall>t. (d,t)\<in>positive_meaning P \<longleftrightarrow> t\<in>decode_finite_term ` set xs"
    by (rule finite_ground_source_meaning[OF installed]) blast
  show ?thesis using exact
    by (simp only: condition development_existing_condition_exact[OF native])
      (metis decode_finite_term_injective decode_finite_term.simps(3) image_iff)
qed

section \<open>A program of its own is installed beside the guard source\<close>

definition finite_standalone_condition ::
    "local_address option finite_native_system \<Rightarrow> local_address option definition_site \<Rightarrow>
      native_development_condition option" where
  "finite_standalone_condition R e=finite_program_condition
    (finite_system_union (finite_guard_source_program True) R) e"

lemma finite_guard_source_program_definitions:
  "system_definitions (decode_finite_system (finite_guard_source_program True))={(None,[Suc 0])}"
  by (simp add: finite_guard_source_program_def decode_finite_system_def system_definitions_def rel_dom_def
    map_relation_values_def)

theorem finite_standalone_condition_total:
  assumes formed: "schema_system_formed (decode_finite_system R)"
    and separate: "(None,[Suc 0])\<notin>system_definitions (decode_finite_system R)"
    and member: "e\<in>system_definitions (decode_finite_system R)"
  shows "\<exists>C. finite_standalone_condition R e=Some C"
proof -
  let ?G="decode_finite_system (finite_guard_source_program True)"
  have guard: "schema_system_formed ?G"
    by (rule native_package_system_formed[OF finite_guard_source_package])
  have disjoint: "system_definitions ?G \<inter> system_definitions (decode_finite_system R)={}"
    using separate by (simp add: finite_guard_source_program_definitions)
  have union: "decode_finite_system (finite_system_union (finite_guard_source_program True) R)=
      system_union ?G (decode_finite_system R)" by simp
  have ready_context: "finite_source_extension_context (finite_guard_source True) None [0]
      (finite_system_union (finite_guard_source_program True) R)=Some (finite_guard_source_program True)"
    unfolding finite_source_extension_context_correct union
    using finite_guard_source_package[where b=True] system_union_formed[OF guard formed disjoint]
      system_union_left_agreement[OF formed disjoint] by blast
  have entry: "e |\<in>| finite_system_definitions (finite_system_union (finite_guard_source_program True) R)"
    using member by (simp add: finite_system_definitions_correct union)
  show ?thesis
    using ready_context entry by (auto simp: finite_standalone_condition_def finite_program_condition_total)
qed

theorem finite_standalone_condition_exact:
  assumes formed: "schema_system_formed (decode_finite_system R)"
    and separate: "(None,[Suc 0])\<notin>system_definitions (decode_finite_system R)"
    and member: "e\<in>system_definitions (decode_finite_system R)"
    and condition: "finite_standalone_condition R e=Some C"
  shows "development_condition_holds C x y \<longleftrightarrow>
    (e,Pair_Term (decode_finite_term x) (decode_finite_term y))\<in>positive_meaning (decode_finite_system R)"
proof -
  let ?G="decode_finite_system (finite_guard_source_program True)"
  have guard: "schema_system_formed ?G"
    by (rule native_package_system_formed[OF finite_guard_source_package])
  have disjoint: "system_definitions (decode_finite_system R) \<inter> system_definitions ?G={}"
    using separate by (auto simp: finite_guard_source_program_definitions)
  have union: "decode_finite_system (finite_system_union (finite_guard_source_program True) R)=
      system_union (decode_finite_system R) ?G"
    by (simp only: finite_system_union_correct system_union_commute)
  show ?thesis
    using finite_program_condition_exact[OF condition[unfolded finite_standalone_condition_def]]
      system_union_left_locality(2)[OF formed guard disjoint member,
        where t="Pair_Term (decode_finite_term x) (decode_finite_term y)"]
    by (simp only: union)
qed

end
