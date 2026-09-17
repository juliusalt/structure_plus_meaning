theory Finite_Presented_Programs
  imports Finite_Presented_Coordinates Factor_Executable_Systems
begin

section \<open>Patterns retain their constructors and the presentation of their variables\<close>

fun finite_pattern_presentation ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> 'a finite_term_pattern \<Rightarrow> finite_factor_term" where
  "finite_pattern_presentation f (Finite_Variable a)=Finite_Pair (Finite_Payload [0]) (f a)"
| "finite_pattern_presentation f (Finite_Pattern_Payload v)=Finite_Pair (Finite_Payload [1]) (Finite_Payload v)"
| "finite_pattern_presentation f (Finite_Pattern_Pair p q)=Finite_Pair (Finite_Payload [2])
    (Finite_Pair (finite_pattern_presentation f p) (finite_pattern_presentation f q))"
| "finite_pattern_presentation f (Finite_Pattern_Target t)=Finite_Pair (Finite_Payload [3]) (Finite_Target t)"

lemma finite_pattern_presentation_injective [intro]:
  assumes f: "inj f"
  shows "inj (finite_pattern_presentation f)"
proof (rule injI)
  fix p q show "finite_pattern_presentation f p=finite_pattern_presentation f q \<Longrightarrow> p=q"
    by (induction p arbitrary: q) (case_tac q; auto simp: inj_eq[OF f])+
qed

theorem finite_pattern_presentation_class:
  assumes "inj f"
  shows "presentation_class (finite_presents (finite_pattern_presentation f)) (\<lambda>_. True)
    (\<lambda>t. \<exists>p. t=decode_finite_term (finite_pattern_presentation f p))"
  by (rule finite_presents_class[where D="\<lambda>_. True", simplified];
      rule finite_pattern_presentation_injective[OF assms])

section \<open>Material fields, schema premises and whole programs compose their notions\<close>

definition finite_material_presentation ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> 'a finite_material_pattern \<Rightarrow> finite_factor_term" where
  "finite_material_presentation f M=Finite_Pair (finite_pattern_presentation f (finite_material_source M))
    (Finite_Pair (finite_pattern_presentation f (finite_material_atoms M))
    (Finite_Pair (finite_pattern_presentation f (finite_material_edges M))
    (Finite_Pair (finite_pattern_presentation f (finite_material_counts M))
      (finite_pattern_presentation f (finite_material_functions M)))))"

lemma finite_material_presentation_injective [intro]:
  assumes f: "inj f"
  shows "inj (finite_material_presentation f)"
proof (rule injI)
  fix M N assume same: "finite_material_presentation f M=finite_material_presentation f N"
  show "M=N"
    by (rule finite_material_pattern.equality;
      use same in \<open>simp add: finite_material_presentation_def
        inj_eq[OF finite_pattern_presentation_injective[OF f]]\<close>)
qed

definition finite_schema_presentation ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> ('s \<Rightarrow> finite_factor_term) \<Rightarrow>
    ('d \<Rightarrow> finite_factor_term) \<Rightarrow> ('a,'s,'d) finite_factor_schema \<Rightarrow> finite_factor_term" where
  "finite_schema_presentation fa fs fd S=Finite_Pair
    (finite_pattern_presentation fa (finite_schema_conclusion S))
    (Finite_Pair
      (finite_collection_presentation (finite_pair_presentation fs
        (finite_pair_presentation fd (finite_pattern_presentation fa))) (finite_schema_premises S))
      (finite_collection_presentation (finite_pair_presentation fs (finite_material_presentation fa))
        (finite_schema_materials S)))"

lemma finite_schema_presentation_injective [intro]:
  assumes a: "inj fa" and s: "inj fs" and d: "inj fd"
  shows "inj (finite_schema_presentation fa fs fd)"
proof (rule injI)
  fix S T assume same: "finite_schema_presentation fa fs fd S=finite_schema_presentation fa fs fd T"
  have patterns: "inj (finite_pattern_presentation fa)" by (rule finite_pattern_presentation_injective[OF a])
  have slots: "inj (finite_collection_presentation (finite_pair_presentation fs
      (finite_pair_presentation fd (finite_pattern_presentation fa))))"
    by (intro finite_collection_presentation_injective finite_pair_presentation_injective patterns s d)
  have materials: "inj (finite_collection_presentation
      (finite_pair_presentation fs (finite_material_presentation fa)))"
    by (intro finite_collection_presentation_injective finite_pair_presentation_injective
      finite_material_presentation_injective s a)
  show "S=T"
    by (rule finite_factor_schema.equality;
      use same in \<open>simp add: finite_schema_presentation_def inj_eq[OF patterns]
        inj_eq[OF slots] inj_eq[OF materials]\<close>)
qed

definition finite_system_presentation ::
  "('a \<Rightarrow> finite_factor_term) \<Rightarrow> ('s \<Rightarrow> finite_factor_term) \<Rightarrow>
    ('d \<Rightarrow> finite_factor_term) \<Rightarrow> ('c \<Rightarrow> finite_factor_term) \<Rightarrow>
    ('a,'s,'d,'c) finite_schema_system \<Rightarrow> finite_factor_term" where
  "finite_system_presentation fa fs fd fc P=Finite_Pair
    (finite_collection_presentation (finite_pair_presentation fd (finite_pattern_presentation fa))
      (finite_system_interfaces P))
    (finite_collection_presentation (finite_pair_presentation (finite_pair_presentation fd fc)
      (finite_schema_presentation fa fs fd)) (finite_system_clauses P))"

lemma finite_system_presentation_injective [intro]:
  assumes a: "inj fa" and s: "inj fs" and d: "inj fd" and c: "inj fc"
  shows "inj (finite_system_presentation fa fs fd fc)"
proof (rule injI)
  fix P Q assume same: "finite_system_presentation fa fs fd fc P=finite_system_presentation fa fs fd fc Q"
  have interfaces: "inj (finite_collection_presentation (finite_pair_presentation fd (finite_pattern_presentation fa)))"
    by (intro finite_collection_presentation_injective finite_pair_presentation_injective
      finite_pattern_presentation_injective d a)
  have clauses: "inj (finite_collection_presentation (finite_pair_presentation (finite_pair_presentation fd fc)
      (finite_schema_presentation fa fs fd)))"
    by (intro finite_collection_presentation_injective finite_pair_presentation_injective
      finite_schema_presentation_injective a s d c)
  show "P=Q"
    by (rule finite_schema_system.equality;
      use same in \<open>simp add: finite_system_presentation_def inj_eq[OF interfaces] inj_eq[OF clauses]\<close>)
qed

theorem finite_system_presentation_class:
  assumes "inj fa" "inj fs" "inj fd" "inj fc"
  shows "presentation_class (finite_presents (finite_system_presentation fa fs fd fc)) (\<lambda>_. True)
    (\<lambda>t. \<exists>P. t=decode_finite_term (finite_system_presentation fa fs fd fc P))"
  by (rule finite_presents_class[where D="\<lambda>_. True", simplified];
      rule finite_system_presentation_injective[OF assms])

text \<open>
  Every program keeps its interface collection and its complete keyed clause
  collection. Each clause keeps its conclusion, socket-indexed ordinary premises,
  and socket-indexed material premises; each material keeps all five pattern
  fields. Variable, socket, definition and clause-key presentations are explicit
  separate arguments, even when their HOL carriers coincide. These presentations
  identify complete values, including unformed programs. They supply no program
  formation, soundness or admission verdict.
\<close>

end
