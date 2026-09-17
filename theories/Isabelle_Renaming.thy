theory Isabelle_Renaming
  imports Isabelle_Entities Inference_Embeddings
begin

section \<open>The coordinates of a name table carry no meaning\<close>

text \<open>
  A renaming moves every name of a context to another position. The names themselves are
  unchanged: the moved table holds the same name at the moved position, and holds nothing
  where the original held nothing. Under such a correspondence every computed observation
  of a context is the image of the original observation, so no decision of the state
  depends on a position or on the order of the table.

  The reading of an equation consults the table for the three fixed base names. Changing
  a name in the table is not a renaming; the seeded controls show that it changes what the
  state reads. That dependence on the fixed Isabelle/HOL base is exposed here, not hidden.
\<close>

definition isabelle_table_correspondence ::
    "(nat \<Rightarrow> nat) \<Rightarrow> String.literal list \<Rightarrow> String.literal list \<Rightarrow> bool" where
  "isabelle_table_correspondence f names names' \<longleftrightarrow>
    inj f \<and> (\<forall>i. isabelle_name_at names' (f i)=isabelle_name_at names i)"

lemma isabelle_table_correspondence_injective: "isabelle_table_correspondence f names names' \<Longrightarrow> inj f"
  by (simp add: isabelle_table_correspondence_def)

lemma isabelle_table_correspondence_name:
  "isabelle_table_correspondence f names names' \<Longrightarrow> isabelle_name_at names' (f i)=isabelle_name_at names i"
  by (simp add: isabelle_table_correspondence_def)

section \<open>Types, terms and entities move with their positions\<close>

fun isabelle_type_rename :: "(nat \<Rightarrow> nat) \<Rightarrow> isabelle_type \<Rightarrow> isabelle_type" where
  "isabelle_type_rename f (Isabelle_Type_Application c Ts)=
    Isabelle_Type_Application (f c) (map (isabelle_type_rename f) Ts)"
| "isabelle_type_rename f (Isabelle_Type_Free a S)=Isabelle_Type_Free (f a) (map f S)"
| "isabelle_type_rename f (Isabelle_Type_Variable a i S)=Isabelle_Type_Variable (f a) i (map f S)"

fun isabelle_term_rename :: "(nat \<Rightarrow> nat) \<Rightarrow> isabelle_term \<Rightarrow> isabelle_term" where
  "isabelle_term_rename f (Isabelle_Constant c T)=Isabelle_Constant (f c) (isabelle_type_rename f T)"
| "isabelle_term_rename f (Isabelle_Free x T)=Isabelle_Free (f x) (isabelle_type_rename f T)"
| "isabelle_term_rename f (Isabelle_Variable x i T)=Isabelle_Variable (f x) i (isabelle_type_rename f T)"
| "isabelle_term_rename f (Isabelle_Bound i)=Isabelle_Bound i"
| "isabelle_term_rename f (Isabelle_Abstraction T t)=
    Isabelle_Abstraction (isabelle_type_rename f T) (isabelle_term_rename f t)"
| "isabelle_term_rename f (Isabelle_Application t u)=
    Isabelle_Application (isabelle_term_rename f t) (isabelle_term_rename f u)"

fun isabelle_entity_rename :: "(nat \<Rightarrow> nat) \<Rightarrow> isabelle_entity \<Rightarrow> isabelle_entity" where
  "isabelle_entity_rename f (Isabelle_Base_Constant t)=Isabelle_Base_Constant (isabelle_term_rename f t)"
| "isabelle_entity_rename f (Isabelle_Development_Constant t)=
    Isabelle_Development_Constant (isabelle_term_rename f t)"
| "isabelle_entity_rename f (Isabelle_Frontier_Constant t)=
    Isabelle_Frontier_Constant (isabelle_term_rename f t)"
| "isabelle_entity_rename f (Isabelle_Definition p)=Isabelle_Definition (isabelle_term_rename f p)"
| "isabelle_entity_rename f (Isabelle_Specification p)=Isabelle_Specification (isabelle_term_rename f p)"
| "isabelle_entity_rename f (Isabelle_Code_Equation p)=Isabelle_Code_Equation (isabelle_term_rename f p)"

lemma isabelle_type_rename_injective [intro]: "inj f \<Longrightarrow> inj (isabelle_type_rename f)"
proof (rule injI)
  fix T U assume injective: "inj f"
  show "isabelle_type_rename f T=isabelle_type_rename f U \<Longrightarrow> T=U"
  proof (induction T arbitrary: U)
    case (Isabelle_Type_Application c Ts)
    from Isabelle_Type_Application.prems obtain Us where U: "U=Isabelle_Type_Application c Us"
      and same: "map (isabelle_type_rename f) Ts=map (isabelle_type_rename f) Us"
      by (cases U) (simp_all add: inj_eq[OF injective])
    have "Ts=Us" by (rule map_members_injective[OF Isabelle_Type_Application.IH same])
    then show ?case by (simp add: U)
  next
    case (Isabelle_Type_Free a S)
    then show ?case
      by (cases U) (simp_all add: inj_eq[OF injective] inj_map_eq_map[OF injective])
  next
    case (Isabelle_Type_Variable a i S)
    then show ?case
      by (cases U) (simp_all add: inj_eq[OF injective] inj_map_eq_map[OF injective])
  qed
qed

lemma isabelle_term_rename_injective [intro]: "inj f \<Longrightarrow> inj (isabelle_term_rename f)"
proof (rule injI)
  fix t u assume injective: "inj f"
  note names = inj_eq[OF injective] and types = inj_eq[OF isabelle_type_rename_injective[OF injective]]
  show "isabelle_term_rename f t=isabelle_term_rename f u \<Longrightarrow> t=u"
  proof (induction t arbitrary: u)
    case (Isabelle_Constant c T)
    then show ?case by (cases u) (simp_all add: names types)
  next
    case (Isabelle_Free x T)
    then show ?case by (cases u) (simp_all add: names types)
  next
    case (Isabelle_Variable x i T)
    then show ?case by (cases u) (simp_all add: names types)
  next
    case (Isabelle_Bound i)
    then show ?case by (cases u) simp_all
  next
    case (Isabelle_Abstraction T s)
    from Isabelle_Abstraction.prems obtain U v where u: "u=Isabelle_Abstraction U v"
      and type: "isabelle_type_rename f T=isabelle_type_rename f U"
      and body: "isabelle_term_rename f s=isabelle_term_rename f v"
      by (cases u) simp_all
    have same: "T=U" using type by (simp only: types)
    show ?case by (simp only: u same Isabelle_Abstraction.IH[OF body])
  next
    case (Isabelle_Application s s')
    from Isabelle_Application.prems obtain v v' where u: "u=Isabelle_Application v v'"
      and left: "isabelle_term_rename f s=isabelle_term_rename f v"
      and right: "isabelle_term_rename f s'=isabelle_term_rename f v'"
      by (cases u) simp_all
    show ?case
      by (simp only: u Isabelle_Application.IH(1)[OF left] Isabelle_Application.IH(2)[OF right])
  qed
qed

text \<open>
  The hypotheses of this induction are instantiated at the components the case analysis
  supplies. Handing them to the simplifier instead makes each one a conditional rewrite of
  an arbitrary equation between components, and against this context that search does not
  return.
\<close>

lemma isabelle_entity_rename_injective [intro]: "inj f \<Longrightarrow> inj (isabelle_entity_rename f)"
proof (rule injI)
  fix e g assume injective: "inj f"
  show "isabelle_entity_rename f e=isabelle_entity_rename f g \<Longrightarrow> e=g"
    by (cases e; cases g) (simp_all add: inj_eq[OF isabelle_term_rename_injective[OF injective]])
qed

section \<open>Every structural reading of a context is the image of the original reading\<close>

text \<open>
  A reading that selects by an option and a reading that collects a finite set both
  travel with the map of their values; these two shapes are shared by every reading
  below, so each is established once.
\<close>

lemma map_filter_rename:
  assumes step: "\<And>x. g (h x)=map_option f (g x)"
  shows "List.map_filter g (map h xs)=map f (List.map_filter g xs)"
  by (induction xs) (auto simp: List.map_filter_simps step split: option.splits)

lemma concat_map_map_pointwise:
  assumes step: "\<And>x. F (h x)=map g (G x)"
  shows "concat (map F (map h xs))=map g (concat (map G xs))"
  by (induction xs) (simp_all add: step)

lemma filter_map_pointwise:
  assumes step: "\<And>x. P (h x)=Q x"
  shows "filter P (map h xs)=map h (filter Q xs)"
  by (induction xs) (simp_all add: step)

lemma fset_of_list_image:
  assumes "set xs=f ` set ys"
  shows "fset_of_list xs=fimage f (fset_of_list ys)"
  by (metis assms fimage.rep_eq fset_inject fset_of_list.rep_eq)

lemma isabelle_type_rename_positions:
  "isabelle_type_positions (isabelle_type_rename f T)=map f (isabelle_type_positions T)"
proof (induction T)
  case (Isabelle_Type_Application c Ts)
  then show ?case by (simp add: map_concat o_def cong: map_cong)
qed simp_all

lemma isabelle_term_rename_positions:
  "isabelle_term_positions (isabelle_term_rename f t)=map f (isabelle_term_positions t)"
  by (induction t) (simp_all add: isabelle_type_rename_positions)

lemma isabelle_entity_rename_positions:
  "isabelle_entity_positions (isabelle_entity_rename f e)=map f (isabelle_entity_positions e)"
  by (cases e) (simp_all add: isabelle_entity_positions_def isabelle_term_rename_positions)

lemma isabelle_term_rename_constants:
  "isabelle_term_constants (isabelle_term_rename f t)=map f (isabelle_term_constants t)"
  by (induction t) simp_all

lemma isabelle_term_rename_head:
  "isabelle_head_constant (isabelle_term_rename f t)=map_option f (isabelle_head_constant t)"
  by (induction t) simp_all

lemma isabelle_entity_rename_declared:
  "isabelle_declared_constant (isabelle_entity_rename f e)=map_option f (isabelle_declared_constant e)"
  by (cases e) (simp_all split: isabelle_term.splits)

lemma isabelle_entity_rename_specified:
  "isabelle_specified_proposition (isabelle_entity_rename f e)=
    map_option (isabelle_term_rename f) (isabelle_specified_proposition e)"
  by (cases e) simp_all

lemma isabelle_rename_development_constants:
  "isabelle_development_constants (map (isabelle_entity_rename f) es)=map f (isabelle_development_constants es)"
  unfolding isabelle_development_constants_def
  by (rule map_filter_rename) (case_tac x; simp_all split: isabelle_term.splits)

lemma isabelle_rename_frontier_constants:
  "isabelle_frontier_constants (map (isabelle_entity_rename f) es)=map f (isabelle_frontier_constants es)"
  unfolding isabelle_frontier_constants_def
  by (rule map_filter_rename) (case_tac x; simp_all split: isabelle_term.splits)

lemma isabelle_rename_declared_list:
  "List.map_filter isabelle_declared_constant (map (isabelle_entity_rename f) es)=
    map f (List.map_filter isabelle_declared_constant es)"
  by (rule map_filter_rename) (rule isabelle_entity_rename_declared)

lemma isabelle_rename_head_list:
  "List.map_filter isabelle_head_constant (map (isabelle_term_rename f) roots)=
    map f (List.map_filter isabelle_head_constant roots)"
  by (rule map_filter_rename) (rule isabelle_term_rename_head)

lemma isabelle_rename_equation_left:
  "isabelle_table_correspondence f names names' \<Longrightarrow>
    isabelle_equation_left names' (isabelle_term_rename f p)=
      map_option (isabelle_term_rename f) (isabelle_equation_left names p)"
proof (induction names p rule: isabelle_equation_left.induct)
  case (1 nm c T p)
  then show ?case by (simp add: isabelle_table_correspondence_name)
next
  case (2 nm c T l r)
  then show ?case by (simp add: isabelle_table_correspondence_name)
qed simp_all

lemma isabelle_rename_equation_head:
  assumes corr: "isabelle_table_correspondence f names names'"
  shows "Option.bind (isabelle_equation_left names' (isabelle_term_rename f p)) isabelle_head_constant=
    map_option f (Option.bind (isabelle_equation_left names p) isabelle_head_constant)"
proof (cases "isabelle_equation_left names p")
  case None
  then show ?thesis by (simp add: isabelle_rename_equation_left[OF corr])
next
  case (Some l)
  then show ?thesis by (simp add: isabelle_rename_equation_left[OF corr] isabelle_term_rename_head)
qed

lemma isabelle_rename_entity_subjects:
  assumes corr: "isabelle_table_correspondence f names names'"
  shows "isabelle_entity_subjects names' (map f D) (isabelle_entity_rename f e)=
    map f (isabelle_entity_subjects names D e)"
proof -
  have injective: "inj f" by (rule isabelle_table_correspondence_injective[OF corr])
  show ?thesis
    by (cases e)
      (simp_all add: isabelle_rename_equation_head[OF corr] isabelle_term_rename_constants filter_map comp_def
        inj_image_mem_iff[OF injective] split: option.splits)
qed

section \<open>Reached constants are the image of the original least closure\<close>

definition isabelle_context_rename ::
    "(nat \<Rightarrow> nat) \<Rightarrow> String.literal list \<Rightarrow> isabelle_context \<Rightarrow> isabelle_context" where
  "isabelle_context_rename f names' C=(names',map (isabelle_entity_rename f) (snd C))"

lemma isabelle_context_rename_fields [simp]:
  "fst (isabelle_context_rename f names' C)=names'"
  "snd (isabelle_context_rename f names' C)=map (isabelle_entity_rename f) (snd C)"
  by (simp_all add: isabelle_context_rename_def)

lemma isabelle_reach_rules_formed: "finite_inference_formed (isabelle_reach_rules C)"
  by (auto simp: finite_inference_formed_def finite_premise_functional_def isabelle_reach_rules_def
    fset_of_list_elem)

lemma isabelle_rename_reach_rules:
  assumes corr: "isabelle_table_correspondence f (fst C) names'"
  shows "isabelle_reach_rules (isabelle_context_rename f names' C)=
    finite_embedded_inferences f (isabelle_reach_rules C)"
proof -
  let ?read="\<lambda>names D e. case isabelle_specified_proposition e of None \<Rightarrow> []
    | Some p \<Rightarrow> concat (map (\<lambda>s. map (\<lambda>c. (c,{|(0,s)|})) (isabelle_term_constants p))
        (isabelle_entity_subjects names D e))"
  let ?moved="\<lambda>(a,H). (f a,fimage (\<lambda>(i,b). (i,f b)) H)"
  have rules: "isabelle_reach_rules E=
      fset_of_list (concat (map (?read (fst E) (isabelle_development_constants (snd E))) (snd E)))" for E
    by (simp add: isabelle_reach_rules_def)
  have entity: "?read names' (map f (isabelle_development_constants (snd C))) (isabelle_entity_rename f e)=
      map ?moved (?read (fst C) (isabelle_development_constants (snd C)) e)" for e
    by (simp add: isabelle_entity_rename_specified isabelle_rename_entity_subjects[OF corr]
      isabelle_term_rename_constants map_concat comp_def split: option.splits)
  have mapped: "concat (map (?read names' (map f (isabelle_development_constants (snd C))))
      (map (isabelle_entity_rename f) (snd C)))=
    map ?moved (concat (map (?read (fst C) (isabelle_development_constants (snd C))) (snd C)))"
    by (rule concat_map_map_pointwise) (rule entity)
  show ?thesis
    by (simp only: rules isabelle_context_rename_fields isabelle_rename_development_constants
      mapped finite_embedded_inferences_def fset_of_list_map)
qed

lemma isabelle_rename_reached_constants:
  assumes corr: "isabelle_table_correspondence f (fst C) names'"
  shows "isabelle_reached_constants (map (isabelle_term_rename f) roots) (isabelle_context_rename f names' C)=
    f ` isabelle_reached_constants roots C"
  unfolding isabelle_reached_constants_def
  by (simp only: isabelle_rename_head_list fset_of_list_map isabelle_rename_reach_rules[OF corr]
    finite_inference_result_renaming[OF isabelle_table_correspondence_injective[OF corr]
      isabelle_reach_rules_formed])

section \<open>The whole assessment of a renamed context is the image of the original\<close>

fun isabelle_assessment_rename ::
    "(nat \<Rightarrow> nat) \<Rightarrow> isabelle_context_assessment \<Rightarrow> isabelle_context_assessment" where
  "isabelle_assessment_rename f (U,D,M,R,Fr)=(fimage f U,fimage f D,
    fimage (isabelle_entity_rename f) M,fimage (isabelle_entity_rename f) R,fimage f Fr)"

lemma isabelle_rename_unknown_positions:
  assumes corr: "isabelle_table_correspondence f (fst C) names'"
  shows "fset_of_list (isabelle_unknown_positions (isabelle_context_rename f names' C))=
    fimage f (fset_of_list (isabelle_unknown_positions C))"
proof (rule fset_of_list_image)
  have occurrences: "concat (map isabelle_entity_positions (map (isabelle_entity_rename f) (snd C)))=
      map f (concat (map isabelle_entity_positions (snd C)))"
    by (simp add: map_concat comp_def isabelle_entity_rename_positions)
  show "set (isabelle_unknown_positions (isabelle_context_rename f names' C))=
      f ` set (isabelle_unknown_positions C)"
    by (simp only: isabelle_unknown_positions_def isabelle_context_rename_fields occurrences
      filter_map comp_def isabelle_table_correspondence_name[OF corr] set_remdups set_map)
qed

lemma isabelle_rename_mentioned_constants:
  "isabelle_mentioned_constants (map (isabelle_term_rename f) roots) (isabelle_context_rename f names' C)=
    map f (isabelle_mentioned_constants roots C)"
proof -
  have step: "(case isabelle_specified_proposition (isabelle_entity_rename f e) of None \<Rightarrow> []
        | Some p \<Rightarrow> isabelle_term_constants p)=
      map f (case isabelle_specified_proposition e of None \<Rightarrow> [] | Some p \<Rightarrow> isabelle_term_constants p)" for e
    by (simp add: isabelle_entity_rename_specified isabelle_term_rename_constants split: option.splits)
  have propositions: "concat (map (\<lambda>e. case isabelle_specified_proposition e of None \<Rightarrow> []
        | Some p \<Rightarrow> isabelle_term_constants p) (map (isabelle_entity_rename f) es))=
      map f (concat (map (\<lambda>e. case isabelle_specified_proposition e of None \<Rightarrow> []
        | Some p \<Rightarrow> isabelle_term_constants p) es))" for es
    by (induction es) (simp_all add: step)
  show ?thesis
    by (simp only: isabelle_mentioned_constants_def isabelle_context_rename_fields
      isabelle_rename_head_list propositions map_append)
qed

lemma isabelle_rename_undeclared_constants:
  assumes injective: "inj f"
  shows "fset_of_list (isabelle_undeclared_constants (map (isabelle_term_rename f) roots)
      (isabelle_context_rename f names' C))=
    fimage f (fset_of_list (isabelle_undeclared_constants roots C))"
  by (rule fset_of_list_image)
    (simp add: isabelle_undeclared_constants_def Let_def
      isabelle_rename_mentioned_constants isabelle_rename_declared_list filter_map comp_def
      inj_image_mem_iff[OF injective])

lemma isabelle_rename_malformed_entities:
  assumes corr: "isabelle_table_correspondence f (fst C) names'"
  shows "isabelle_malformed_entities (isabelle_context_rename f names' C)=
    map (isabelle_entity_rename f) (isabelle_malformed_entities C)"
proof -
  have subjects: "isabelle_entity_subjects names' [] (isabelle_entity_rename f e)=
      map f (isabelle_entity_subjects (fst C) [] e)" for e
    using isabelle_rename_entity_subjects[OF corr, of "[]" e] by simp
  have malformed: "(case isabelle_entity_rename f e of Isabelle_Specification p \<Rightarrow> False
        | _ \<Rightarrow> isabelle_declared_constant (isabelle_entity_rename f e)=None \<and>
            isabelle_entity_subjects names' [] (isabelle_entity_rename f e)=[])=
      (case e of Isabelle_Specification p \<Rightarrow> False
        | _ \<Rightarrow> isabelle_declared_constant e=None \<and> isabelle_entity_subjects (fst C) [] e=[])" for e
    by (cases e) (simp_all add: subjects isabelle_rename_equation_head[OF corr]
      split: isabelle_term.splits option.splits)
  have filtered: "filter (\<lambda>e. case e of Isabelle_Specification p \<Rightarrow> False
        | _ \<Rightarrow> isabelle_declared_constant e=None \<and> isabelle_entity_subjects names' [] e=[])
      (map (isabelle_entity_rename f) (snd C))=
    map (isabelle_entity_rename f) (filter (\<lambda>e. case e of Isabelle_Specification p \<Rightarrow> False
        | _ \<Rightarrow> isabelle_declared_constant e=None \<and> isabelle_entity_subjects (fst C) [] e=[]) (snd C))"
    by (rule filter_map_pointwise) (rule malformed)
  show ?thesis
    by (simp only: isabelle_malformed_entities_def isabelle_context_rename_fields filtered)
qed

lemma isabelle_rename_unreached_entities:
  assumes corr: "isabelle_table_correspondence f (fst C) names'"
  shows "fset_of_list (isabelle_unreached_entities (map (isabelle_term_rename f) roots)
      (isabelle_context_rename f names' C))=
    fimage (isabelle_entity_rename f) (fset_of_list (isabelle_unreached_entities roots C))"
proof (rule fset_of_list_image)
  have injective: "inj f" by (rule isabelle_table_correspondence_injective[OF corr])
  have reached: "isabelle_entity_reached (f ` isabelle_reached_constants roots C)
      (isabelle_context_rename f names' C) (isabelle_entity_rename f e)=
    isabelle_entity_reached (isabelle_reached_constants roots C) C e" for e
    by (simp add: isabelle_entity_reached_def isabelle_entity_rename_declared
      isabelle_rename_development_constants isabelle_rename_entity_subjects[OF corr] list_ex_iff
      inj_image_mem_iff[OF injective] split: option.splits)
  show "set (isabelle_unreached_entities (map (isabelle_term_rename f) roots)
      (isabelle_context_rename f names' C))=
    isabelle_entity_rename f ` set (isabelle_unreached_entities roots C)"
    by (simp add: isabelle_unreached_entities_def Let_def
      isabelle_rename_reached_constants[OF corr] reached filter_map comp_def)
qed

theorem isabelle_renamed_context_assessment:
  assumes corr: "isabelle_table_correspondence f (fst C) names'"
  shows "isabelle_context_assessment (map (isabelle_term_rename f) roots) (isabelle_context_rename f names' C)=
    isabelle_assessment_rename f (isabelle_context_assessment roots C)"
  by (simp add: isabelle_context_assessment_def isabelle_rename_unknown_positions[OF corr]
    isabelle_rename_undeclared_constants[OF isabelle_table_correspondence_injective[OF corr]]
    isabelle_rename_malformed_entities[OF corr] isabelle_rename_unreached_entities[OF corr]
    fset_of_list_map
    isabelle_rename_frontier_constants fset_of_list_map)

definition isabelle_rooted_rename ::
    "(nat \<Rightarrow> nat) \<Rightarrow> String.literal list \<Rightarrow> isabelle_rooted_context \<Rightarrow> isabelle_rooted_context" where
  "isabelle_rooted_rename f names' S=(map (isabelle_term_rename f) (fst S),isabelle_context_rename f names' (snd S))"

theorem isabelle_renamed_rooted_assessment:
  assumes corr: "isabelle_table_correspondence f (fst (snd S)) names'"
  shows "isabelle_context_assessment (fst (isabelle_rooted_rename f names' S))
      (snd (isabelle_rooted_rename f names' S))=
    isabelle_assessment_rename f (isabelle_context_assessment (fst S) (snd S))"
  by (simp add: isabelle_rooted_rename_def isabelle_renamed_context_assessment[OF corr])

section \<open>Reversing a table is one concrete correspondence\<close>

text \<open>
  Reversal moves every position of a table and fixes nothing outside it. It is one
  witness of the general contract; the theorems above hold for every correspondence.
\<close>

definition isabelle_reversal :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "isabelle_reversal n i=(if i<n then n-Suc i else i)"

lemma isabelle_reversal_injective [intro]: "inj (isabelle_reversal n)"
  by (rule injI) (auto simp: isabelle_reversal_def split: if_splits)

theorem isabelle_reversal_correspondence:
  "isabelle_table_correspondence (isabelle_reversal (length names)) names (rev names)"
proof (unfold isabelle_table_correspondence_def, intro conjI allI)
  show "inj (isabelle_reversal (length names))" by (rule isabelle_reversal_injective)
  fix i show "isabelle_name_at (rev names) (isabelle_reversal (length names) i)=isabelle_name_at names i"
  proof (cases "i<length names")
    case True
    then show ?thesis by (simp add: isabelle_reversal_def isabelle_name_at_def rev_nth)
  next
    case False
    then show ?thesis by (simp add: isabelle_reversal_def isabelle_name_at_def)
  qed
qed

text \<open>
  Nothing the seeded state computes is preserved by accident: unknown positions,
  undeclared constants, malformed and unreached entities and the frontier are each the
  image of the original reading under the same correspondence. A state that decided
  anything by a position or by table order could not satisfy this equation.
\<close>

end
