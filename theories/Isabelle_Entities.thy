theory Isabelle_Entities
  imports Isabelle_Terms Finite_Inference_Development
begin

section \<open>Checked contexts present development entities\<close>

text \<open>
  A constant of the fixed Isabelle/HOL base is presented only by its declaration. An
  expanded development constant also brings its kernel definitions, the non-definitional
  specifications that mention it and the code equations in effect in the checked context. A
  code equation is presented exactly as it was declared: it is not rewritten by any
  simplification rule, and it is the output neither of the code generator's function
  transformers nor of its preprocessor, which a refinement neither states nor answers for.
  A development constant that this state mentions without expanding is declared on its
  frontier, so the state states exactly how far it reaches and extends on demand.
  A context is its name table together with these entities; every name position of an
  entity is a position of that table. An entity is stated over its term, as a term is over its
  types, so an entity whose term presents its types elsewhere is the same datatype.
\<close>

datatype 't isabelle_entity_with =
    Isabelle_Base_Constant 't
  | Isabelle_Development_Constant 't
  | Isabelle_Frontier_Constant 't
  | Isabelle_Definition 't
  | Isabelle_Specification 't
  | Isabelle_Code_Equation 't

type_synonym isabelle_entity = "isabelle_term isabelle_entity_with"

type_synonym isabelle_context = "String.literal list\<times>isabelle_entity list"

text \<open>
  A context is judged from roots, so the roots and the context they reach form one
  subject: every control, renaming and report reads that whole subject.
\<close>

type_synonym isabelle_rooted_context = "isabelle_term list\<times>isabelle_context"

fun isabelle_entity_data :: "isabelle_entity \<Rightarrow> finite_factor_term" where
  "isabelle_entity_data (Isabelle_Base_Constant t)=Finite_Pair (Finite_Payload [0]) (isabelle_term_data t)"
| "isabelle_entity_data (Isabelle_Development_Constant t)=Finite_Pair (Finite_Payload [1]) (isabelle_term_data t)"
| "isabelle_entity_data (Isabelle_Frontier_Constant t)=Finite_Pair (Finite_Payload [2]) (isabelle_term_data t)"
| "isabelle_entity_data (Isabelle_Definition t)=Finite_Pair (Finite_Payload [3]) (isabelle_term_data t)"
| "isabelle_entity_data (Isabelle_Specification t)=Finite_Pair (Finite_Payload [4]) (isabelle_term_data t)"
| "isabelle_entity_data (Isabelle_Code_Equation t)=Finite_Pair (Finite_Payload [5]) (isabelle_term_data t)"

lemma isabelle_entity_data_injective [intro]: "inj isabelle_entity_data"
proof (rule injI)
  fix e f show "isabelle_entity_data e=isabelle_entity_data f \<Longrightarrow> e=f"
    by (cases e; cases f) (simp_all add: inj_eq[OF isabelle_term_data_injective])
qed

lemma isabelle_entity_data_formed [simp]: "finite_term_formed (isabelle_entity_data e)"
  by (cases e) (simp_all add: octets_formed_def)

theorem isabelle_entity_presentation_class:
  "presentation_class (finite_presents isabelle_entity_data) (\<lambda>_. True)
    (\<lambda>p. \<exists>e. p=decode_finite_term (isabelle_entity_data e))"
  using finite_presents_class[of isabelle_entity_data "\<lambda>_. True"] isabelle_entity_data_injective by simp

definition isabelle_entities_data :: "isabelle_entity fset \<Rightarrow> finite_factor_term" where
  "isabelle_entities_data=finite_collection_presentation isabelle_entity_data"

definition isabelle_positions_data :: "nat fset \<Rightarrow> finite_factor_term" where
  "isabelle_positions_data=finite_collection_presentation isabelle_position_data"

definition isabelle_terms_data :: "isabelle_term fset \<Rightarrow> finite_factor_term" where
  "isabelle_terms_data=finite_collection_presentation isabelle_term_data"

definition isabelle_context_data :: "isabelle_context \<Rightarrow> finite_factor_term" where
  "isabelle_context_data=finite_pair_presentation isabelle_names_data
    (finite_sequence_presentation isabelle_entity_data)"

lemma isabelle_collections_injective [intro]:
  "inj isabelle_entities_data" "inj isabelle_positions_data" "inj isabelle_terms_data"
  unfolding isabelle_entities_data_def isabelle_positions_data_def isabelle_terms_data_def
  by (intro finite_collection_presentation_injective isabelle_entity_data_injective
    isabelle_position_data_injective isabelle_term_data_injective)+

lemma isabelle_context_data_injective [intro]: "inj isabelle_context_data"
  unfolding isabelle_context_data_def
  by (intro finite_pair_presentation_injective isabelle_names_data_injective
    finite_sequence_presentation_injective isabelle_entity_data_injective)

text \<open>
  A rooted state is its ordered roots together with the context they reach; it is presented as
  that pair, so two states with equal presentations have equal roots, tables and entities.
\<close>

definition isabelle_rooted_context_data :: "isabelle_rooted_context \<Rightarrow> finite_factor_term" where
  "isabelle_rooted_context_data=finite_pair_presentation (finite_sequence_presentation isabelle_term_data)
    isabelle_context_data"

lemma isabelle_rooted_context_data_injective [intro]: "inj isabelle_rooted_context_data"
  unfolding isabelle_rooted_context_data_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective
    isabelle_term_data_injective isabelle_context_data_injective)

section \<open>Constants, equations and subjects are read structurally\<close>

fun isabelle_term_constants :: "isabelle_term \<Rightarrow> nat list" where
  "isabelle_term_constants (Isabelle_Constant c T)=[c]"
| "isabelle_term_constants (Isabelle_Free x T)=[]"
| "isabelle_term_constants (Isabelle_Variable x i T)=[]"
| "isabelle_term_constants (Isabelle_Bound i)=[]"
| "isabelle_term_constants (Isabelle_Abstraction T t)=isabelle_term_constants t"
| "isabelle_term_constants (Isabelle_Application t u)=isabelle_term_constants t@isabelle_term_constants u"

fun isabelle_head_constant :: "isabelle_term \<Rightarrow> nat option" where
  "isabelle_head_constant (Isabelle_Constant c T)=Some c"
| "isabelle_head_constant (Isabelle_Free x T)=None"
| "isabelle_head_constant (Isabelle_Variable x i T)=None"
| "isabelle_head_constant (Isabelle_Bound i)=None"
| "isabelle_head_constant (Isabelle_Abstraction T t)=None"
| "isabelle_head_constant (Isabelle_Application t u)=isabelle_head_constant t"

definition isabelle_name_at :: "String.literal list \<Rightarrow> nat \<Rightarrow> String.literal option" where
  "isabelle_name_at names i=(if i<length names then Some (names!i) else None)"

text \<open>
  An equation is recognized by the kernel's meta-equality or by HOL equality under the
  object-level judgment. These three constants belong to the fixed base, so the context's
  name table decides them; no development name is read.
\<close>

definition isabelle_judgment_name :: "String.literal" where
  "isabelle_judgment_name=STR ''HOL.Trueprop''"

definition isabelle_equality_names :: "String.literal list" where
  "isabelle_equality_names=[STR ''Pure.eq'', STR ''HOL.eq'']"

fun isabelle_equation_left :: "String.literal list \<Rightarrow> isabelle_term \<Rightarrow> isabelle_term option" where
  "isabelle_equation_left names (Isabelle_Application (Isabelle_Constant c T) p)=
    (if isabelle_name_at names c=Some isabelle_judgment_name then isabelle_equation_left names p else None)"
| "isabelle_equation_left names (Isabelle_Application (Isabelle_Application (Isabelle_Constant c T) l) r)=
    (if (\<exists>n\<in>set isabelle_equality_names. isabelle_name_at names c=Some n) then Some l else None)"
| "isabelle_equation_left names t=None"

fun isabelle_declared_constant :: "isabelle_entity \<Rightarrow> nat option" where
  "isabelle_declared_constant (Isabelle_Base_Constant t)=
    (case t of Isabelle_Constant c T \<Rightarrow> Some c | _ \<Rightarrow> None)"
| "isabelle_declared_constant (Isabelle_Development_Constant t)=
    (case t of Isabelle_Constant c T \<Rightarrow> Some c | _ \<Rightarrow> None)"
| "isabelle_declared_constant (Isabelle_Frontier_Constant t)=
    (case t of Isabelle_Constant c T \<Rightarrow> Some c | _ \<Rightarrow> None)"
| "isabelle_declared_constant (Isabelle_Definition p)=None"
| "isabelle_declared_constant (Isabelle_Specification p)=None"
| "isabelle_declared_constant (Isabelle_Code_Equation p)=None"

text \<open>
  No two entities of a state declare one constant. The obligation is the exporter's: the exporter that
  defines a state's entities (theory \<open>Isabelle_Entity_Export\<close>) owes it, and an answer state is
  exported by it too; a reader of an answer must refuse a state that fails it. It is stated here once,
  beside the reading it constrains, and every use discharges it rather than restating it.
\<close>

definition isabelle_declared_once :: "isabelle_context \<Rightarrow> bool" where
  "isabelle_declared_once C \<longleftrightarrow> (\<forall>e\<in>set (snd C). \<forall>e'\<in>set (snd C). \<forall>c.
    isabelle_declared_constant e=Some c \<longrightarrow> isabelle_declared_constant e'=Some c \<longrightarrow> e=e')"

text \<open>
  Distinct declared constants are a condition sufficient for the obligation: an optional reading whose
  values are distinct takes each value at one member only.
\<close>

lemma map_filter_unique:
  assumes distinct: "distinct (List.map_filter g xs)" and x: "x\<in>set xs" and y: "y\<in>set xs"
    and same: "g x=Some v" "g y=Some v"
  shows "x=y"
  using assms
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons z zs)
  show ?case
  proof (cases "g z")
    case None
    then have "distinct (List.map_filter g zs)" using Cons.prems(1) by (simp add: List.map_filter_simps)
    moreover have "x\<in>set zs" "y\<in>set zs" using Cons.prems(2,3,4,5) None by auto
    ultimately show ?thesis using Cons.IH Cons.prems(4,5) by blast
  next
    case (Some w)
    then have rest: "distinct (List.map_filter g zs)" and fresh: "w\<notin>set (List.map_filter g zs)"
      using Cons.prems(1) by (simp_all add: List.map_filter_simps)
    have listed: "u\<in>set us \<Longrightarrow> g u=Some w \<Longrightarrow> w\<in>set (List.map_filter g us)" for u us
      by (induction us) (auto simp: List.map_filter_simps split: option.splits)
    have inside: "u\<in>set zs \<Longrightarrow> g u=Some w \<Longrightarrow> False" for u
      using fresh listed by blast
    show ?thesis
    proof (cases "x=z")
      case True
      then have "w=v" using Some Cons.prems(4) by simp
      then show ?thesis using True Cons.prems(3,5) inside by auto
    next
      case False
      then have x': "x\<in>set zs" using Cons.prems(2) by simp
      show ?thesis
      proof (cases "y=z")
        case True
        then have "w=v" using Some Cons.prems(5) by simp
        then show ?thesis using x' Cons.prems(4) inside by auto
      next
        case False
        then have "y\<in>set zs" using Cons.prems(3) by simp
        then show ?thesis using Cons.IH[OF rest x'] Cons.prems(4,5) by blast
      qed
    qed
  qed
qed

lemma isabelle_declared_once_distinct:
  assumes "distinct (List.map_filter isabelle_declared_constant (snd C))"
  shows "isabelle_declared_once C"
  unfolding isabelle_declared_once_def using map_filter_unique[OF assms] by blast

text \<open>
  A declaration states its constant as a term of the table carrying the declared type; that term
  is what a use naming the constant itself, rather than one of its statements, refers to.
\<close>

fun isabelle_declaration_term :: "isabelle_entity \<Rightarrow> isabelle_term option" where
  "isabelle_declaration_term (Isabelle_Base_Constant t)=Some t"
| "isabelle_declaration_term (Isabelle_Development_Constant t)=Some t"
| "isabelle_declaration_term (Isabelle_Frontier_Constant t)=Some t"
| "isabelle_declaration_term (Isabelle_Definition p)=None"
| "isabelle_declaration_term (Isabelle_Specification p)=None"
| "isabelle_declaration_term (Isabelle_Code_Equation p)=None"

fun isabelle_specified_proposition :: "isabelle_entity \<Rightarrow> isabelle_term option" where
  "isabelle_specified_proposition (Isabelle_Base_Constant t)=None"
| "isabelle_specified_proposition (Isabelle_Development_Constant t)=None"
| "isabelle_specified_proposition (Isabelle_Frontier_Constant t)=None"
| "isabelle_specified_proposition (Isabelle_Definition p)=Some p"
| "isabelle_specified_proposition (Isabelle_Specification p)=Some p"
| "isabelle_specified_proposition (Isabelle_Code_Equation p)=Some p"

definition isabelle_development_constants :: "isabelle_entity list \<Rightarrow> nat list" where
  "isabelle_development_constants es=List.map_filter (\<lambda>e. case e of
     Isabelle_Development_Constant t \<Rightarrow> isabelle_declared_constant e | _ \<Rightarrow> None) es"

text \<open>
  An entity declares a development constant when it is that constant's development declaration
  (\<open>development_declared\<close>); the development constants of a list are the constants its entities declare so,
  and a constant is one of them exactly when some entity of the list declares it.
\<close>

definition development_declared :: "isabelle_entity \<Rightarrow> nat option" where
  "development_declared e=(case e of Isabelle_Development_Constant t \<Rightarrow> isabelle_declared_constant e | _ \<Rightarrow> None)"

lemma development_constants_declared: "isabelle_development_constants es=List.map_filter development_declared es"
  by (simp only: isabelle_development_constants_def development_declared_def[abs_def])

lemma development_constants_member:
  "c\<in>set (isabelle_development_constants E) \<longleftrightarrow> (\<exists>e\<in>set E. development_declared e=Some c)"
  unfolding development_constants_declared
  by (induction E) (auto simp: List.map_filter_simps split: option.splits)

definition isabelle_frontier_constants :: "isabelle_entity list \<Rightarrow> nat list" where
  "isabelle_frontier_constants es=List.map_filter (\<lambda>e. case e of
     Isabelle_Frontier_Constant t \<Rightarrow> isabelle_declared_constant e | _ \<Rightarrow> None) es"

text \<open>
  A definition or code equation belongs to the head constant of its left side. A
  specification belongs to every development constant it mentions, as a type definition
  belongs to both of its representation constants.
\<close>

fun isabelle_entity_subjects :: "String.literal list \<Rightarrow> nat list \<Rightarrow> isabelle_entity \<Rightarrow> nat list" where
  "isabelle_entity_subjects names D (Isabelle_Base_Constant t)=[]"
| "isabelle_entity_subjects names D (Isabelle_Development_Constant t)=[]"
| "isabelle_entity_subjects names D (Isabelle_Frontier_Constant t)=[]"
| "isabelle_entity_subjects names D (Isabelle_Definition p)=
    (case Option.bind (isabelle_equation_left names p) isabelle_head_constant of Some c \<Rightarrow> [c] | None \<Rightarrow> [])"
| "isabelle_entity_subjects names D (Isabelle_Specification p)=filter (\<lambda>c. c\<in>set D) (isabelle_term_constants p)"
| "isabelle_entity_subjects names D (Isabelle_Code_Equation p)=
    (case Option.bind (isabelle_equation_left names p) isabelle_head_constant of Some c \<Rightarrow> [c] | None \<Rightarrow> [])"

section \<open>Declarations, formation and reachability are computed on the presented entities\<close>

text \<open>
  Reaching a subject reaches every constant its entities mention. These are ordinary
  finite inference rules, so the reached constants are their least closure from the roots.
\<close>

definition isabelle_reach_rules :: "isabelle_context \<Rightarrow> (nat\<times>(nat\<times>nat) fset) fset" where
  "isabelle_reach_rules C=fset_of_list (concat (map (\<lambda>e. case isabelle_specified_proposition e of
     None \<Rightarrow> []
   | Some p \<Rightarrow> concat (map (\<lambda>s. map (\<lambda>c. (c,{|(0,s)|})) (isabelle_term_constants p))
       (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e))) (snd C)))"

definition isabelle_reached_constants :: "isabelle_term list \<Rightarrow> isabelle_context \<Rightarrow> nat set" where
  "isabelle_reached_constants roots C=finite_inference_result (isabelle_reach_rules C)
    (fset_of_list (List.map_filter isabelle_head_constant roots))"

theorem isabelle_reached_constants_exact:
  "isabelle_reached_constants roots C=inference_closure (finite_inference_rules (isabelle_reach_rules C))
    (set (List.map_filter isabelle_head_constant roots))"
  by (simp add: isabelle_reached_constants_def finite_inference_result_exact fset_of_list.rep_eq)

definition isabelle_entity_reached :: "nat set \<Rightarrow> isabelle_context \<Rightarrow> isabelle_entity \<Rightarrow> bool" where
  "isabelle_entity_reached R C e=(case isabelle_declared_constant e of
     Some c \<Rightarrow> c\<in>R
   | None \<Rightarrow> list_ex (\<lambda>s. s\<in>R) (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e))"

definition isabelle_unreached_entities :: "isabelle_term list \<Rightarrow> isabelle_context \<Rightarrow> isabelle_entity list" where
  "isabelle_unreached_entities roots C=(let R=isabelle_reached_constants roots C
     in filter (\<lambda>e. \<not> isabelle_entity_reached R C e) (snd C))"

definition isabelle_mentioned_constants :: "isabelle_term list \<Rightarrow> isabelle_context \<Rightarrow> nat list" where
  "isabelle_mentioned_constants roots C=List.map_filter isabelle_head_constant roots @
    concat (map (\<lambda>e. case isabelle_specified_proposition e of None \<Rightarrow> [] | Some p \<Rightarrow> isabelle_term_constants p) (snd C))"

definition isabelle_undeclared_constants :: "isabelle_term list \<Rightarrow> isabelle_context \<Rightarrow> nat list" where
  "isabelle_undeclared_constants roots C=(let declared=List.map_filter isabelle_declared_constant (snd C) in
     remdups (filter (\<lambda>c. c\<notin>set declared) (isabelle_mentioned_constants roots C)))"

definition isabelle_malformed_entities :: "isabelle_context \<Rightarrow> isabelle_entity list" where
  "isabelle_malformed_entities C=filter (\<lambda>e. case e of
     Isabelle_Specification p \<Rightarrow> False
   | _ \<Rightarrow> isabelle_declared_constant e=None \<and> isabelle_entity_subjects (fst C) [] e=[]) (snd C)"

text \<open>
  Every name position of a context must be a position of its table: an entity that names
  what the table does not hold is retained as an unknown position.
\<close>

definition isabelle_entity_positions :: "isabelle_entity \<Rightarrow> nat list" where
  "isabelle_entity_positions e=(case e of
     Isabelle_Base_Constant t \<Rightarrow> isabelle_term_positions t
   | Isabelle_Development_Constant t \<Rightarrow> isabelle_term_positions t
   | Isabelle_Frontier_Constant t \<Rightarrow> isabelle_term_positions t
   | Isabelle_Definition p \<Rightarrow> isabelle_term_positions p
   | Isabelle_Specification p \<Rightarrow> isabelle_term_positions p
   | Isabelle_Code_Equation p \<Rightarrow> isabelle_term_positions p)"

definition isabelle_unknown_positions :: "isabelle_context \<Rightarrow> nat list" where
  "isabelle_unknown_positions C=remdups (filter (\<lambda>i. isabelle_name_at (fst C) i=None)
    (concat (map isabelle_entity_positions (snd C))))"

theorem isabelle_unknown_positions_exact:
  "i\<in>set (isabelle_unknown_positions C) \<longleftrightarrow>
    (\<exists>e\<in>set (snd C). i\<in>set (isabelle_entity_positions e)) \<and> \<not> i<length (fst C)"
  by (auto simp: isabelle_unknown_positions_def isabelle_name_at_def)

theorem isabelle_unreached_entities_exact:
  "e\<in>set (isabelle_unreached_entities roots C) \<longleftrightarrow> e\<in>set (snd C) \<and>
    (case isabelle_declared_constant e of
       Some c \<Rightarrow> c\<notin>inference_closure (finite_inference_rules (isabelle_reach_rules C))
         (set (List.map_filter isabelle_head_constant roots))
     | None \<Rightarrow> (\<forall>s\<in>set (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e).
         s\<notin>inference_closure (finite_inference_rules (isabelle_reach_rules C))
           (set (List.map_filter isabelle_head_constant roots))))"
  by (auto simp: isabelle_unreached_entities_def isabelle_entity_reached_def isabelle_reached_constants_exact
    list_ex_iff Let_def split: option.splits)

theorem isabelle_undeclared_constants_exact:
  "c\<in>set (isabelle_undeclared_constants roots C) \<longleftrightarrow>
    c\<in>set (isabelle_mentioned_constants roots C) \<and> c\<notin>set (List.map_filter isabelle_declared_constant (snd C))"
  by (auto simp: isabelle_undeclared_constants_def Let_def)

section \<open>One assessment collects the computed observations of a context\<close>

type_synonym isabelle_context_assessment =
  "nat fset\<times>nat fset\<times>isabelle_entity fset\<times>isabelle_entity fset\<times>nat fset"

definition isabelle_context_assessment :: "isabelle_term list \<Rightarrow> isabelle_context \<Rightarrow> isabelle_context_assessment" where
  "isabelle_context_assessment roots C=(fset_of_list (isabelle_unknown_positions C),
    fset_of_list (isabelle_undeclared_constants roots C), fset_of_list (isabelle_malformed_entities C),
    fset_of_list (isabelle_unreached_entities roots C), fset_of_list (isabelle_frontier_constants (snd C)))"

definition isabelle_context_assessment_data :: "isabelle_context_assessment \<Rightarrow> finite_factor_term" where
  "isabelle_context_assessment_data=finite_pair_presentation isabelle_positions_data
    (finite_pair_presentation isabelle_positions_data
      (finite_pair_presentation isabelle_entities_data
        (finite_pair_presentation isabelle_entities_data isabelle_positions_data)))"

lemma isabelle_context_assessment_data_injective [intro]: "inj isabelle_context_assessment_data"
  unfolding isabelle_context_assessment_data_def
  by (intro finite_pair_presentation_injective isabelle_collections_injective)

text \<open>
  A seeded context is closed when it has no unknown position, no undeclared constant, no
  malformed entity and no unreached entity. Its frontier states which development
  constants it mentions without expanding, so extension is demanded work rather than a
  silent gap. These are computed observations of the presented context; the selection of
  items inside the checked context remains the exporter's, and a missing item of an
  expanded constant is not observable here.
\<close>

end
