theory Native_Control_Syntax_Statements
  imports Native_Control_Refinement_Composition Isabelle_Entity_Export
begin

section \<open>The actual whole-constructor propositions in their checked context\<close>

lemma original_syntax_statement: "syntax_join_refinement Original_Union"
  by (rule syntax_join_refinement_from_union) simp

lemma enumerated_syntax_statement: "syntax_join_refinement Enumerated_Union"
  by (rule syntax_join_refinement_from_union) simp

local_setup \<open>fn lthy =>
  let
    val thy = Proof_Context.theory_of lthy;
    val candidates = [\<^term>\<open>Original_Union\<close>, \<^term>\<open>Enumerated_Union\<close>,
      \<^term>\<open>Left_Projection\<close>];
    val propositions = map (HOLogic.mk_Trueprop o (fn m => \<^term>\<open>syntax_join_refinement\<close> $ m)) candidates;
    val accepted = [@{thm original_syntax_statement}, @{thm enumerated_syntax_statement}];
    val _ = if forall (null o Thm.hyps_of) accepted andalso
        eq_list (op aconv) (map Thm.prop_of accepted, take 2 propositions)
      then () else error "The checked propositions differ from the requested whole refinements";
    val roots = [\<^term>\<open>syntax_join_refinement\<close>, \<^term>\<open>candidate_syntax_join\<close>,
      \<^term>\<open>union_candidate_result :: union_candidate => local_address fset => local_address fset => local_address fset\<close>,
      \<^term>\<open>enumerated_union :: local_address fset => local_address fset => local_address fset\<close>,
      \<^term>\<open>finite_syntax_join\<close>] @ candidates;
    val root_names = distinct (op =) (maps (fn t => Term.add_const_names t []) roots);
    val (context, _, _, position) = Isabelle_Entity_Export.context_terms thy
      (member (op =) root_names) root_names [] [] (propositions @ roots);
    val encode = Isabelle_Entity_Export.term_term position;
    fun define name value = Local_Theory.define
      ((Binding.name name,NoSyn),((Binding.name (name ^ "_def"),[]),value)) #> snd;
  in lthy
    |> define "syntax_statement_context" context
    |> define "syntax_statement_roots" (HOLogic.mk_list \<^typ>\<open>isabelle_term\<close> (map encode roots))
    |> define "syntax_original_proposition" (encode (nth propositions 0))
    |> define "syntax_enumerated_proposition" (encode (nth propositions 1))
    |> define "syntax_projection_proposition" (encode (nth propositions 2))
    |> define "syntax_checked_propositions" (HOLogic.mk_list \<^typ>\<open>isabelle_term\<close> (map (encode o Thm.prop_of) accepted))
  end\<close>

declare syntax_statement_context_def[code] syntax_statement_roots_def[code]
  syntax_original_proposition_def[code] syntax_enumerated_proposition_def[code]
  syntax_projection_proposition_def[code] syntax_checked_propositions_def[code]

fun syntax_proposition :: "union_candidate \<Rightarrow> isabelle_term" where
  "syntax_proposition Original_Union=syntax_original_proposition"
| "syntax_proposition Enumerated_Union=syntax_enumerated_proposition"
| "syntax_proposition Left_Projection=syntax_projection_proposition"

lemma syntax_proposition_injective: "inj syntax_proposition"
  by (rule injI; rename_tac x y; case_tac x; case_tac y)
    (simp_all add: syntax_original_proposition_def syntax_enumerated_proposition_def syntax_projection_proposition_def)

lemma checked_syntax_propositions_exact:
  "p\<in>set syntax_checked_propositions \<longleftrightarrow>
    (\<exists>m. p=syntax_proposition m \<and> syntax_join_refinement m)"
proof -
  have list: "syntax_checked_propositions=[syntax_proposition Original_Union,
      syntax_proposition Enumerated_Union]"
    by (simp add: syntax_checked_propositions_def syntax_original_proposition_def syntax_enumerated_proposition_def)
  have truth: "syntax_join_refinement m \<longleftrightarrow> m=Original_Union \<or> m=Enumerated_Union" for m
    by (cases m) (simp_all add: original_syntax_statement enumerated_syntax_statement left_projection_is_not_a_refinement)
  show ?thesis by (auto simp: list truth; metis syntax_proposition.simps)
qed

type_synonym syntax_judgment_subject = "isabelle_rooted_context\<times>isabelle_term"

definition syntax_checked_rooted_context :: isabelle_rooted_context where
  "syntax_checked_rooted_context=(syntax_statement_roots,syntax_statement_context)"

definition syntax_judgment_truth :: "syntax_judgment_subject \<Rightarrow> bool" where
  "syntax_judgment_truth s \<longleftrightarrow> fst s=syntax_checked_rooted_context \<and>
    (\<exists>m. snd s=syntax_proposition m \<and> syntax_join_refinement m)"

definition syntax_judgment_check :: "syntax_judgment_subject \<Rightarrow> bool" where
  "syntax_judgment_check s=(fst s=syntax_checked_rooted_context \<and>
    snd s\<in>set syntax_checked_propositions)"

lemma syntax_judgment_check_exact:
  "syntax_judgment_check s=syntax_judgment_truth s"
  by (simp only: syntax_judgment_check_def syntax_judgment_truth_def checked_syntax_propositions_exact)

declare syntax_judgment_truth_def[code del]
lemma syntax_judgment_truth_code [code]:
  "syntax_judgment_truth s=syntax_judgment_check s"
  by (rule syntax_judgment_check_exact[symmetric])

lemma syntax_judgment_at_proposition:
  "syntax_judgment_truth (C,syntax_proposition m) \<longleftrightarrow>
    C=syntax_checked_rooted_context \<and> syntax_join_refinement m"
  by (auto simp: syntax_judgment_truth_def inj_eq[OF syntax_proposition_injective])

definition syntax_judgment_data :: "syntax_judgment_subject \<Rightarrow> finite_factor_term" where
  "syntax_judgment_data=finite_pair_presentation isabelle_rooted_context_data isabelle_term_data"

lemma syntax_judgment_data_injective: "inj syntax_judgment_data"
  unfolding syntax_judgment_data_def
  by (intro finite_pair_presentation_injective isabelle_rooted_context_data_injective
    isabelle_term_data_injective)

lemma syntax_judgment_data_formed [simp]: "finite_term_formed (syntax_judgment_data s)"
  by (simp add: syntax_judgment_data_def isabelle_rooted_context_data_def finite_pair_presentation_def
    isabelle_context_data_def finite_sequence_presentation_def finite_data_list_formed list_all_iff)

text \<open>This local truth predicate concerns exactly the three whole syntax
  refinements and the rooted context defined here. The positive statements are
  obtained from actual checked theorem objects, and their exact semantic
  correspondence is proved above, including the false projection. It is not an
  interpreter or proof checker for arbitrary encoded HOL propositions. Physical
  build provenance is still checked by the existing immutable provider boundary.\<close>

end
