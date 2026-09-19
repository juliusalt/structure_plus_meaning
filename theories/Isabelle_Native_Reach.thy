theory Isabelle_Native_Reach
  imports Native_Table_Reach Isabelle_Entities Natural_Binary_Digits
begin

section \<open>The reach of a state is native reach over the table of its constants\<close>

text \<open>
  A state reaches a constant from its roots when the constant is the head of a root or a statement of a
  reached subject mentions it. The rows of a state's table are its constants: a key is the path of the
  binary digits of the constant's position, a row is a root when the constant heads a root, and its
  predecessors are the subjects whose statements mention it. Native reach on that table is exactly the
  state's reach; the reading of subjects and mentions from the state's entities is the presentation, and the
  closure is the native definition's.
\<close>

definition isabelle_entity_reach_pairs :: "isabelle_context \<Rightarrow> isabelle_entity \<Rightarrow> (nat\<times>nat) list" where
  "isabelle_entity_reach_pairs C e=(case isabelle_specified_proposition e of None \<Rightarrow> []
     | Some p \<Rightarrow> concat (map (\<lambda>s. map (\<lambda>c. (c,s)) (isabelle_term_constants p))
       (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e)))"

definition isabelle_reach_pairs :: "isabelle_context \<Rightarrow> (nat\<times>nat) list" where
  "isabelle_reach_pairs C=concat (map (isabelle_entity_reach_pairs C) (snd C))"

lemma isabelle_entity_reach_rules_member:
  "(c,G)\<in>set (case isabelle_specified_proposition e of None \<Rightarrow> [] | Some p \<Rightarrow> concat (map (\<lambda>s. map (\<lambda>c. (c,{|(0::nat,s)|}))
      (isabelle_term_constants p)) (isabelle_entity_subjects (fst C) (isabelle_development_constants (snd C)) e))) \<longleftrightarrow>
    (\<exists>s. (c,s)\<in>set (isabelle_entity_reach_pairs C e) \<and> G={|(0,s)|})"
  by (cases "isabelle_specified_proposition e") (auto simp: isabelle_entity_reach_pairs_def)

lemma isabelle_reach_rule_member:
  "(c,G) |\<in>| isabelle_reach_rules C \<longleftrightarrow> (\<exists>s. (c,s)\<in>set (isabelle_reach_pairs C) \<and> G={|(0,s)|})"
proof -
  have "(c,G) |\<in>| isabelle_reach_rules C \<longleftrightarrow>
      (\<exists>e\<in>set (snd C). \<exists>s. (c,s)\<in>set (isabelle_entity_reach_pairs C e) \<and> G={|(0,s)|})"
    unfolding isabelle_reach_rules_def fset_of_list_elem set_concat set_map
    using isabelle_entity_reach_rules_member[where C=C and c=c and G=G] by blast
  then show ?thesis unfolding isabelle_reach_pairs_def by auto
qed

definition isabelle_reach_heads :: "isabelle_term list \<Rightarrow> nat list" where
  "isabelle_reach_heads roots=List.map_filter isabelle_head_constant roots"

definition isabelle_reach_constants :: "isabelle_term list \<Rightarrow> isabelle_context \<Rightarrow> nat list" where
  "isabelle_reach_constants roots C=remdups (isabelle_reach_heads roots@map fst (isabelle_reach_pairs C))"

definition isabelle_reach_predecessors :: "isabelle_context \<Rightarrow> nat \<Rightarrow> nat list" where
  "isabelle_reach_predecessors C c=map snd (filter (\<lambda>q. fst q=c) (isabelle_reach_pairs C))"

definition isabelle_reach_table :: "isabelle_term list \<Rightarrow> isabelle_context \<Rightarrow> reach_table" where
  "isabelle_reach_table roots C=map (\<lambda>c. (natural_binary_digits c,c\<in>set (isabelle_reach_heads roots),
     map natural_binary_digits (isabelle_reach_predecessors C c))) (isabelle_reach_constants roots C)"

lemma isabelle_reach_table_row:
  "(k,r,ps)\<in>set (isabelle_reach_table roots C) \<longleftrightarrow> (\<exists>c. k=natural_binary_digits c \<and>
    c\<in>set (isabelle_reach_constants roots C) \<and> r=(c\<in>set (isabelle_reach_heads roots)) \<and>
    ps=map natural_binary_digits (isabelle_reach_predecessors C c))"
  by (auto simp: isabelle_reach_table_def)

lemma isabelle_reach_table_formed: "reach_table_formed (isabelle_reach_table roots C)"
  unfolding reach_table_formed_def single_valued_def by (auto simp: isabelle_reach_table_row)

lemma isabelle_reach_table_sound:
  assumes "bs\<in>table_reached (isabelle_reach_table roots C)"
  shows "\<exists>c. bs=natural_binary_digits c \<and> c\<in>isabelle_reached_constants roots C"
  using assms
proof (induction rule: table_reached.induct)
  case (root k ps)
  then obtain c where k: "k=natural_binary_digits c" and head: "c\<in>set (isabelle_reach_heads roots)"
    by (auto simp: isabelle_reach_table_row)
  have "c\<in>inference_closure (finite_inference_rules (isabelle_reach_rules C))
      (set (List.map_filter isabelle_head_constant roots))"
    using head inference_closure_seed[of "set (List.map_filter isabelle_head_constant roots)"
      "finite_inference_rules (isabelle_reach_rules C)"] by (auto simp: isabelle_reach_heads_def)
  then have "c\<in>isabelle_reached_constants roots C" by (simp only: isabelle_reached_constants_exact)
  then show ?case using k by blast
next
  case (step k r ps p)
  obtain c where k: "k=natural_binary_digits c"
    and ps: "ps=map natural_binary_digits (isabelle_reach_predecessors C c)"
    using step.hyps(1) by (auto simp: isabelle_reach_table_row)
  obtain s where s: "s\<in>set (isabelle_reach_predecessors C c)" and p: "p=natural_binary_digits s"
    using step.hyps(2) ps by auto
  obtain s' where p': "p=natural_binary_digits s'" and reached: "s'\<in>isabelle_reached_constants roots C"
    using step.IH by blast
  have same: "s'=s" using p p' by simp
  have pair: "(c,s)\<in>set (isabelle_reach_pairs C)" using s by (auto simp: isabelle_reach_predecessors_def)
  have rule: "finite_inference_rules (isabelle_reach_rules C) c {(0,s)}"
    unfolding finite_inference_rules_def using pair by (auto simp: isabelle_reach_rule_member)
  have "c\<in>inference_closure (finite_inference_rules (isabelle_reach_rules C))
      (set (List.map_filter isabelle_head_constant roots))"
  proof (rule inference_closure_step[where R="finite_inference_rules (isabelle_reach_rules C)" and a=c
      and H="{(0,s)}"])
    show "finite {(0::nat,s)}" by simp
    show "single_valued {(0::nat,s)}" by (simp add: single_valued_def)
    show "finite_inference_rules (isabelle_reach_rules C) c {(0,s)}" by (rule rule)
    show "rel_ran {(0::nat,s)}\<subseteq>inference_closure (finite_inference_rules (isabelle_reach_rules C))
        (set (List.map_filter isabelle_head_constant roots))"
      using reached same by (simp add: rel_ran_def isabelle_reached_constants_exact)
  qed
  then show ?case using k by (auto simp: isabelle_reached_constants_exact)
qed

lemma isabelle_reach_table_complete:
  assumes "c\<in>isabelle_reached_constants roots C"
  shows "natural_binary_digits c\<in>table_reached (isabelle_reach_table roots C)"
proof -
  have "finite_inference (finite_inference_rules (isabelle_reach_rules C))
      (set (List.map_filter isabelle_head_constant roots)) c"
    using assms by (simp add: isabelle_reached_constants_exact finite_inference_exact)
  then show ?thesis
  proof (induction rule: finite_inference.induct)
    case (seed a)
    have "a\<in>set (isabelle_reach_constants roots C)" "a\<in>set (isabelle_reach_heads roots)"
      using seed by (simp_all add: isabelle_reach_constants_def isabelle_reach_heads_def)
    then have "(natural_binary_digits a,True,map natural_binary_digits (isabelle_reach_predecessors C a))
        \<in>set (isabelle_reach_table roots C)"
      by (auto simp: isabelle_reach_table_row)
    then show ?case by (rule table_reached.root)
  next
    case (step H a)
    obtain G where rule: "(a,G) |\<in>| isabelle_reach_rules C" and H: "H=fset G"
      using step.hyps(3) by (auto simp: finite_inference_rules_def)
    obtain s where pair: "(a,s)\<in>set (isabelle_reach_pairs C)" and G: "G={|(0,s)|}"
      using rule by (auto simp: isabelle_reach_rule_member)
    have premise: "natural_binary_digits s\<in>table_reached (isabelle_reach_table roots C)"
      using step.IH by (simp add: H G rel_ran_def)
    have listed: "a\<in>set (isabelle_reach_constants roots C)"
      using pair by (force simp: isabelle_reach_constants_def)
    have predecessor: "s\<in>set (isabelle_reach_predecessors C a)"
      using pair by (force simp: isabelle_reach_predecessors_def)
    have row: "(natural_binary_digits a,a\<in>set (isabelle_reach_heads roots),
        map natural_binary_digits (isabelle_reach_predecessors C a))\<in>set (isabelle_reach_table roots C)"
      using listed by (auto simp: isabelle_reach_table_row)
    show ?case
      by (rule table_reached.step[OF row _ premise]) (use predecessor in auto)
  qed
qed

theorem isabelle_reach_table_exact:
  "natural_binary_digits c\<in>table_reached (isabelle_reach_table roots C) \<longleftrightarrow>
    c\<in>isabelle_reached_constants roots C"
proof
  assume "natural_binary_digits c\<in>table_reached (isabelle_reach_table roots C)"
  then obtain c' where digits: "natural_binary_digits c=natural_binary_digits c'"
    and reached: "c'\<in>isabelle_reached_constants roots C"
    by (blast dest: isabelle_reach_table_sound)
  then show "c\<in>isabelle_reached_constants roots C" by simp
next
  assume "c\<in>isabelle_reached_constants roots C"
  then show "natural_binary_digits c\<in>table_reached (isabelle_reach_table roots C)"
    by (rule isabelle_reach_table_complete)
qed

theorem isabelle_native_reached:
  "(reach_reached,Pair_Term (reach_table_term (isabelle_reach_table roots C)) (path_term (natural_binary_digits c)))
      \<in>positive_meaning native_reach_system \<longleftrightarrow> c\<in>isabelle_reached_constants roots C"
  by (simp only: native_reached_exact[OF isabelle_reach_table_formed] isabelle_reach_table_exact)

end
