theory Development_Library_Issue
  imports Development_Native_Decomposition Development_Repair_Rows
begin

section \<open>The children of an application are computed from its intermediates\<close>

text \<open>
  An application of task 60's schema at a parent is determined by its intermediates
  (@{thm [source] development_decomposition_application_functional}): its children are the definition
  problems of the intermediates, at the first sockets, and one problem of the parent's kind for each
  constant of its subject, at the sockets after them. The children are computed here from the
  intermediates, so a row of the library is read off the application and never written.
\<close>

definition development_definition_children :: "isabelle_context \<Rightarrow> nat list \<Rightarrow> development_problem list" where
  "development_definition_children C I=List.map_filter (development_intermediate_problem C) I"

definition development_part_children :: "isabelle_context \<Rightarrow> development_problem \<Rightarrow> development_problem list" where
  "development_part_children C p=List.map_filter (development_part_problem C p) (sorted_list_of_fset (problem_subject p))"

definition development_application_children ::
    "isabelle_context \<Rightarrow> development_problem \<Rightarrow> nat list \<Rightarrow> (nat\<times>development_problem) fset" where
  "development_application_children C p I=(let zs=development_definition_children C I@development_part_children C p in
     fset_of_list (zip [0..<length zs] zs))"

theorem development_application_children_exact:
  assumes application: "development_decomposition_application C p I H"
  shows "H=development_application_children C p I"
proof -
  obtain ds rs where d: "list_all2 (\<lambda>h q. development_intermediate_problem C h=Some q) I ds"
    and r: "list_all2 (\<lambda>c q. development_part_problem C p c=Some q) (sorted_list_of_fset (problem_subject p)) rs"
    and H: "H=fset_of_list (zip [0..<length (ds@rs)] (ds@rs))"
    using application unfolding development_decomposition_application_def by blast
  have "development_definition_children C I=ds"
    unfolding development_definition_children_def by (rule list_all2_some_map_filter[OF d])
  moreover have "development_part_children C p=rs"
    unfolding development_part_children_def by (rule list_all2_some_map_filter[OF r])
  ultimately show ?thesis by (simp add: H development_application_children_def)
qed

text \<open>
  The children of an application are its definition children and its part children. At a parent
  that has a locus the part child is the parent's own problem at its own locus (task 66's entry), so
  what the application adds to the loop is its definition children: the application less its part
  child.
\<close>

theorem development_application_children_split:
  "fimage snd (development_application_children C p I)=
    fset_of_list (development_definition_children C I) |\<union>| fset_of_list (development_part_children C p)"
proof -
  let ?zs="development_definition_children C I@development_part_children C p"
  have "development_application_children C p I=fset_of_list (zip [0..<length ?zs] ?zs)"
    by (simp only: development_application_children_def Let_def)
  then have "fimage snd (development_application_children C p I)=fset_of_list (map snd (zip [0..<length ?zs] ?zs))"
    by (simp only: fset_of_list_map)
  also have "\<dots>=fset_of_list ?zs" by simp
  also have "\<dots>=fset_of_list (development_definition_children C I) |\<union>| fset_of_list (development_part_children C p)"
    by (auto simp: fset_eq_iff fset_of_list_elem)
  finally show ?thesis .
qed

section \<open>Whether the schema applies is decided from the intermediates\<close>

text \<open>
  The native schema holds at a presented parent exactly when the intermediates are nonempty and an
  application exists (@{thm [source] native_decomposition_applies}); an application exists exactly when
  every intermediate and every subject constant poses its child. That is the executable reading of the
  native contract, stated once.
\<close>

definition development_applies :: "isabelle_context \<Rightarrow> development_problem \<Rightarrow> nat list \<Rightarrow> bool" where
  "development_applies C p I \<longleftrightarrow> I\<noteq>[] \<and> sorted_list_of_fset (problem_subject p)\<noteq>[] \<and>
    list_all (\<lambda>h. development_intermediate_problem C h\<noteq>None) I \<and>
    list_all (\<lambda>c. development_part_problem C p c\<noteq>None) (sorted_list_of_fset (problem_subject p))"


theorem development_applies_exact:
  "development_applies C p I \<longleftrightarrow> I\<noteq>[] \<and> (\<exists>H. development_decomposition_application C p I H)"
proof
  assume applies: "development_applies C p I"
  have subject: "problem_subject p\<noteq>{||}"
    using applies unfolding development_applies_def by (auto simp: sorted_list_of_fset.rep_eq)
  have intermediates: "\<forall>h\<in>set I. development_intermediate_problem C h\<noteq>None"
    using applies unfolding development_applies_def by (simp add: list_all_iff)
  have parts: "\<forall>c. c |\<in>| problem_subject p \<longrightarrow> development_part_problem C p c\<noteq>None"
    using applies unfolding development_applies_def by (simp add: list_all_iff)
  show "I\<noteq>[] \<and> (\<exists>H. development_decomposition_application C p I H)"
    using applies development_decomposition_application_exists[OF subject intermediates parts]
    unfolding development_applies_def by blast
next
  assume "I\<noteq>[] \<and> (\<exists>H. development_decomposition_application C p I H)"
  then obtain H where nonempty: "I\<noteq>[]" and application: "development_decomposition_application C p I H" by blast
  obtain ds rs where subject: "problem_subject p\<noteq>{||}"
    and d: "list_all2 (\<lambda>h q. development_intermediate_problem C h=Some q) I ds"
    and r: "list_all2 (\<lambda>c q. development_part_problem C p c=Some q) (sorted_list_of_fset (problem_subject p)) rs"
    using application unfolding development_decomposition_application_def by blast
  have "\<forall>h\<in>set I. development_intermediate_problem C h\<noteq>None"
    using list_all2_members[OF d] by fastforce
  moreover have "\<forall>c\<in>set (sorted_list_of_fset (problem_subject p)). development_part_problem C p c\<noteq>None"
    using list_all2_members[OF r] by fastforce
  moreover have "sorted_list_of_fset (problem_subject p)\<noteq>[]"
    using subject by (auto simp: sorted_list_of_fset.rep_eq)
  ultimately show "development_applies C p I"
    using nonempty unfolding development_applies_def by (simp add: list_all_iff)
qed

text \<open>
  At a presented parent the executable reading is the native program's decision: the contract
  @{thm [source] native_decomposition_applies}, consumed under its own premises.
\<close>

theorem development_applies_native:
  assumes present: "development_rows_present key ekey inert origin grant supported scope decs ps rs iss rows"
    and p: "p\<in>set ps" and xf: "term_formed x" and state: "state_presents key S R"
    and identity: "\<And>y. term_formed (ident y)"
    and families: "set Fs=range (state_entities R)" and single: "declarations_single_valued Fs"
    and intermediates: "set I\<subseteq>{..<length (fst (snd S))}"
    and subject: "fset (problem_subject p)\<subseteq>{..<length (fst (snd S))}"
  shows "development_applies (snd S) p I \<longleftrightarrow> (decomposition_applies,development_decomposition_argument x rows
      (development_parent_row key inert origin grant p) key I
      (development_decomposition_families ident R [Definition_Kind])
      (development_decomposition_families ident R (development_contract_families (problem_contract p)))
      (declaration_term Fs))\<in>positive_meaning native_decomposition_system"
  by (simp only: development_applies_exact
    native_decomposition_applies[OF present p xf state identity families single intermediates subject])

section \<open>The library at a loop\<close>

text \<open>
  The library at a loop is generated, never written: the native schema's applications at the loop's
  problems that have a locus, each at an intermediate family an admissible source names, together with
  the repair rows of the loop's history. A source names intermediates; it never decides whether the
  schema applies, which the schema does. The refusal source is read from the history: a repair record
  names, at the problem of its refused request, the constants its answer introduced, which its row
  holds at its sockets. The loop's state keeps the positions of the extended state the repair made
  (@{thm [source] development_successor_keeps}), so they are read there. The split source (instance B)
  is a parameter.
\<close>

definition development_native_library ::
    "isabelle_context \<Rightarrow> (development_problem \<Rightarrow> nat list list) \<Rightarrow> development_problem list \<Rightarrow>
      development_dependencies" where
  "development_native_library C source ps=fset_of_list (concat (map (\<lambda>p. if development_subject_constant p\<noteq>None then
     List.map_filter (\<lambda>I. if development_applies C p I then Some (p,development_application_children C p I) else None)
       (source p) else []) ps))"

lemma development_native_library_member:
  "(p,H) |\<in>| development_native_library C source ps \<longleftrightarrow> p\<in>set ps \<and> development_subject_constant p\<noteq>None \<and>
    (\<exists>I\<in>set (source p). development_applies C p I \<and> H=development_application_children C p I)"
  unfolding development_native_library_def by (auto simp: fset_of_list_elem map_filter_member split: if_splits)

theorem development_native_library_exact:
  "(p,H) |\<in>| development_native_library C source ps \<longleftrightarrow> p\<in>set ps \<and> development_subject_constant p\<noteq>None \<and>
    (\<exists>I\<in>set (source p). I\<noteq>[] \<and> development_decomposition_application C p I H)"
  unfolding development_native_library_member
  using development_applies_exact development_application_children_exact by metis

text \<open>
  At a presented loop state a native row of the library is exactly a family the source names at which
  the native program holds, with the children read off it.
\<close>

theorem development_native_library_native:
  assumes present: "development_rows_present key ekey inert origin grant supported scope decs ps rs iss rows"
    and p: "p\<in>set ps" and xf: "term_formed x" and state: "state_presents key S R"
    and identity: "\<And>y. term_formed (ident y)"
    and families: "set Fs=range (state_entities R)" and single: "declarations_single_valued Fs"
    and intermediates: "\<And>I. I\<in>set (source p) \<Longrightarrow> set I\<subseteq>{..<length (fst (snd S))}"
    and subject: "fset (problem_subject p)\<subseteq>{..<length (fst (snd S))}"
  shows "(p,H) |\<in>| development_native_library (snd S) source ps \<longleftrightarrow> development_subject_constant p\<noteq>None \<and>
    (\<exists>I\<in>set (source p). (decomposition_applies,development_decomposition_argument x rows
      (development_parent_row key inert origin grant p) key I
      (development_decomposition_families ident R [Definition_Kind])
      (development_decomposition_families ident R (development_contract_families (problem_contract p)))
      (declaration_term Fs))\<in>positive_meaning native_decomposition_system \<and>
      H=development_application_children (snd S) p I)"
proof -
  have native: "development_applies (snd S) p I \<longleftrightarrow> (decomposition_applies,development_decomposition_argument x rows
      (development_parent_row key inert origin grant p) key I
      (development_decomposition_families ident R [Definition_Kind])
      (development_decomposition_families ident R (development_contract_families (problem_contract p)))
      (declaration_term Fs))\<in>positive_meaning native_decomposition_system" if "I\<in>set (source p)" for I
    by (rule development_applies_native[OF present p xf state identity families single intermediates[OF that] subject])
  show ?thesis unfolding development_native_library_member using native p by blast
qed

definition development_repair_sources :: "development_record list \<Rightarrow> development_problem \<Rightarrow> nat list list" where
  "development_repair_sources history p=List.map_filter (\<lambda>e. case development_repair_row e of None \<Rightarrow> None
     | Some (q,H) \<Rightarrow> if q=p then Some (sorted_list_of_fset (fimage fst H)) else None) history"

definition development_loop_library ::
    "(development_problem \<Rightarrow> nat list list) \<Rightarrow> development_loop \<Rightarrow> development_dependencies" where
  "development_loop_library source L=(case L of (S,ps,D,answered,history) \<Rightarrow>
     development_native_library (snd S) (\<lambda>p. source p@development_repair_sources history p) ps |\<union>|
       development_history_rows history)"

section \<open>The repair's rows are instance C's applications less their part child\<close>

text \<open>
  Task 58's repair row, headed by the repaired problem with the definition problems at the sockets of
  their constants, is the image of instance C's application under task 66's correspondence: the
  application at the extended state over the repair's intermediates, less its part child. Its children
  are that application's definition children, and the application's children are those together with
  its part children. It is not itself an application of task 60's relation: an application at a
  refinement problem has a part child of the refinement kind, and a repair row holds definition problems
  alone.
\<close>

lemma development_definition_problems_children:
  "development_definition_problems E J=development_definition_children (snd E) J"
  by (simp add: development_definition_problems_def development_constant_problems_def
    development_definition_children_def development_intermediate_problem_def[abs_def])

lemma development_repair_definitions_children:
  assumes repair: "development_refinement_repair S r S' I=(extension,definitions,r',v',a)"
  shows "definitions=development_definition_children (snd (development_repair_state S r S' I))
    (development_repair_intermediates S r S' I)"
  using development_repair_definition_problems[of S r S' I] repair
  by (simp add: development_definition_problems_children)

theorem development_repair_row_recorded:
  assumes accepted: "development_extension_accepted extension"
  shows "(fst r,development_definition_sockets definitions) |\<in>|
    development_history_rows [Development_Repair_Record r (extension,definitions,r',v',True)]"
  unfolding development_history_rows_exact using accepted by auto

theorem development_repair_sockets_children:
  assumes repair: "development_refinement_repair S r S' I=(extension,definitions,r',v',a)"
  shows "fimage snd (development_definition_sockets definitions)=fset_of_list (development_definition_children
    (snd (development_repair_state S r S' I)) (development_repair_intermediates S r S' I))"
proof -
  have defs: "definitions=development_definition_problems (development_repair_state S r S' I)
      (development_repair_intermediates S r S' I)"
    using development_repair_definition_problems[of S r S' I] repair by simp
  show ?thesis
    using development_definition_sockets_problems[of "development_repair_state S r S' I"
      "development_repair_intermediates S r S' I"]
    by (simp only: defs development_definition_problems_children)
qed

theorem development_repair_row_less_part:
  assumes repair: "development_refinement_repair S r S' I=(extension,definitions,r',v',a)"
    and application: "development_repair_application S r S' I H"
  shows "fimage snd H=fimage snd (development_definition_sockets definitions) |\<union>|
    fset_of_list (development_part_children (snd (development_repair_state S r S' I)) (fst r))"
proof -
  have "H=development_application_children (snd (development_repair_state S r S' I)) (fst r)
      (development_repair_intermediates S r S' I)"
    using application unfolding development_repair_application_def by (rule development_application_children_exact)
  then show ?thesis
    by (simp only: development_application_children_split development_repair_sockets_children[OF repair])
qed

theorem development_repair_row_not_application:
  assumes repair: "development_refinement_repair S r S' I=(extension,definitions,r',v',a)"
    and refinement: "problem_contract (fst r)=Development_Refinement t"
  shows "\<not>development_decomposition_application C (fst r) J (development_definition_sockets definitions)"
proof
  assume application: "development_decomposition_application C (fst r) J (development_definition_sockets definitions)"
  obtain ds rs where subject: "problem_subject (fst r)\<noteq>{||}"
    and parts: "list_all2 (\<lambda>c q. development_part_problem C (fst r) c=Some q) (sorted_list_of_fset (problem_subject (fst r))) rs"
    and H: "development_definition_sockets definitions=fset_of_list (zip [0..<length (ds@rs)] (ds@rs))"
    using application unfolding development_decomposition_application_def by blast
  have "sorted_list_of_fset (problem_subject (fst r))\<noteq>[]" using subject by (auto simp: sorted_list_of_fset.rep_eq)
  then obtain c where "c\<in>set (sorted_list_of_fset (problem_subject (fst r)))"
    by (cases "sorted_list_of_fset (problem_subject (fst r))") auto
  then obtain q where part: "development_part_problem C (fst r) c=Some q" and inside: "q\<in>set rs"
    using list_all2_members[OF parts] by blast
  have "q\<in>snd ` set (zip [0..<length (ds@rs)] (ds@rs))" using inside by (simp only: zip_indices_values) simp
  then obtain k where "(k,q) |\<in>| development_definition_sockets definitions" by (auto simp: H fset_of_list_elem)
  then have "q\<in>set definitions" by (simp add: development_definition_sockets_member)
  then have "q\<in>set (development_definition_problems (development_repair_state S r S' I)
      (development_repair_intermediates S r S' I))"
    using development_repair_definition_problems[of S r S' I] repair by simp
  then obtain d where "development_constant_problem isabelle_definition_proposition Development_Definition
      (snd (development_repair_state S r S' I)) Development_Demand Development_Generated d=Some q"
    unfolding development_definition_problems_def development_constant_problems_exact by blast
  then obtain s where defined: "problem_contract q=Development_Definition s"
    using development_constant_problem_contract by blast
  obtain s' where "problem_contract q=development_contract_kind (problem_contract (fst r)) s'"
    using part development_constant_problem_contract unfolding development_part_problem_def by blast
  then show False using defined refinement by simp
qed

section \<open>Instance B's source: one intermediate splitting the support\<close>

text \<open>
  A split names one constant of the state outside the parent's support whose definitions mention a
  nonempty part of it (@{const development_split_application}); the part is the computed observation
  of the state, and no threshold on its size is asserted. The source names every such constant; whether
  the schema applies at it is the schema's.
\<close>

definition development_split_sources :: "isabelle_context \<Rightarrow> development_problem \<Rightarrow> nat list list" where
  "development_split_sources C p=(case development_subject_constant p of
     Some c \<Rightarrow> (let S=development_request_support C c in map (\<lambda>h. [h]) (filter (\<lambda>h. h |\<notin>| S \<and>
       snd (hd (development_support_partition C S [h]))\<noteq>{||}) [0..<length (fst C)]))
   | None \<Rightarrow> [])"

theorem development_split_sources_split:
  assumes source: "I\<in>set (development_split_sources C p)"
    and application: "development_decomposition_application C p I H"
  obtains c h where "problem_subject p={|c|}" "I=[h]"
    "development_split_application C (development_request_support C c) p h H"
proof -
  obtain c where listed: "development_subject_constant p=Some c"
    using source by (cases "development_subject_constant p") (simp_all add: development_split_sources_def)
  have subject: "problem_subject p={|c|}" using listed by (simp only: development_subject_constant_exact)
  obtain h where I: "I=[h]" and outside: "h |\<notin>| development_request_support C c"
    and part: "snd (hd (development_support_partition C (development_request_support C c) [h]))\<noteq>{||}"
    using source listed by (auto simp: development_split_sources_def Let_def)
  have "development_split_application C (development_request_support C c) p h H"
    unfolding development_split_application_def using subject outside part application I by blast
  then show ?thesis using that subject I by blast
qed

theorem development_loop_library_exact:
  "(p,H) |\<in>| development_loop_library source (S,ps,D,answered,history) \<longleftrightarrow>
    (p\<in>set ps \<and> development_subject_constant p\<noteq>None \<and>
      (\<exists>I\<in>set (source p@development_repair_sources history p). I\<noteq>[] \<and>
        development_decomposition_application (snd S) p I H)) \<or>
    (p,H) |\<in>| development_history_rows history"
  unfolding development_loop_library_def by (simp add: development_native_library_exact)

text \<open>
  A problem whose refused answer was repaired is refused issue while its repair row stands in the
  history: the row is a rule of the library headed by it (@{thm [source] development_broad_refused}), so the
  issue at that loop sends no request for it.
\<close>

theorem development_loop_library_refuses_repaired:
  assumes recorded: "Development_Repair_Record r (extension,definitions,r',v',True)\<in>set history"
    and accepted: "development_extension_accepted extension"
  shows "\<not>development_issuable D' (development_loop_library source (S,ps,D,answered,history)) answered' (fst r)"
proof -
  have "(fst r,development_definition_sockets definitions) |\<in>| development_history_rows history"
    unfolding development_history_rows_exact using recorded accepted by blast
  then have "(fst r,development_definition_sockets definitions) |\<in>| development_loop_library source (S,ps,D,answered,history)"
    by (simp add: development_loop_library_def)
  then show ?thesis by (rule development_broad_refused)
qed

corollary development_loop_issue_refuses_repaired:
  assumes recorded: "Development_Repair_Record r (extension,definitions,r',v',True)\<in>set history"
    and accepted: "development_extension_accepted extension"
    and issue: "development_loop_issue (development_loop_library source (S,ps,D,answered,history)) request_of
      (S,ps,D,answered,history) xs=(loop',issued,unissued)"
  shows "fst r\<notin>fst ` set issued"
proof
  assume "fst r\<in>fst ` set issued"
  then obtain q where same: "fst r=fst q" and member: "q\<in>set issued" by (rule imageE)
  have "development_issuable D (development_loop_library source (S,ps,D,answered,history)) answered (fst q)"
    by (rule development_loop_issue_leaf(2)[OF issue member])
  then show False using development_loop_library_refuses_repaired[OF recorded accepted] same by metis
qed

end
