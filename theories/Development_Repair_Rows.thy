theory Development_Repair_Rows
imports Development_Successor
begin

section \<open>The repair of a refused answer is a row of the development library\<close>

text \<open>
  The repair of a refused answer derives the definition problems of the constants the answer
  introduced, and the request is admitted again only once they are answered
  (\<open>development_repaired_successor\<close>). That is a decomposition of the repaired problem: its answer is
  composed of the answers to those definitions. The decomposition is recorded as a row of the
  development library, headed by the problem whose request was repaired, one socket per definition
  problem. A socket is the position of the introduced constant the problem is about, as a premise of
  a problem of a constant stands at the position of the constant it mentions
  (\<open>development_constant_premises\<close>); distinct constants stand at distinct sockets, and no two
  occurrences merge.

  The rows are read from the repair records of the history, which already hold the repair's output,
  so neither the loop nor its presentation changes. Each definition problem keeps the empty
  prerequisite row the repaired successor gives it: an answered problem settles only through a row
  headed by itself (\<open>development_answered_rules\<close>), so without it the definitions would stay
  unsettled and the library row would never fire. The library row is the trace of the
  decomposition those rows alone did not record. Nothing here issues, selects or decomposes.
\<close>


definition development_definition_sockets ::
    "development_problem list \<Rightarrow> (nat\<times>development_problem) fset" where
  "development_definition_sockets defs=fset_of_list (filter (\<lambda>(c,q). problem_subject q={|c|})
    (concat (map (\<lambda>q. map (\<lambda>c. (c,q)) (sorted_list_of_fset (problem_subject q))) defs)))"

lemma development_definition_sockets_member:
  "(c,q) |\<in>| development_definition_sockets defs \<longleftrightarrow> q\<in>set defs \<and> problem_subject q={|c|}"
  by (auto simp: development_definition_sockets_def fset_of_list.rep_eq sorted_list_of_fset.rep_eq)

text \<open>
  The definition problems of a repair are those of its introduced constants in the extended state,
  so each stands at the socket of its own constant, and the sockets hold exactly those problems.
\<close>

lemma development_definition_problems_socket:
  "(c,q) |\<in>| development_definition_sockets (development_definition_problems E I) \<longleftrightarrow>
    c\<in>set I \<and> development_constant_problem isabelle_definition_proposition Development_Definition (snd E)
      Development_Demand Development_Generated c=Some q"
proof
  assume "(c,q) |\<in>| development_definition_sockets (development_definition_problems E I)"
  then have member: "q\<in>set (development_definition_problems E I)" and subject: "problem_subject q={|c|}"
    by (simp_all add: development_definition_sockets_member)
  from member obtain d where d: "d\<in>set I" and problem: "development_constant_problem isabelle_definition_proposition
      Development_Definition (snd E) Development_Demand Development_Generated d=Some q"
    unfolding development_definition_problems_def development_constant_problems_exact by blast
  have "problem_subject q={|d|}" by (rule development_constant_problem_subject[OF problem])
  then have "d=c" using subject by (metis fsingleton_inject)
  then show "c\<in>set I \<and> development_constant_problem isabelle_definition_proposition Development_Definition (snd E)
      Development_Demand Development_Generated c=Some q" using d problem by simp
next
  assume "c\<in>set I \<and> development_constant_problem isabelle_definition_proposition Development_Definition (snd E)
      Development_Demand Development_Generated c=Some q"
  then have d: "c\<in>set I" and problem: "development_constant_problem isabelle_definition_proposition
      Development_Definition (snd E) Development_Demand Development_Generated c=Some q" by simp_all
  have "q\<in>set (development_definition_problems E I)"
    unfolding development_definition_problems_def development_constant_problems_exact using d problem by blast
  then show "(c,q) |\<in>| development_definition_sockets (development_definition_problems E I)"
    using development_constant_problem_subject[OF problem] by (simp add: development_definition_sockets_member)
qed

theorem development_definition_sockets_problems:
  "fimage snd (development_definition_sockets (development_definition_problems E I))=
    fset_of_list (development_definition_problems E I)"
proof -
  have "q\<in>snd ` fset (development_definition_sockets (development_definition_problems E I)) \<longleftrightarrow>
      q\<in>set (development_definition_problems E I)" for q
  proof
    assume "q\<in>snd ` fset (development_definition_sockets (development_definition_problems E I))"
    then obtain c where "(c,q) |\<in>| development_definition_sockets (development_definition_problems E I)" by force
    then show "q\<in>set (development_definition_problems E I)" by (simp add: development_definition_sockets_member)
  next
    assume member: "q\<in>set (development_definition_problems E I)"
    then obtain c where c: "c\<in>set I" and problem: "development_constant_problem isabelle_definition_proposition
        Development_Definition (snd E) Development_Demand Development_Generated c=Some q"
      unfolding development_definition_problems_def development_constant_problems_exact by blast
    have "(c,q) |\<in>| development_definition_sockets (development_definition_problems E I)"
      using c problem by (simp add: development_definition_problems_socket)
    then show "q\<in>snd ` fset (development_definition_sockets (development_definition_problems E I))" by force
  qed
  then have "fset (fimage snd (development_definition_sockets (development_definition_problems E I)))=
      fset (fset_of_list (development_definition_problems E I))"
    by (auto simp: fimage.rep_eq fset_of_list.rep_eq)
  then show ?thesis by (metis fimage.rep_eq fset_inject)
qed

text \<open>
  The row is formed: a socket holds one problem, because the problem of a constant in a state is
  determined by the constant.
\<close>

theorem development_definition_sockets_functional:
  "finite_premise_functional (development_definition_sockets (development_definition_problems E I))"
  by (auto simp: finite_premise_functional_def development_definition_problems_socket)

section \<open>The library rows a history supplies\<close>

definition development_repair_row ::
    "development_record \<Rightarrow> (development_problem\<times>(nat\<times>development_problem) fset) option" where
  "development_repair_row e=(case e of
     Development_Repair_Record r R \<Rightarrow> (case R of (extension,definitions,r',v',accepted) \<Rightarrow>
       if development_extension_accepted extension \<and> accepted
       then Some (fst r,development_definition_sockets definitions) else None)
   | _ \<Rightarrow> None)"

definition development_history_rows :: "development_record list \<Rightarrow> development_dependencies" where
  "development_history_rows history=fset_of_list (List.map_filter development_repair_row history)"

lemma development_repair_row_exact:
  "development_repair_row e=Some (p,H) \<longleftrightarrow> (\<exists>r extension definitions r' v'.
    e=Development_Repair_Record r (extension,definitions,r',v',True) \<and> development_extension_accepted extension \<and>
    p=fst r \<and> H=development_definition_sockets definitions)"
  by (cases e) (auto simp: development_repair_row_def split: prod.splits if_splits)

theorem development_history_rows_exact:
  "(p,H) |\<in>| development_history_rows history \<longleftrightarrow> (\<exists>r extension definitions r' v'.
    Development_Repair_Record r (extension,definitions,r',v',True)\<in>set history \<and>
    development_extension_accepted extension \<and> p=fst r \<and> H=development_definition_sockets definitions)"
  unfolding development_history_rows_def fset_of_list.rep_eq map_filter_member development_repair_row_exact
  by blast

text \<open>
  The definitions a repair records are the definition problems of its extended state, read at the
  introduced constants carried into that state.
\<close>

lemma development_refinement_repair_definitions:
  assumes repair: "development_refinement_repair S r S' I=(extension,definitions,r',v',a)"
  shows "definitions=development_definition_problems (development_repair_state S r S' I)
    (map (isabelle_state_embedding (fst (snd S')) (fst (snd (development_repair_state S r S' I)))) I)"
  using repair unfolding development_refinement_repair_def development_repair_state_def Let_def by auto

section \<open>The repaired problem keeps its locus in the extension\<close>

text \<open>
  The extension appends the names the request state lacks, so reading a problem of the request state into
  the extension gives the problem itself: the repaired problem the definitions cite stands at the same
  locus in both states.
\<close>

theorem development_repair_state_keeps:
  assumes distinct: "distinct (fst (snd S))"
    and inside: "development_problem_positions p\<subseteq>{..<length (fst (snd S))}"
  shows "development_problem_rename (isabelle_state_embedding (fst (snd S)) (fst (snd (development_repair_state S r S' I)))) p=p"
proof -
  obtain extra where names: "fst (snd (development_repair_state S r S' I))=fst (snd S)@extra"
    by (simp add: development_repair_state_def development_request_extension_def Let_def isabelle_appended_names_def)
  show ?thesis
  proof (rule development_problem_rename_fixed)
    fix i assume "i\<in>development_problem_positions p"
    then have "i<length (fst (snd S))" using inside by auto
    then show "isabelle_state_embedding (fst (snd S)) (fst (snd (development_repair_state S r S' I))) i=i"
      unfolding names by (rule isabelle_state_embedding_prefix[OF distinct])
  qed
qed

corollary development_repair_origin_locus:
  assumes distinct: "distinct (fst (snd S))"
    and inside: "development_problem_positions (fst r)\<subseteq>{..<length (fst (snd S))}"
    and q: "q\<in>set definitions"
  shows "development_repair_origin key r definitions q=Some (development_located_at key Development_Problem_Role
    (development_problem_rename (isabelle_state_embedding (fst (snd S)) (fst (snd (development_repair_state S r S' I)))) (fst r)))"
  by (simp add: development_repair_origin_def q development_repair_state_keeps[OF distinct inside])

section \<open>A loop is a context: a demanded problem cites the head of the history's row that posed it\<close>

text \<open>
  The loop reads its origins from its history: a problem cites the head of the first repair row of the
  history whose sockets hold it, the problem whose repair posed it; a problem no row holds cites nothing.
  The grant is absent: the loop's problems are generated. The origin is what posed the problem, a recorded
  decision, not a row of the dependencies, which is settlement structure a later premise may share.
\<close>

definition development_loop_origin ::
    "(nat \<Rightarrow> bool list) \<Rightarrow> development_record list \<Rightarrow> development_problem \<Rightarrow> bool list option" where
  "development_loop_origin key history p=map_option (\<lambda>z. development_located_at key Development_Problem_Role (fst z))
    (find (\<lambda>z. p |\<in>| fimage snd (snd z)) (List.map_filter development_repair_row history))"

lemma development_loop_origin_empty [simp]: "development_loop_origin key [] p=None"
  by (simp add: development_loop_origin_def)

theorem development_loop_origin_absent:
  "development_loop_origin key history p=None \<longleftrightarrow>
    (\<forall>h H. (h,H) |\<in>| development_history_rows history \<longrightarrow> p |\<notin>| fimage snd H)"
  by (auto simp: development_loop_origin_def development_history_rows_def find_None_iff fset_of_list_elem)

theorem development_loop_origin_cites:
  assumes "development_loop_origin key history p=Some l"
  obtains h H where "(h,H) |\<in>| development_history_rows history" "p |\<in>| fimage snd H"
    "l=development_located_at key Development_Problem_Role h"
proof -
  have found: "z\<in>set xs \<and> P z" if "find P xs=Some z" for P xs z using that by (induct xs) (auto split: if_splits)
  obtain z where z: "find (\<lambda>z. p |\<in>| fimage snd (snd z)) (List.map_filter development_repair_row history)=Some z"
      and l: "l=development_located_at key Development_Problem_Role (fst z)"
    using assms by (auto simp: development_loop_origin_def)
  obtain h H where hH: "z=(h,H)" by (cases z) auto
  have "(h,H) |\<in>| development_history_rows history" "p |\<in>| fimage snd H"
    using found[OF z] by (simp_all add: hH development_history_rows_def fset_of_list_elem)
  then show thesis using that l hH by simp
qed

lemma development_loop_origin_mono:
  assumes kept: "set history\<subseteq>set history'" and cited: "development_loop_origin key history p\<noteq>None"
  shows "development_loop_origin key history' p\<noteq>None"
  using assms unfolding development_loop_origin_absent development_history_rows_exact by blast

lemma development_loop_origin_extend:
  assumes kept: "set history\<subseteq>set history'"
    and new: "\<And>r ext defs r0 v0. Development_Repair_Record r (ext,defs,r0,v0,True)\<in>set history' \<Longrightarrow>
      Development_Repair_Record r (ext,defs,r0,v0,True)\<notin>set history \<Longrightarrow> p\<notin>set defs"
  shows "development_loop_origin key history' p=None \<longleftrightarrow> development_loop_origin key history p=None"
proof -
  have "(\<forall>h H. (h,H) |\<in>| development_history_rows history' \<longrightarrow> p |\<notin>| fimage snd H) \<longleftrightarrow>
      (\<forall>h H. (h,H) |\<in>| development_history_rows history \<longrightarrow> p |\<notin>| fimage snd H)"
  proof
    assume all: "\<forall>h H. (h,H) |\<in>| development_history_rows history' \<longrightarrow> p |\<notin>| fimage snd H"
    show "\<forall>h H. (h,H) |\<in>| development_history_rows history \<longrightarrow> p |\<notin>| fimage snd H"
      using all kept unfolding development_history_rows_exact by blast
  next
    assume all: "\<forall>h H. (h,H) |\<in>| development_history_rows history \<longrightarrow> p |\<notin>| fimage snd H"
    show "\<forall>h H. (h,H) |\<in>| development_history_rows history' \<longrightarrow> p |\<notin>| fimage snd H"
    proof (intro allI impI)
      fix h H assume "(h,H) |\<in>| development_history_rows history'"
      then obtain r ext defs r0 v0 where recorded: "Development_Repair_Record r (ext,defs,r0,v0,True)\<in>set history'"
          and accepted: "development_extension_accepted ext" and hH: "h=fst r" "H=development_definition_sockets defs"
        unfolding development_history_rows_exact by blast
      show "p |\<notin>| fimage snd H"
      proof (cases "Development_Repair_Record r (ext,defs,r0,v0,True)\<in>set history")
        case True
        then have "(h,H) |\<in>| development_history_rows history"
          unfolding development_history_rows_exact using accepted hH by blast
        then show ?thesis using all by blast
      next
        case False
        then have "p\<notin>set defs" by (rule new[OF recorded])
        then show ?thesis by (auto simp: hH development_definition_sockets_member)
      qed
    qed
  qed
  then show ?thesis by (simp only: development_loop_origin_absent)
qed

text \<open>
  A successor adds no repair row, so its origins are those of the loop it succeeds; and the successor
  keeps the positions of that loop's state (@{thm [source] development_successor_keeps}), so a head the
  history cites is the same problem in the successor, at the same locus, with no transport.
\<close>

theorem development_loop_origin_successor:
  assumes successor: "development_successor (S,ps,D,answered,history) r S'=Some (S2,ps',D',answered',history')"
  shows "development_loop_origin key history'=development_loop_origin key history"
proof -
  obtain G where "history'=history@[Development_Answer_Record G]"
    using development_successor_answered(3)[OF successor] by blast
  then show ?thesis by (simp add: fun_eq_iff development_loop_origin_def map_filter_def development_repair_row_def)
qed

corollary development_loop_origin_successor_keeps:
  assumes successor: "development_successor (S,ps,D,answered,history) r S'=Some (S2,ps',D',answered',history')"
    and distinct: "distinct (fst (snd S))"
    and cites: "development_loop_origin key history p=Some l"
    and inside: "\<And>h H. (h,H) |\<in>| development_history_rows history \<Longrightarrow> development_problem_positions h\<subseteq>{..<length (fst (snd S))}"
  obtains h H where "(h,H) |\<in>| development_history_rows history'" "p |\<in>| fimage snd H"
    "development_problem_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S2))) h=h"
    "development_loop_origin key history' p=Some l" "l=development_located_at key Development_Problem_Role h"
proof -
  obtain h H where row: "(h,H) |\<in>| development_history_rows history" and held: "p |\<in>| fimage snd H"
      and l: "l=development_located_at key Development_Problem_Role h"
    by (rule development_loop_origin_cites[OF cites])
  have "set history\<subseteq>set history'"
    using development_successor_answered(3)[OF successor] by auto
  then have row': "(h,H) |\<in>| development_history_rows history'"
    using row unfolding development_history_rows_exact by blast
  have kept: "development_problem_rename (isabelle_state_embedding (fst (snd S)) (fst (snd S2))) h=h"
    by (rule development_successor_keeps(2)[OF successor distinct inside[OF row]])
  have "development_loop_origin key history' p=Some l"
    using cites development_loop_origin_successor[OF successor] by simp
  then show thesis using that row' held kept l by blast
qed

subsection \<open>Every problem of a loop its constructors reach meets the premise\<close>

definition development_loop_cited :: "(nat \<Rightarrow> bool list) \<Rightarrow> development_loop \<Rightarrow> bool" where
  "development_loop_cited key L\<longleftrightarrow>(case L of (S,ps,D,answered,history) \<Rightarrow>
    \<forall>p\<in>set ps. development_row_premise (development_loop_origin key history) (\<lambda>_. None) p)"

theorem development_loop_cited_initial:
  assumes "\<And>p. p\<in>set ps \<Longrightarrow> development_row_premise (\<lambda>_. None) (\<lambda>_. None) p"
  shows "development_loop_cited key (S,ps,D,answered,[])"
  using assms by (simp add: development_loop_cited_def development_row_premise_def)

text \<open>
  A step that keeps the history and adds only repair rows holding no residual problem keeps the premise
  of every problem the loop had: a residual stays uncited, and a cited problem stays cited.
\<close>

lemma development_loop_cited_step:
  assumes cited: "development_loop_cited key (S,ps,D,answered,history)"
    and kept: "set history\<subseteq>set history'"
    and new: "\<And>r ext defs r0 v0. Development_Repair_Record r (ext,defs,r0,v0,True)\<in>set history' \<Longrightarrow>
      Development_Repair_Record r (ext,defs,r0,v0,True)\<notin>set history \<Longrightarrow>
        \<forall>q\<in>set defs. problem_origin q\<noteq>Development_Residual"
  shows "\<forall>p\<in>set ps. development_row_premise (development_loop_origin key history') (\<lambda>_. None) p"
proof
  fix p assume p: "p\<in>set ps"
  have premise: "development_row_premise (development_loop_origin key history) (\<lambda>_. None) p"
    using cited p by (simp add: development_loop_cited_def)
  have same: "development_loop_origin key history p=None \<longleftrightarrow> development_loop_origin key history' p=None"
  proof (cases "development_loop_origin key history p=None")
    case True
    then have residual: "problem_origin p=Development_Residual"
      using premise by (simp add: development_row_premise_def)
    have "development_loop_origin key history' p=None \<longleftrightarrow> development_loop_origin key history p=None"
      by (rule development_loop_origin_extend[OF kept]) (use new residual in blast)
    then show ?thesis by simp
  next
    case False
    have "development_loop_origin key history' p\<noteq>None" by (rule development_loop_origin_mono[OF kept False])
    with False show ?thesis by blast
  qed
  show "development_row_premise (development_loop_origin key history') (\<lambda>_. None) p"
    using development_row_premise_origin_cong[of "development_loop_origin key history" p
      "development_loop_origin key history'"] same premise by simp
qed

theorem development_loop_cited_successor:
  assumes cited: "development_loop_cited key (S,ps,D,answered,history)"
    and successor: "development_successor (S,ps,D,answered,history) r S'=Some L'"
  shows "development_loop_cited key L'"
proof -
  obtain S2 ps' D' answered' history' where L': "L'=(S2,ps',D',answered',history')" by (cases L') auto
  note fields=development_successor_answered[OF successor[unfolded L']]
  obtain G where history': "history'=history@[Development_Answer_Record G]" using fields(3) by blast
  have "\<forall>p\<in>set ps. development_row_premise (development_loop_origin key history') (\<lambda>_. None) p"
    by (rule development_loop_cited_step[OF cited]) (auto simp: history')
  then show ?thesis using fields(4) by (simp add: L' development_loop_cited_def)
qed

theorem development_loop_cited_selection:
  assumes cited: "development_loop_cited key (S,ps,D,answered,history)"
    and selection: "development_loop_selection (S,ps,D,answered,history)=Some (L',xs)"
  shows "development_loop_cited key L'"
proof -
  obtain Q where question: "development_selection_question D answered ps=Some Q"
    and admitted: "development_packet_problems D answered ps (native_development_packet Q)=Some xs"
    and L': "L'=(S,ps,D,answered,history@[Development_Selection_Record (native_development_packet Q) xs])"
    using selection by (auto simp: development_loop_selection_def Let_def split: option.splits)
  have "\<forall>p\<in>set ps. development_row_premise (development_loop_origin key
      (history@[Development_Selection_Record (native_development_packet Q) xs])) (\<lambda>_. None) p"
    by (rule development_loop_cited_step[OF cited]) auto
  then show ?thesis by (simp add: L' development_loop_cited_def)
qed

theorem development_loop_cited_issue:
  assumes cited: "development_loop_cited key (S,ps,D,answered,history)"
    and issue: "development_loop_issue Lib request_of (S,ps,D,answered,history) xs=(L',issued,unissued)"
  shows "development_loop_cited key L'"
proof -
  obtain more where L': "L'=(S,ps,D,answered,history@map (\<lambda>r. Development_Issue_Record r
      (development_library_reading Lib (fst r))) more)"
    using issue by (auto simp: development_loop_issue_def Let_def)
  have "\<forall>p\<in>set ps. development_row_premise (development_loop_origin key (history@map (\<lambda>r. Development_Issue_Record r
      (development_library_reading Lib (fst r))) more)) (\<lambda>_. None) p"
    by (rule development_loop_cited_step[OF cited]) auto
  then show ?thesis by (simp add: L' development_loop_cited_def)
qed

text \<open>
  On a cited loop every problem has its row in the loop's context, and so does every request whose problem
  is the loop's, each a formed value whenever the inert presentation is formed: the store's formedness
  premise for the rows the loop's reports present.
\<close>

theorem development_loop_cited_rows:
  assumes cited: "development_loop_cited key (S,ps,D,answered,history)"
    and inert: "\<And>t. finite_term_formed (inert t)"
  shows "\<And>p. p\<in>set ps \<Longrightarrow> \<exists>x. development_problem_row_data key inert (development_loop_origin key history)
      (\<lambda>_. None) p=Some x \<and> finite_term_formed x \<and> term_formed (decode_finite_term x)"
    and "\<And>r. fst r\<in>set ps \<Longrightarrow> \<exists>x. development_request_row_data key inert (development_loop_origin key history)
      (\<lambda>_. None) r=Some x \<and> finite_term_formed x \<and> term_formed (decode_finite_term x)"
proof -
  have premise: "development_row_premise (development_loop_origin key history) (\<lambda>_. None) p" if "p\<in>set ps" for p
    using cited that by (simp add: development_loop_cited_def)
  show "\<exists>x. development_problem_row_data key inert (development_loop_origin key history)
      (\<lambda>_. None) p=Some x \<and> finite_term_formed x \<and> term_formed (decode_finite_term x)" if p: "p\<in>set ps" for p
  proof -
    obtain x where row: "development_problem_row_data key inert (development_loop_origin key history) (\<lambda>_. None) p=Some x"
      using development_problem_row_data_inside[OF premise[OF p]] by blast
    show ?thesis using row development_problem_row_data_formed[OF row inert]
      development_problem_row_data_term_formed[OF row inert] by blast
  qed
  show "\<exists>x. development_request_row_data key inert (development_loop_origin key history)
      (\<lambda>_. None) r=Some x \<and> finite_term_formed x \<and> term_formed (decode_finite_term x)" if r: "fst r\<in>set ps" for r
  proof -
    obtain x where row: "development_request_row_data key inert (development_loop_origin key history) (\<lambda>_. None) r=Some x"
      using development_request_row_data_premise[of key inert _ _ r] premise[OF r] by auto
    show ?thesis using row development_request_row_data_formed[OF row inert]
      development_request_row_data_term_formed[OF row inert] by blast
  qed
qed

section \<open>A repaired successor records its row, and the row composes its answer\<close>

text \<open>
  When the repaired successor succeeds, the history it leaves supplies the row of the repair: its
  head is the problem of the repaired request, and its sockets hold exactly the definition problems
  the successor added to the loop's problems, each at the socket of its own constant. The successor
  keeps the positions of the state it succeeds, so those problems stand unchanged among the
  successor's problems and its answered set, in the coordinates of the history's rows.
\<close>

theorem development_repaired_successor_row:
  assumes successor: "development_repaired_successor (S,ps,D,answered,history) r S' I=
      Some (S2,ps',D',answered',history')"
  defines "E\<equiv>development_repair_state S r S' I"
  defines "I'\<equiv>map (isabelle_state_embedding (fst (snd S')) (fst (snd E))) I"
  obtains extension definitions r' v' where
    "development_refinement_repair S r S' I=(extension,definitions,r',v',True)"
    "development_extension_accepted extension"
    "definitions=development_definition_problems E I'"
    "(fst r,development_definition_sockets definitions) |\<in>| development_history_rows history'"
    "fimage snd (development_definition_sockets definitions)=fset_of_list definitions"
    "\<And>c q. (c,q) |\<in>| development_definition_sockets definitions \<longleftrightarrow> c\<in>set I' \<and>
      development_constant_problem isabelle_definition_proposition Development_Definition (snd E)
        Development_Demand Development_Generated c=Some q"
    "finite_premise_functional (development_definition_sockets definitions)"
    "ps'=ps@definitions"
    "\<And>q. q\<in>set definitions \<Longrightarrow> q\<in>set ps' \<and> q |\<in>| answered'"
proof -
  obtain extension definitions r' v' where repair: "development_refinement_repair S r S' I=(extension,definitions,r',v',True)"
      and accepted: "development_extension_accepted extension"
      and final: "\<exists>G S3 ps3 D3 answered3. (S2,ps',D',answered',history')=(S3,ps3,D3,answered3,history@
        [Development_Repair_Record r (extension,definitions,r',v',True),Development_Answer_Record G])"
    by (rule development_repaired_successor_records[OF successor])
  have definitions: "definitions=development_definition_problems E I'"
    using development_refinement_repair_definitions[OF repair] unfolding E_def I'_def .
  have recorded: "Development_Repair_Record r (extension,definitions,r',v',True)\<in>set history'"
    using final by auto
  have row: "(fst r,development_definition_sockets definitions) |\<in>| development_history_rows history'"
    unfolding development_history_rows_exact using recorded accepted by blast
  have moved: "development_successor (E,ps@definitions,D |\<union>| fset_of_list (map (\<lambda>q. (q,{||})) definitions),
      answered |\<union>| fset_of_list definitions,history@[Development_Repair_Record r (extension,definitions,r',v',True)])
      r' S'=Some (S2,ps',D',answered',history')"
    using successor accepted unfolding E_def by (simp add: development_repaired_successor_def repair Let_def)
  have problems: "ps'=ps@definitions"
      and answers: "answered'=finsert (fst r') (answered |\<union>| fset_of_list definitions)"
    using development_successor_answered(4,6)[OF moved] by simp_all
  have added: "q\<in>set ps' \<and> q |\<in>| answered'" if "q\<in>set definitions" for q
    using that problems answers by (auto simp: fset_of_list.rep_eq)
  show thesis
    by (rule that[OF repair accepted definitions row
          development_definition_sockets_problems[of E I', folded definitions]
          development_definition_problems_socket[of _ _ E I', folded definitions]
          development_definition_sockets_functional[of E I', folded definitions] problems added])
qed

text \<open>
  The row a repaired successor records settles its head once its definition problems are settled:
  the composition law of the library, \<open>development_composition_settles\<close>, with the history's rows
  as the library and the functionality of the sockets as the row's formation.
\<close>

corollary development_repaired_successor_settles:
  assumes successor: "development_repaired_successor (S,ps,D,answered,history) r S' I=
      Some (S2,ps',D',answered',history')"
    and settled: "\<And>q. q\<in>set (development_definition_problems (development_repair_state S r S' I)
        (map (isabelle_state_embedding (fst (snd S')) (fst (snd (development_repair_state S r S' I)))) I)) \<Longrightarrow>
      q\<in>development_composed_settled D' (development_history_rows history') answered'"
  shows "fst r\<in>development_composed_settled D' (development_history_rows history') answered'"
proof -
  obtain extension definitions r' v' where
      definitions: "definitions=development_definition_problems (development_repair_state S r S' I)
        (map (isabelle_state_embedding (fst (snd S')) (fst (snd (development_repair_state S r S' I)))) I)"
      and row: "(fst r,development_definition_sockets definitions) |\<in>| development_history_rows history'"
      and formed: "finite_premise_functional (development_definition_sockets definitions)"
    by (rule development_repaired_successor_row[OF successor]) blast+
  show ?thesis
  proof (rule development_composition_settles[OF row formed])
    fix n q assume "(n,q) |\<in>| development_definition_sockets definitions"
    then have "q\<in>set definitions" by (simp add: development_definition_sockets_member)
    then show "q\<in>development_composed_settled D' (development_history_rows history') answered'"
      using settled definitions by simp
  qed
qed


text \<open>
  A repaired successor adds its definition problems, each held by the repair row it records, so they cite
  the repaired problem; every other problem keeps its citation, the new row holding no residual.
\<close>

theorem development_loop_cited_repaired:
  assumes cited: "development_loop_cited key (S,ps,D,answered,history)"
    and successor: "development_repaired_successor (S,ps,D,answered,history) r S' I=Some L'"
  shows "development_loop_cited key L'"
proof -
  obtain S2 ps' D' answered' history' where L': "L'=(S2,ps',D',answered',history')" by (cases L') auto
  have succ: "development_repaired_successor (S,ps,D,answered,history) r S' I=Some (S2,ps',D',answered',history')"
    using successor L' by simp
  obtain extension definitions r' v' where
      repair: "development_refinement_repair S r S' I=(extension,definitions,r',v',True)"
      and row: "(fst r,development_definition_sockets definitions) |\<in>| development_history_rows history'"
      and held: "fimage snd (development_definition_sockets definitions)=fset_of_list definitions"
      and problems: "ps'=ps@definitions"
    by (rule development_repaired_successor_row[OF succ]) blast+
  obtain e2 d2 r2 v2 where repair2: "development_refinement_repair S r S' I=(e2,d2,r2,v2,True)"
      and final: "\<exists>G S3 ps3 D3 answered3. L'=(S3,ps3,D3,answered3,history@
        [Development_Repair_Record r (e2,d2,r2,v2,True),Development_Answer_Record G])"
    by (rule development_repaired_successor_records[OF successor]) blast+
  have same: "e2=extension" "d2=definitions" "r2=r'" "v2=v'" using repair repair2 by simp_all
  obtain G where history': "history'=history@[Development_Repair_Record r (extension,definitions,r',v',True),
      Development_Answer_Record G]"
    using final same L' by auto
  have demand: "problem_origin q=Development_Demand" if q: "q\<in>set definitions" for q
  proof -
    obtain C c where "development_constant_problem isabelle_definition_proposition Development_Definition
        C Development_Demand Development_Generated c=Some q"
      by (rule development_refinement_repair_definition_problem[OF repair q])
    then show ?thesis by (rule development_constant_problem_fields(2))
  qed
  have old: "\<forall>p\<in>set ps. development_row_premise (development_loop_origin key history') (\<lambda>_. None) p"
    by (rule development_loop_cited_step[OF cited]) (auto simp: history' dest: demand)
  have new: "development_row_premise (development_loop_origin key history') (\<lambda>_. None) q"
    if q: "q\<in>set definitions" for q
  proof -
    obtain C c where problem: "development_constant_problem isabelle_definition_proposition Development_Definition
        C Development_Demand Development_Generated c=Some q"
      by (rule development_refinement_repair_definition_problem[OF repair q])
    have "q |\<in>| fimage snd (development_definition_sockets definitions)" using held q by (simp add: fset_of_list_elem)
    then have cites: "development_loop_origin key history' q\<noteq>None"
      unfolding development_loop_origin_absent using row by blast
    show ?thesis by (rule development_constant_problem_premise[OF problem]) (use cites in simp_all)
  qed
  show ?thesis using old new by (auto simp: L' problems development_loop_cited_def)
qed

end
