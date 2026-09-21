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

section \<open>A repaired successor records its row, and the row composes its answer\<close>

text \<open>
  When the repaired successor succeeds, the history it leaves supplies the row of the repair: its
  head is the problem of the repaired request, and its sockets hold exactly the definition problems
  the successor added to the loop's problems, each at the socket of its own constant. The successor
  then moves every problem with the correspondence into the answer state, so those problems stand,
  moved, among the successor's problems and its answered set.
\<close>

theorem development_repaired_successor_row:
  assumes successor: "development_repaired_successor (S,ps,D,answered,history) r S' I=
      Some (S2,ps',D',answered',history')"
  defines "E\<equiv>development_repair_state S r S' I"
  defines "I'\<equiv>map (isabelle_state_embedding (fst (snd S')) (fst (snd E))) I"
  defines "g\<equiv>development_problem_rename (isabelle_state_embedding (fst (snd E)) (fst (snd S')))"
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
    "ps'=map g (ps@definitions)"
    "\<And>q. q\<in>set definitions \<Longrightarrow> g q\<in>set ps' \<and> g q |\<in>| answered'"
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
  then have problems: "ps'=map g (ps@definitions)"
      and answers: "answered'=fimage g (finsert (fst r') (answered |\<union>| fset_of_list definitions))"
    unfolding g_def by (auto simp: development_successor_def Let_def split: option.splits)
  have added: "g q\<in>set ps' \<and> g q |\<in>| answered'" if "q\<in>set definitions" for q
    using that problems answers by (auto simp: fset_of_list.rep_eq fimage.rep_eq)
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

end
