theory Development_Native_Selection
  imports Development_Native_Readiness Development_Problems Factor_Finite_Development_Questions
    Complete_Value_References
begin

section \<open>The development's readiness is the native readiness of its rows\<close>

text \<open>
  The development's problems, their dependencies and the answered problems are presented as the rows native
  readiness reads: each problem by a key, its status and the lists of premise keys of its decompositions. A
  problem's readiness is judged with the table of the rows its settledness reads: the answered problems
  reachable from its premises through answered problems. An open premise ends settlement whether its row is
  present or not, so the table holds exactly the answered rows the reading can reach, and nothing else of the
  development enters it. The keys are formed terms and distinct problems have distinct keys; which list
  presents a finite set is the presentation's choice. On such a presentation the native readiness of a
  problem's row is exactly the development's readiness of the problem, so every consumer of the
  development's readiness can consume the native definition.
\<close>

definition readiness_edges :: "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
    (development_problem\<times>development_problem) set" where
  "readiness_edges D answered={(r,q). (\<exists>H. (r,H) |\<in>| D \<and> q\<in>snd ` fset H) \<and> q |\<in>| answered}"

definition readiness_entry :: "(development_problem \<Rightarrow> factor_term) \<Rightarrow> development_problem fset \<Rightarrow>
    (development_problem \<Rightarrow> factor_term list list) \<Rightarrow> development_problem \<Rightarrow> factor_term\<times>bool\<times>factor_term list list" where
  "readiness_entry key answered hs p=(key p,p |\<in>| answered,hs p)"

definition readiness_presents ::
    "(development_problem \<Rightarrow> factor_term) \<Rightarrow> development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
      development_problem list \<Rightarrow> (development_problem \<Rightarrow> factor_term list list) \<Rightarrow>
      (development_problem \<Rightarrow> readiness_table) \<Rightarrow> bool" where
  "readiness_presents key D answered ps hs cone \<longleftrightarrow>
    inj_on key (set ps) \<and> (\<forall>p\<in>set ps. term_formed (key p)) \<and>
    (\<forall>p H. (p,H) |\<in>| D \<longrightarrow> p\<in>set ps \<and> snd ` fset H\<subseteq>set ps \<and> single_valued (fset H)) \<and>
    fset answered\<subseteq>set ps \<and>
    (\<forall>p\<in>set ps. set (map set (hs p))=(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)) \<and>
    (\<forall>p\<in>set ps. set (cone p)=readiness_entry key answered hs ` {q\<in>set ps. (p,q)\<in>(readiness_edges D answered)\<^sup>+})"

lemma development_decompositions_member:
  "H |\<in>| development_decompositions D p \<longleftrightarrow> (p,H) |\<in>| D"
proof
  assume "H |\<in>| development_decompositions D p"
  then show "(p,H) |\<in>| D" by (auto simp: development_decompositions_def)
next
  assume "(p,H) |\<in>| D"
  then have "(p,H) |\<in>| ffilter (\<lambda>(q,H). q=p) D" by simp
  then have "snd (p,H) |\<in>| fimage snd (ffilter (\<lambda>(q,H). q=p) D)" by (rule fimageI)
  then show "H |\<in>| development_decompositions D p" by (simp add: development_decompositions_def)
qed

lemma readiness_presents_decompositions_formed:
  assumes presents: "readiness_presents key D answered ps hs cone" and p: "p\<in>set ps"
  shows "\<forall>h\<in>set (hs p). \<forall>x\<in>set h. term_formed x"
proof (intro ballI)
  fix h x assume h: "h\<in>set (hs p)" and x: "x\<in>set h"
  have keyed: "\<forall>p\<in>set ps. term_formed (key p)"
    and rows: "\<forall>p H. (p,H) |\<in>| D \<longrightarrow> p\<in>set ps \<and> snd ` fset H\<subseteq>set ps \<and> single_valued (fset H)"
    and sets: "set (map set (hs p))=(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)"
    using presents p by (simp_all add: readiness_presents_def)
  have "set h\<in>(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)"
    using h sets by (metis image_eqI list.set_map)
  then obtain H where H: "H |\<in>| development_decompositions D p" and hH: "set h=key ` snd ` fset H" by blast
  then obtain q where q: "q\<in>snd ` fset H" and xq: "x=key q" using x by auto
  have "(p,H) |\<in>| D" using H by (simp add: development_decompositions_member)
  then have "q\<in>set ps" using rows q by blast
  then show "term_formed x" using keyed xq by blast
qed

lemma readiness_presents_formed:
  assumes presents: "readiness_presents key D answered ps hs cone" and p: "p\<in>set ps"
  shows "readiness_table_formed (cone p)"
proof -
  have within: "set (cone p)\<subseteq>readiness_entry key answered hs ` set ps" and keyed: "\<forall>p\<in>set ps. term_formed (key p)"
    using presents p by (auto simp: readiness_presents_def)
  show ?thesis
    unfolding readiness_table_formed_def
  proof
    fix e assume "e\<in>set (cone p)"
    then obtain q where q: "q\<in>set ps" and eq: "e=readiness_entry key answered hs q" using within by blast
    show "term_formed (fst e) \<and> (\<forall>h\<in>set (snd (snd e)). \<forall>x\<in>set h. term_formed x)"
      using keyed q readiness_presents_decompositions_formed[OF presents q] by (simp add: eq readiness_entry_def)
  qed
qed

lemma development_settled_problems:
  assumes presents: "readiness_presents key D answered ps hs cone"
    and settled: "q\<in>development_settled D answered"
  shows "q\<in>set ps"
proof -
  have "q\<in>inference_closure (finite_inference_rules (development_answered_rules D answered)) {}"
    using settled by (simp add: development_settled_exact)
  then have "finite_inference (finite_inference_rules (development_answered_rules D answered)) {} q"
    by (simp add: finite_inference_exact)
  then show ?thesis
  proof (cases rule: finite_inference.cases)
    case (step H)
    then obtain G where "(q,G) |\<in>| development_answered_rules D answered"
      by (auto simp: finite_inference_rules_def)
    then show ?thesis using presents by (auto simp: development_answered_rules_def readiness_presents_def)
  qed simp
qed

lemma table_settled_development:
  assumes presents: "readiness_presents key D answered ps hs cone" and p: "p\<in>set ps"
    and settled: "k\<in>table_settled (cone p)"
  shows "\<exists>q. k=key q \<and> q\<in>development_settled D answered"
  using settled
proof (induction rule: table_settled.induct)
  case (settle k hs' h)
  have within: "set (cone p)\<subseteq>readiness_entry key answered hs ` set ps" and injective: "inj_on key (set ps)"
    using presents p by (auto simp: readiness_presents_def)
  obtain q where qps: "q\<in>set ps" and entry: "(k,True,hs')=readiness_entry key answered hs q"
    using settle.hyps(1) within by blast
  have kq: "k=key q" and q: "q |\<in>| answered" and hsq: "hs'=hs q"
    using entry by (auto simp: readiness_entry_def)
  have sets: "set (map set hs')=(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D q)"
    using presents qps hsq by (simp add: readiness_presents_def)
  have "set h\<in>(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D q)"
    using settle.hyps(2) sets by (metis image_eqI list.set_map)
  then obtain H where H: "H |\<in>| development_decompositions D q" and hH: "set h=key ` snd ` fset H" by blast
  have rule: "(q,H) |\<in>| D" using H by (simp add: development_decompositions_member)
  have formed: "snd ` fset H\<subseteq>set ps" "single_valued (fset H)"
    using presents rule by (simp_all add: readiness_presents_def)
  have premises_settled: "rel_ran (fset H)\<subseteq>development_settled D answered"
  proof
    fix r assume "r\<in>rel_ran (fset H)"
    then have r: "r\<in>snd ` fset H" by (simp add: rel_ran_image)
    then have "key r\<in>set h" using hH by blast
    then obtain r' where same: "key r=key r'" and settled_r: "r'\<in>development_settled D answered"
      using settle.IH by blast
    have "r'\<in>set ps" by (rule development_settled_problems[OF presents settled_r])
    then have "r=r'" using injective same r formed(1) by (auto dest: inj_onD)
    then show "r\<in>development_settled D answered" using settled_r by simp
  qed
  have applies: "finite_inference_rules (development_answered_rules D answered) q (fset H)"
    using rule q by (auto simp: finite_inference_rules_def development_answered_rules_def)
  have "q\<in>inference_closure (finite_inference_rules (development_answered_rules D answered)) {}"
  proof (rule inference_closure_step[where H="fset H"])
    show "finite (fset H)" by simp
    show "single_valued (fset H)" by (rule formed(2))
    show "finite_inference_rules (development_answered_rules D answered) q (fset H)" by (rule applies)
    show "rel_ran (fset H)\<subseteq>inference_closure (finite_inference_rules (development_answered_rules D answered)) {}"
      using premises_settled by (simp add: development_settled_exact)
  qed
  then show ?case using kq by (auto simp: development_settled_exact)
qed

lemma development_table_settled:
  assumes presents: "readiness_presents key D answered ps hs cone" and p: "p\<in>set ps"
    and settled: "q\<in>development_settled D answered" and reached: "(p,q)\<in>(readiness_edges D answered)\<^sup>+"
  shows "key q\<in>table_settled (cone p)"
proof -
  have within: "fset answered\<subseteq>set ps"
    and hsets: "\<forall>p\<in>set ps. set (map set (hs p))=(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)"
    and coned: "set (cone p)=readiness_entry key answered hs ` {q\<in>set ps. (p,q)\<in>(readiness_edges D answered)\<^sup>+}"
    using presents p by (simp_all add: readiness_presents_def)
  have "finite_inference (finite_inference_rules (development_answered_rules D answered)) {} q"
    using settled by (simp add: development_settled_exact finite_inference_exact)
  then show ?thesis using reached
  proof (induction rule: finite_inference.induct)
    case (seed a)
    then show ?case by simp
  next
    case (step H a)
    obtain G where G: "(a,G) |\<in>| development_answered_rules D answered" and HG: "H=fset G"
      using step.hyps(3) by (auto simp: finite_inference_rules_def)
    have answered_a: "a |\<in>| answered" and rule: "(a,G) |\<in>| D"
      using G by (auto simp: development_answered_rules_def)
    have aps: "a\<in>set ps" using answered_a within by auto
    have entry: "(key a,True,hs a)\<in>set (cone p)"
      using coned aps step.prems answered_a by (auto simp: readiness_entry_def)
    have "key ` snd ` fset G\<in>set (map set (hs a))"
      using hsets aps rule by (auto simp: development_decompositions_member)
    then obtain h where h: "h\<in>set (hs a)" and hG: "set h=key ` snd ` fset G" by auto
    have all: "\<forall>x\<in>set h. x\<in>table_settled (cone p)"
    proof
      fix x assume "x\<in>set h"
      then obtain b where b: "b\<in>snd ` fset G" and xb: "x=key b" using hG by auto
      have ran: "b\<in>rel_ran H" using b HG by (simp add: rel_ran_image)
      have "finite_inference (finite_inference_rules (development_answered_rules D answered)) {} b"
        using step.IH ran by blast
      then have "b\<in>development_settled D answered"
        by (simp add: development_settled_exact finite_inference_exact)
      then have "b |\<in>| answered" by (rule development_settled_answered)
      then have "(a,b)\<in>readiness_edges D answered" using rule b by (auto simp: readiness_edges_def)
      then have "(p,b)\<in>(readiness_edges D answered)\<^sup>+" by (rule trancl_into_trancl[OF step.prems])
      then show "x\<in>table_settled (cone p)" using step.IH ran xb by blast
    qed
    show ?case by (rule table_settled.settle[OF entry h all])
  qed
qed

theorem native_development_ready:
  assumes presents: "readiness_presents key D answered ps hs cone" and p: "p\<in>set ps" and xf: "term_formed x"
  shows "(readiness_ready,Pair_Term x (Pair_Term (readiness_table_term (cone p))
      (Pair_Term (key p) (readiness_value (p |\<in>| answered) (hs p)))))
      \<in>positive_meaning native_readiness_system \<longleftrightarrow> development_ready D answered p"
proof -
  have formed: "readiness_table_formed (cone p)" by (rule readiness_presents_formed[OF presents p])
  have kf: "term_formed (key p)" using presents p by (simp add: readiness_presents_def)
  have hf: "\<forall>h\<in>set (hs p). \<forall>x\<in>set h. term_formed x"
    by (rule readiness_presents_decompositions_formed[OF presents p])
  have injective: "inj_on key (set ps)"
    and rows: "\<forall>p H. (p,H) |\<in>| D \<longrightarrow> p\<in>set ps \<and> snd ` fset H\<subseteq>set ps \<and> single_valued (fset H)"
    and sets: "set (map set (hs p))=(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)"
    using presents p by (simp_all add: readiness_presents_def)
  have covered: "(\<forall>h\<in>set (hs p). \<forall>x\<in>set h. x\<in>table_settled (cone p)) \<longleftrightarrow>
      fBall (development_premises D p) (\<lambda>q. q\<in>development_settled D answered)"
  proof
    assume all: "\<forall>h\<in>set (hs p). \<forall>x\<in>set h. x\<in>table_settled (cone p)"
    show "fBall (development_premises D p) (\<lambda>q. q\<in>development_settled D answered)"
    proof
      fix q assume "q |\<in>| development_premises D p"
      then obtain H where H: "H |\<in>| development_decompositions D p" and q: "q |\<in>| fimage snd H"
        by (auto simp: development_premises_member)
      have "key ` snd ` fset H\<in>set (map set (hs p))" using sets H by auto
      then obtain h where h: "h\<in>set (hs p)" and hH: "set h=key ` snd ` fset H" by auto
      have "key q\<in>set h" using hH q by auto
      then have "key q\<in>table_settled (cone p)" using all h by blast
      then obtain q' where same: "key q=key q'" and settled_q: "q'\<in>development_settled D answered"
        using table_settled_development[OF presents p] by blast
      have "(p,H) |\<in>| D" using H by (simp add: development_decompositions_member)
      then have "snd ` fset H\<subseteq>set ps" using rows by blast
      then have qps: "q\<in>set ps" using q by (auto simp: fimage.rep_eq)
      have "q'\<in>set ps" by (rule development_settled_problems[OF presents settled_q])
      then show "q\<in>development_settled D answered" using injective same qps settled_q by (auto dest: inj_onD)
    qed
  next
    assume all: "fBall (development_premises D p) (\<lambda>q. q\<in>development_settled D answered)"
    show "\<forall>h\<in>set (hs p). \<forall>x\<in>set h. x\<in>table_settled (cone p)"
    proof (intro ballI)
      fix h x assume h: "h\<in>set (hs p)" and x: "x\<in>set h"
      have "set h\<in>(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)"
        using h sets by (metis image_eqI list.set_map)
      then obtain H where H: "H |\<in>| development_decompositions D p" and hH: "set h=key ` snd ` fset H" by blast
      obtain q where q: "q\<in>snd ` fset H" and xq: "x=key q" using x hH by auto
      have "q |\<in>| development_premises D p" using H q by (auto simp: development_premises_member)
      then have settled_q: "q\<in>development_settled D answered" using all by blast
      have "(p,H) |\<in>| D" using H by (simp add: development_decompositions_member)
      moreover have "q |\<in>| answered" by (rule development_settled_answered[OF settled_q])
      ultimately have "(p,q)\<in>readiness_edges D answered" using q by (auto simp: readiness_edges_def)
      then have "(p,q)\<in>(readiness_edges D answered)\<^sup>+" by (rule r_into_trancl)
      then show "x\<in>table_settled (cone p)" using development_table_settled[OF presents p settled_q] xq by blast
    qed
  qed
  show ?thesis
    using native_ready_exact[OF xf formed kf hf, of "p |\<in>| answered"] covered by (simp add: development_ready_def)
qed

section \<open>The development's readiness as native candidates\<close>

text \<open>
  The problems of a selection are presented to native readiness by their rows. A problem's key is the
  position of its first occurrence among the problems, the value reference index of the problem; its row
  holds the key, the problem's status and its decompositions, each the collection of its premise keys. Each
  candidate of the question is a problem's row together with the table of the rows its settledness reads:
  the rows of the answered problems reachable from its premises through answered problems, computed once
  for all candidates as the transitive closure of the answered-premise edges. The question judges each
  candidate on its own, so its subject is empty. Positions identify problems here and order nothing: native
  readiness compares keys only for equality.
\<close>

definition development_readiness_key :: "development_problem list \<Rightarrow> development_problem \<Rightarrow> finite_factor_term" where
  "development_readiness_key ps p=finite_development_index
    (case value_reference_index p ps of None \<Rightarrow> length ps | Some i \<Rightarrow> i)"

fun finite_data_list_elements :: "finite_factor_term \<Rightarrow> finite_factor_term list" where
  "finite_data_list_elements (Finite_Pair t r)=t#finite_data_list_elements r"
| "finite_data_list_elements t=[]"

lemma finite_data_list_elements_list [simp]: "finite_data_list_elements (finite_data_list xs)=xs"
  by (induction xs) simp_all

definition development_readiness_decompositions :: "development_dependencies \<Rightarrow> development_problem list \<Rightarrow>
    development_problem \<Rightarrow> finite_factor_term list list" where
  "development_readiness_decompositions D ps p=map finite_data_list_elements (ordered_finite_terms
    (fimage (finite_collection_presentation (development_readiness_key ps \<circ> snd)) (development_decompositions D p)))"

definition development_readiness_entry :: "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
    development_problem list \<Rightarrow> development_problem \<Rightarrow> finite_factor_term\<times>bool\<times>finite_factor_term list list" where
  "development_readiness_entry D answered ps p=(development_readiness_key ps p,p |\<in>| answered,
    development_readiness_decompositions D ps p)"

definition finite_readiness_edges :: "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
    (development_problem\<times>development_problem) fset" where
  "finite_readiness_edges D answered=ffUnion (fimage (\<lambda>(r,H).
    fimage (\<lambda>(s,q). (r,q)) (ffilter (\<lambda>(s,q). q |\<in>| answered) H)) D)"

definition development_readiness_closure :: "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
    (development_problem\<times>development_problem) fset" where
  "development_readiness_closure D answered=finite_edge_closure (finite_readiness_edges D answered)"

definition development_readiness_cone :: "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
    development_problem list \<Rightarrow> (development_problem\<times>development_problem) fset \<Rightarrow> development_problem \<Rightarrow>
      (finite_factor_term\<times>bool\<times>finite_factor_term list list) list" where
  "development_readiness_cone D answered ps E p=map (development_readiness_entry D answered ps)
    (filter (\<lambda>q. (p,q) |\<in>| E) ps)"

definition development_readiness_candidate :: "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
    development_problem list \<Rightarrow> (development_problem\<times>development_problem) fset \<Rightarrow> development_problem \<Rightarrow>
      finite_factor_term" where
  "development_readiness_candidate D answered ps E p=Finite_Pair
    (finite_readiness_table (development_readiness_cone D answered ps E p))
    (finite_readiness_row (development_readiness_key ps p) (p |\<in>| answered) (development_readiness_decompositions D ps p))"

definition development_readiness_candidates :: "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
    development_problem list \<Rightarrow> finite_factor_term list" where
  "development_readiness_candidates D answered ps=map (development_readiness_candidate D answered ps
    (development_readiness_closure D answered)) ps"

definition development_readiness_scope_closed :: "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
    development_problem list \<Rightarrow> bool" where
  "development_readiness_scope_closed D answered ps \<longleftrightarrow>
    fBall D (\<lambda>(p,H). p\<in>set ps \<and> fBall H (\<lambda>(s,q). q\<in>set ps) \<and> finite_relation_functional H) \<and>
    fBall answered (\<lambda>p. p\<in>set ps)"

lemma development_readiness_key_at:
  assumes "p\<in>set ps"
  obtains i where "value_reference_index p ps=Some i" "i<length ps" "ps!i=p"
    "development_readiness_key ps p=finite_development_index i"
proof -
  obtain i where index: "value_reference_index p ps=Some i"
    using assms value_reference_index_absent[of p ps] by (cases "value_reference_index p ps") auto
  show thesis using that[OF index] value_reference_index_read[OF index]
    by (simp add: development_readiness_key_def index)
qed

lemma development_readiness_key_injective:
  assumes p: "p\<in>set ps" and q: "q\<in>set ps"
    and same: "development_readiness_key ps p=development_readiness_key ps q"
  shows "p=q"
proof -
  obtain i where "ps!i=p" "development_readiness_key ps p=finite_development_index i"
    by (rule development_readiness_key_at[OF p])
  moreover obtain j where "ps!j=q" "development_readiness_key ps q=finite_development_index j"
    by (rule development_readiness_key_at[OF q])
  ultimately show ?thesis using same by simp
qed

lemma development_readiness_decompositions_sets:
  "set (map set (map (map decode_finite_term) (development_readiness_decompositions D ps p)))=
    (\<lambda>H. (decode_finite_term \<circ> development_readiness_key ps) ` snd ` fset H) ` fset (development_decompositions D p)"
  by (auto simp: development_readiness_decompositions_def ordered_finite_terms_set
    finite_collection_presentation_def image_image fimage.rep_eq)

lemma finite_readiness_edges_member:
  "(r,q) |\<in>| finite_readiness_edges D answered \<longleftrightarrow> (\<exists>H. (r,H) |\<in>| D \<and> q\<in>snd ` fset H) \<and> q |\<in>| answered"
proof
  assume "(r,q) |\<in>| finite_readiness_edges D answered"
  then have "\<exists>e. e |\<in>| D \<and>
      (r,q) |\<in>| (\<lambda>(r,H). fimage (\<lambda>(s,q). (r,q)) (ffilter (\<lambda>(s,q). q |\<in>| answered) H)) e"
    by (simp only: finite_readiness_edges_def finite_union_image_member)
  then obtain e where e: "e |\<in>| D"
    and m: "(r,q) |\<in>| (\<lambda>(r,H). fimage (\<lambda>(s,q). (r,q)) (ffilter (\<lambda>(s,q). q |\<in>| answered) H)) e"
    by blast
  obtain r' H where eH: "e=(r',H)" by (cases e)
  from m have "(r,q) |\<in>| fimage (\<lambda>(s,q). (r',q)) (ffilter (\<lambda>(s,q). q |\<in>| answered) H)"
    by (simp only: eH case_prod_conv)
  then obtain z where rq: "(r,q)=(\<lambda>(s,q). (r',q)) z" and z: "z |\<in>| ffilter (\<lambda>(s,q). q |\<in>| answered) H"
    by (rule fimageE)
  obtain s q' where zs: "z=(s,q')" by (cases z)
  have sq: "(s,q) |\<in>| H" and a: "q |\<in>| answered" and rr: "r=r'" using z rq by (auto simp: zs)
  have "q\<in>snd ` fset H" using sq by force
  then show "(\<exists>H. (r,H) |\<in>| D \<and> q\<in>snd ` fset H) \<and> q |\<in>| answered" using e eH rr a by blast
next
  assume "(\<exists>H. (r,H) |\<in>| D \<and> q\<in>snd ` fset H) \<and> q |\<in>| answered"
  then obtain H s where rH: "(r,H) |\<in>| D" and sq: "(s,q) |\<in>| H" and a: "q |\<in>| answered" by force
  show "(r,q) |\<in>| finite_readiness_edges D answered"
    unfolding finite_readiness_edges_def finite_union_image_member
  proof (intro exI conjI)
    show "(r,H) |\<in>| D" by (rule rH)
    show "(r,q) |\<in>| (\<lambda>(r,H). fimage (\<lambda>(s,q). (r,q)) (ffilter (\<lambda>(s,q). q |\<in>| answered) H)) (r,H)"
      using sq a by force
  qed
qed

lemma development_readiness_closure_exact:
  "(p,q) |\<in>| development_readiness_closure D answered \<longleftrightarrow> (p,q)\<in>(readiness_edges D answered)\<^sup>+"
proof -
  have "fset (finite_readiness_edges D answered)=readiness_edges D answered"
  proof (rule set_eqI)
    fix e show "e\<in>fset (finite_readiness_edges D answered) \<longleftrightarrow> e\<in>readiness_edges D answered"
      by (cases e) (simp only: readiness_edges_def finite_readiness_edges_member mem_Collect_eq case_prod_conv)
  qed
  then show ?thesis by (simp add: development_readiness_closure_def finite_edge_closure_correct)
qed

theorem development_readiness_presents:
  assumes closed: "development_readiness_scope_closed D answered ps"
  shows "readiness_presents (decode_finite_term \<circ> development_readiness_key ps) D answered ps
    (\<lambda>p. map (map decode_finite_term) (development_readiness_decompositions D ps p))
    (\<lambda>p. decode_readiness_table (development_readiness_cone D answered ps (development_readiness_closure D answered) p))"
proof -
  let ?key="decode_finite_term \<circ> development_readiness_key ps"
  let ?hs="\<lambda>p. map (map decode_finite_term) (development_readiness_decompositions D ps p)"
  let ?cone="\<lambda>p. decode_readiness_table (development_readiness_cone D answered ps (development_readiness_closure D answered) p)"
  have all: "fBall D (\<lambda>(p,H). p\<in>set ps \<and> fBall H (\<lambda>(s,q). q\<in>set ps) \<and> finite_relation_functional H)"
    and answered_all: "fBall answered (\<lambda>p. p\<in>set ps)"
    using closed by (simp_all add: development_readiness_scope_closed_def)
  have rows: "\<forall>p H. (p,H) |\<in>| D \<longrightarrow> p\<in>set ps \<and> snd ` fset H\<subseteq>set ps \<and> single_valued (fset H)"
  proof (intro allI impI)
    fix p H assume member: "(p,H) |\<in>| D"
    have fields: "p\<in>set ps" "fBall H (\<lambda>(s,q). q\<in>set ps)" "finite_relation_functional H"
      using fbspec[OF all member] by simp_all
    have "snd ` fset H\<subseteq>set ps"
    proof
      fix q assume "q\<in>snd ` fset H"
      then obtain s where sq: "(s,q) |\<in>| H" by auto
      show "q\<in>set ps" using fbspec[OF fields(2) sq] by simp
    qed
    then show "p\<in>set ps \<and> snd ` fset H\<subseteq>set ps \<and> single_valued (fset H)"
      using fields by (simp add: finite_relation_functional_correct)
  qed
  have within: "fset answered\<subseteq>set ps"
    using fbspec[OF answered_all] by blast
  have injective: "inj_on ?key (set ps)"
    by (rule inj_onI) (auto intro: development_readiness_key_injective)
  have formed: "\<forall>p\<in>set ps. term_formed (?key p)"
  proof
    fix p assume "p\<in>set ps"
    have "finite_term_formed (development_readiness_key ps p)"
      by (simp only: development_readiness_key_def finite_development_index_formed)
    then show "term_formed (?key p)" by (simp only: comp_def finite_term_formed_correct[symmetric])
  qed
  have entries: "\<forall>p\<in>set ps. set (map set (?hs p))=(\<lambda>H. ?key ` snd ` fset H) ` fset (development_decompositions D p)"
    by (intro ballI) (rule development_readiness_decompositions_sets)
  have decoded: "decode_readiness_table (map (development_readiness_entry D answered ps) qs)=
      map (readiness_entry ?key answered ?hs) qs" for qs
    by (simp add: decode_readiness_table_def development_readiness_entry_def readiness_entry_def)
  have coned: "\<forall>p\<in>set ps. set (?cone p)=
      readiness_entry ?key answered ?hs ` {q\<in>set ps. (p,q)\<in>(readiness_edges D answered)\<^sup>+}"
    by (simp add: development_readiness_cone_def decoded development_readiness_closure_exact)
  show ?thesis
    unfolding readiness_presents_def
    using injective formed rows within entries coned by blast
qed

end
