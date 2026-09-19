theory Development_Native_Selection
  imports Development_Native_Readiness
begin

section \<open>The development's readiness is the native readiness of its table\<close>

text \<open>
  The development's problems, their dependencies and the answered problems are presented as the table
  native readiness reads: each problem by a key, each of its decompositions by the list of its premise keys,
  and the answered and the open problems by their keys. The keys are data and distinct problems have
  distinct keys; which list presents a finite set is the presentation's choice. On such a presentation the
  native readiness of a problem's key is exactly the development's readiness of the problem, so every
  consumer of the development's readiness can consume the native definition.
\<close>

definition readiness_presents ::
    "(development_problem \<Rightarrow> factor_term) \<Rightarrow> development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
      development_problem list \<Rightarrow> readiness_table \<Rightarrow> factor_term list \<Rightarrow> factor_term list \<Rightarrow> bool" where
  "readiness_presents key D answered ps T A Opn \<longleftrightarrow>
    inj_on key (set ps) \<and> (\<forall>p\<in>set ps. term_formed (key p) \<and> self_contained_term (key p)) \<and>
    (\<forall>p H. (p,H) |\<in>| D \<longrightarrow> p\<in>set ps \<and> snd ` fset H\<subseteq>set ps \<and> single_valued (fset H)) \<and>
    fset answered\<subseteq>set ps \<and> map fst T=map key ps \<and>
    (\<forall>p hs. p\<in>set ps \<longrightarrow> (key p,hs)\<in>set T \<longrightarrow>
      set (map set hs)=(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)) \<and>
    set A=key ` fset answered \<and> set Opn=key ` (set ps-fset answered)"

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

lemma readiness_presents_entry:
  assumes presents: "readiness_presents key D answered ps T A Opn" and p: "p\<in>set ps"
  obtains hs where "(key p,hs)\<in>set T"
proof -
  have keys: "map fst T=map key ps" using presents by (simp add: readiness_presents_def)
  obtain i where i: "i<length ps" "ps!i=p" using p by (auto simp: in_set_conv_nth)
  have length: "length T=length ps" using keys by (metis length_map)
  have "fst (T!i)=key p" using keys i length by (metis nth_map)
  then have "(key p,snd (T!i))\<in>set T" using i length by (metis nth_mem prod.collapse)
  then show ?thesis using that by blast
qed

lemma readiness_presents_keys:
  assumes presents: "readiness_presents key D answered ps T A Opn" and e: "e\<in>set T"
  shows "\<exists>p\<in>set ps. fst e=key p"
proof -
  have "fst e\<in>set (map fst T)" using e by simp
  moreover have "map fst T=map key ps" using presents by (simp add: readiness_presents_def)
  ultimately have "fst e\<in>key ` set ps" by (metis set_map)
  then show ?thesis by blast
qed

lemma readiness_presents_data:
  assumes presents: "readiness_presents key D answered ps T A Opn"
  shows "readiness_table_data T A" "data_elements Opn"
proof -
  have keyed: "\<forall>p\<in>set ps. term_formed (key p) \<and> self_contained_term (key p)"
    using presents by (simp add: readiness_presents_def)
  have answers: "set A=key ` fset answered" and within: "fset answered\<subseteq>set ps"
    and opens: "set Opn=key ` (set ps-fset answered)"
    using presents by (simp_all add: readiness_presents_def)
  have entries: "\<forall>e\<in>set T. term_formed (fst e) \<and> self_contained_term (fst e) \<and> (\<forall>h\<in>set (snd e). data_elements h)"
  proof
    fix e assume e: "e\<in>set T"
    obtain p where p: "p\<in>set ps" and key: "fst e=key p" using readiness_presents_keys[OF presents e] by blast
    have member: "(key p,snd e)\<in>set T" using e key by (metis prod.collapse)
    have sets: "set (map set (snd e))=(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)"
      using presents p member by (simp add: readiness_presents_def)
    have "\<forall>h\<in>set (snd e). \<forall>x\<in>set h. term_formed x \<and> self_contained_term x"
    proof (intro ballI)
      fix h x assume h: "h\<in>set (snd e)" and x: "x\<in>set h"
      have "set h\<in>(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)"
        using h sets by (metis image_eqI list.set_map)
      then obtain H where H: "H |\<in>| development_decompositions D p" and "set h=key ` snd ` fset H" by blast
      then obtain q where q: "q\<in>snd ` fset H" and xq: "x=key q" using x by auto
      have "(p,H) |\<in>| D" using H by (simp add: development_decompositions_member)
      then have "snd ` fset H\<subseteq>set ps" using presents by (simp add: readiness_presents_def)
      then have "q\<in>set ps" using q by blast
      then show "term_formed x \<and> self_contained_term x" using keyed xq by blast
    qed
    then show "term_formed (fst e) \<and> self_contained_term (fst e) \<and> (\<forall>h\<in>set (snd e). data_elements h)"
      using keyed p key by auto
  qed
  have "data_elements A" using answers within keyed by auto
  then show "readiness_table_data T A" using entries by (simp add: readiness_table_data_def)
  show "data_elements Opn" using opens keyed by auto
qed

lemma development_settled_problems:
  assumes presents: "readiness_presents key D answered ps T A Opn"
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
  assumes presents: "readiness_presents key D answered ps T A Opn" and settled: "k\<in>table_settled T A"
  shows "\<exists>q. k=key q \<and> q\<in>development_settled D answered"
  using settled
proof (induction rule: table_settled.induct)
  case (settle k hs h)
  have answers: "set A=key ` fset answered" and within: "fset answered\<subseteq>set ps"
    and injective: "inj_on key (set ps)"
    using presents by (simp_all add: readiness_presents_def)
  obtain q where q: "q |\<in>| answered" and kq: "k=key q" using settle.hyps(1) answers by auto
  have qps: "q\<in>set ps" using q within by auto
  have sets: "set (map set hs)=(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D q)"
    using presents qps settle.hyps(2) kq by (simp add: readiness_presents_def)
  have "set h\<in>(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D q)"
    using settle.hyps(3) sets by (metis image_eqI list.set_map)
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
  assumes presents: "readiness_presents key D answered ps T A Opn"
    and settled: "q\<in>development_settled D answered"
  shows "key q\<in>table_settled T A"
proof -
  have "finite_inference (finite_inference_rules (development_answered_rules D answered)) {} q"
    using settled by (simp add: development_settled_exact finite_inference_exact)
  then show ?thesis
  proof (induction rule: finite_inference.induct)
    case (seed a)
    then show ?case by simp
  next
    case (step H a)
    obtain G where G: "(a,G) |\<in>| development_answered_rules D answered" and HG: "H=fset G"
      using step.hyps(3) by (auto simp: finite_inference_rules_def)
    have answered_a: "a |\<in>| answered" and rule: "(a,G) |\<in>| D"
      using G by (auto simp: development_answered_rules_def)
    have answers: "set A=key ` fset answered" and within: "fset answered\<subseteq>set ps"
      using presents by (simp_all add: readiness_presents_def)
    have aps: "a\<in>set ps" using answered_a within by auto
    obtain hs where entry: "(key a,hs)\<in>set T" by (rule readiness_presents_entry[OF presents aps])
    have sets: "set (map set hs)=(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D a)"
      using presents aps entry by (simp add: readiness_presents_def)
    have "key ` snd ` fset G\<in>set (map set hs)"
      using sets rule by (auto simp: development_decompositions_member)
    then obtain h where h: "h\<in>set hs" and hG: "set h=key ` snd ` fset G" by auto
    have all: "\<forall>x\<in>set h. x\<in>table_settled T A"
      using hG step.IH HG by (auto simp: rel_ran_image)
    show ?case by (rule table_settled.settle[OF _ entry h all]) (use answers answered_a in auto)
  qed
qed

theorem native_development_ready:
  assumes presents: "readiness_presents key D answered ps T A Opn" and p: "p\<in>set ps"
  shows "(202,Pair_Term (Pair_Term (readiness_context_term T A) (data_list_term Opn)) (key p))
      \<in>positive_meaning native_readiness_system \<longleftrightarrow> development_ready D answered p"
proof -
  have data: "readiness_table_data T A" and open_data: "data_elements Opn"
    by (rule readiness_presents_data[OF presents])+
  have injective: "inj_on key (set ps)" and within: "fset answered\<subseteq>set ps"
    and opens: "set Opn=key ` (set ps-fset answered)"
    using presents by (simp_all add: readiness_presents_def)
  have opened: "key p\<in>set Opn \<longleftrightarrow> p |\<notin>| answered"
    using opens injective p within by (auto dest: inj_onD)
  have covered: "(\<exists>hs. (key p,hs)\<in>set T \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A)) \<longleftrightarrow>
      fBall (development_premises D p) (\<lambda>q. q\<in>development_settled D answered)"
  proof
    assume "\<exists>hs. (key p,hs)\<in>set T \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A)"
    then obtain hs where entry: "(key p,hs)\<in>set T" and all: "\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A" by blast
    have sets: "set (map set hs)=(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)"
      using presents p entry by (simp add: readiness_presents_def)
    show "fBall (development_premises D p) (\<lambda>q. q\<in>development_settled D answered)"
    proof
      fix q assume "q |\<in>| development_premises D p"
      then obtain H where H: "H |\<in>| development_decompositions D p" and q: "q |\<in>| fimage snd H"
        by (auto simp: development_premises_member)
      have "key ` snd ` fset H\<in>set (map set hs)" using sets H by auto
      then obtain h where h: "h\<in>set hs" and hH: "set h=key ` snd ` fset H" by auto
      have "key q\<in>set h" using hH q by auto
      then have "key q\<in>table_settled T A" using all h by blast
      then obtain q' where same: "key q=key q'" and settled_q: "q'\<in>development_settled D answered"
        using table_settled_development[OF presents] by blast
      have "(p,H) |\<in>| D" using H by (simp add: development_decompositions_member)
      then have "snd ` fset H\<subseteq>set ps" using presents by (simp add: readiness_presents_def)
      then have qps: "q\<in>set ps" using q by (auto simp: fimage.rep_eq)
      have "q'\<in>set ps" by (rule development_settled_problems[OF presents settled_q])
      then show "q\<in>development_settled D answered" using injective same qps settled_q by (auto dest: inj_onD)
    qed
  next
    assume all: "fBall (development_premises D p) (\<lambda>q. q\<in>development_settled D answered)"
    obtain hs where entry: "(key p,hs)\<in>set T" by (rule readiness_presents_entry[OF presents p])
    have sets: "set (map set hs)=(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)"
      using presents p entry by (simp add: readiness_presents_def)
    have "\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A"
    proof (intro ballI)
      fix h x assume h: "h\<in>set hs" and x: "x\<in>set h"
      have "set h\<in>(\<lambda>H. key ` snd ` fset H) ` fset (development_decompositions D p)"
        using h sets by (metis image_eqI list.set_map)
      then obtain H where H: "H |\<in>| development_decompositions D p" and hH: "set h=key ` snd ` fset H" by blast
      obtain q where q: "q\<in>snd ` fset H" and xq: "x=key q" using x hH by auto
      have "q |\<in>| development_premises D p" using H q by (auto simp: development_premises_member)
      then have "q\<in>development_settled D answered" using all by blast
      then show "x\<in>table_settled T A" using development_table_settled[OF presents] xq by blast
    qed
    then show "\<exists>hs. (key p,hs)\<in>set T \<and> (\<forall>h\<in>set hs. \<forall>x\<in>set h. x\<in>table_settled T A)" using entry by blast
  qed
  show ?thesis
    using native_ready_exact[OF data open_data] opened covered by (simp add: development_ready_def)
qed

end
