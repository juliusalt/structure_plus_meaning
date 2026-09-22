theory Native_Collection_Programs
  imports Factor_Development_Criterion_Sources
begin

section \<open>Ordinary rules over native coordinates\<close>

text \<open>
  A native definition is a finite program over native coordinates: its variables, premise sockets and
  clause identities are local addresses and its definitions are sites. The collection notions of this
  theory are native definitions, each stated once as a family of ordinary rules whose conclusion binds
  every variable its premises use, so a call determines exactly the calls it premises and a program
  built from them is evaluated by demand. Each family carries its local contract, proved once for
  every formed system that holds the family at a site whose interface admits every formed term; a
  program composes the notions by choosing their sites, and its own contracts consume theirs.
\<close>

abbreviation native_var :: "nat \<Rightarrow> local_address finite_term_pattern" where
  "native_var n \<equiv> Finite_Variable [n]"

definition finite_native_rule ::
    "local_address finite_term_pattern \<Rightarrow>
      (local_address\<times>('u definition_site\<times>local_address finite_term_pattern)) list \<Rightarrow>
      (local_address,local_address,'u definition_site) finite_factor_schema" where
  "finite_native_rule p ps=\<lparr>finite_schema_conclusion=p,finite_schema_premises=fset_of_list ps,
    finite_schema_materials={||}\<rparr>"

lemma finite_native_rule_fields [simp]:
  "finite_schema_conclusion (finite_native_rule p ps)=p"
  "finite_schema_premises (finite_native_rule p ps)=fset_of_list ps"
  "finite_schema_materials (finite_native_rule p ps)={||}"
  by (simp_all add: finite_native_rule_def)

lemma decode_finite_native_rule [simp]:
  "schema_conclusion (decode_finite_schema (finite_native_rule p ps))=decode_finite_pattern p"
  "schema_premises (decode_finite_schema (finite_native_rule p ps))=
    (\<lambda>(s,d,q). (s,d,decode_finite_pattern q)) ` set ps"
  "schema_material_premises (decode_finite_schema (finite_native_rule p ps))={}"
  by (auto simp: finite_native_rule_def map_relation_values_def decode_finite_call_pattern_def
    fset_of_list.rep_eq decode_finite_schema_def split_def image_iff)

lemma native_rule_variables:
  "schema_variables (decode_finite_schema (finite_native_rule p ps))=
    pattern_variables (decode_finite_pattern p) \<union> (\<Union>(s,d,q)\<in>set ps. pattern_variables (decode_finite_pattern q))"
  unfolding schema_variables_def decode_finite_native_rule by auto

lemma native_rule_support:
  assumes support: "\<forall>s e r. (s,e,r)\<in>schema_premises (decode_finite_schema (finite_native_rule p ps)) \<longrightarrow>
      (e,evaluate_pattern f r)\<in>Y"
  shows "\<forall>(s,e,q)\<in>set ps. (e,evaluate_pattern f (decode_finite_pattern q))\<in>Y"
proof (intro ballI, clarify)
  fix s e q assume member: "(s,e,q)\<in>set ps"
  have "(s,e,decode_finite_pattern q)\<in>(\<lambda>(s,d,q). (s,d,decode_finite_pattern q)) ` set ps"
    using member by force
  then have "(s,e,decode_finite_pattern q)\<in>schema_premises (decode_finite_schema (finite_native_rule p ps))"
    by (simp only: decode_finite_native_rule)
  then show "(e,evaluate_pattern f (decode_finite_pattern q))\<in>Y" using support by blast
qed

definition native_values :: "factor_term list \<Rightarrow> local_address \<Rightarrow> factor_term" where
  "native_values ts v=ts!hd v"

lemma native_values_variable [simp]: "native_values ts [n]=ts!n"
  by (simp add: native_values_def)

lemma data_list_term_pair:
  "data_list_term xs=Pair_Term a b \<longleftrightarrow> (\<exists>ys. xs=a#ys \<and> b=data_list_term ys)"
  "Pair_Term a b=data_list_term xs \<longleftrightarrow> (\<exists>ys. xs=a#ys \<and> b=data_list_term ys)"
  by (cases xs; auto)+

lemma data_list_term_payload:
  "data_list_term xs=Payload_Term v \<longleftrightarrow> xs=[] \<and> v=[]"
  "Payload_Term v=data_list_term xs \<longleftrightarrow> xs=[] \<and> v=[]"
  by (cases xs; auto)+

lemma data_list_term_target [simp]:
  "data_list_term xs\<noteq>Target_Term a" "Target_Term a\<noteq>data_list_term xs"
  by (cases xs; simp)+

lemma data_rows_pair:
  "data_list_term (map (case_prod Pair_Term) rows)=Pair_Term a b \<longleftrightarrow>
    (\<exists>k v rows'. rows=(k,v)#rows' \<and> a=Pair_Term k v \<and> b=data_list_term (map (case_prod Pair_Term) rows'))"
  "Pair_Term a b=data_list_term (map (case_prod Pair_Term) rows) \<longleftrightarrow>
    (\<exists>k v rows'. rows=(k,v)#rows' \<and> a=Pair_Term k v \<and> b=data_list_term (map (case_prod Pair_Term) rows'))"
proof -
  show first: "data_list_term (map (case_prod Pair_Term) rows)=Pair_Term a b \<longleftrightarrow>
    (\<exists>k v rows'. rows=(k,v)#rows' \<and> a=Pair_Term k v \<and> b=data_list_term (map (case_prod Pair_Term) rows'))"
  proof (cases rows)
    case Nil
    then show ?thesis by simp
  next
    case (Cons r rows')
    then show ?thesis by (cases r) auto
  qed
  then show "Pair_Term a b=data_list_term (map (case_prod Pair_Term) rows) \<longleftrightarrow>
    (\<exists>k v rows'. rows=(k,v)#rows' \<and> a=Pair_Term k v \<and> b=data_list_term (map (case_prod Pair_Term) rows'))"
    by (simp only: eq_commute[of "Pair_Term a b"])
qed

lemma data_rows_formed:
  "term_formed (data_list_term (map (case_prod Pair_Term) rows)) \<longleftrightarrow>
    (\<forall>(k,v)\<in>set rows. term_formed k \<and> term_formed v)"
  by (induction rows) (auto simp: octets_formed_def)

lemma positive_meaning_term_formed:
  assumes "(d,t)\<in>positive_meaning P"
  shows "term_formed t"
  using schema_call_formed_target[OF positive_meaning_formed[OF assms]] by blast

section \<open>A family of ordinary rules at one site\<close>

locale native_rule_family =
  fixes P :: "'u native_system" and site :: "'u definition_site"
    and rules :: "(local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list"
  assumes system_formed: "schema_system_formed P"
    and family: "\<And>c S. ((site,c),S)\<in>system_clauses P \<longleftrightarrow>
      (\<exists>F. (c,F)\<in>set rules \<and> S=decode_finite_schema F)"
    and call: "\<And>t. schema_call_formed P site t \<longleftrightarrow> term_formed t"
    and ordinary: "\<forall>r\<in>set rules. finite_schema_materials (snd r)={||}"
begin

lemma rule_clause:
  assumes "(c,F)\<in>set rules"
  shows "((site,c),decode_finite_schema F)\<in>system_clauses P"
  using assms family by blast

lemma rule_formed:
  assumes "(c,F)\<in>set rules"
  shows "schema_formed (decode_finite_schema F)"
proof -
  have "((site,c),decode_finite_schema F)\<in>system_clauses P" by (rule rule_clause[OF assms])
  then show ?thesis using system_formed unfolding schema_system_formed_def by blast
qed

lemma rule_ordinary:
  assumes "(c,F)\<in>set rules"
  shows "schema_material_premises (decode_finite_schema F)={}"
  using assms ordinary by (auto simp: map_relation_values_def decode_finite_schema_def)

lemma step:
  assumes rule: "(c,F)\<in>set rules"
    and assignment: "\<forall>a\<in>schema_variables (decode_finite_schema F). term_formed (f a)"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning P"
  shows "(site,evaluate_pattern f (schema_conclusion (decode_finite_schema F)))\<in>positive_meaning P"
proof -
  have sf: "schema_formed (decode_finite_schema F)" by (rule rule_formed[OF rule])
  have tf: "term_formed (evaluate_pattern f (schema_conclusion (decode_finite_schema F)))"
    by (rule evaluate_pattern_formed)
      (use sf assignment in \<open>auto simp: schema_formed_def schema_variables_def\<close>)
  show ?thesis
    by (rule ordinary_positive_valuation_step[OF rule_clause[OF rule] rule_ordinary[OF rule] assignment _ support])
      (simp only: call tf)
qed

lemma native_step:
  assumes rule: "(c,finite_native_rule p ps)\<in>set rules"
    and assignment: "\<forall>a\<in>pattern_variables (decode_finite_pattern p) \<union>
      (\<Union>(s,d,q)\<in>set ps. pattern_variables (decode_finite_pattern q)). term_formed (f a)"
    and support: "\<forall>(s,d,q)\<in>set ps. (d,evaluate_pattern f (decode_finite_pattern q))\<in>positive_meaning P"
  shows "(site,evaluate_pattern f (decode_finite_pattern p))\<in>positive_meaning P"
proof -
  have "(site,evaluate_pattern f (schema_conclusion (decode_finite_schema (finite_native_rule p ps))))
      \<in>positive_meaning P"
  proof (rule step[OF rule])
    show "\<forall>a\<in>schema_variables (decode_finite_schema (finite_native_rule p ps)). term_formed (f a)"
      using assignment by (simp only: native_rule_variables)
    show "\<forall>s e r. (s,e,r)\<in>schema_premises (decode_finite_schema (finite_native_rule p ps)) \<longrightarrow>
        (e,evaluate_pattern f r)\<in>positive_meaning P"
      unfolding decode_finite_native_rule using support by auto
  qed
  then show ?thesis by simp
qed

lemma holds_cases:
  assumes holds: "(site,t)\<in>positive_meaning P"
  obtains c F f where "(c,F)\<in>set rules"
    "\<forall>a\<in>schema_variables (decode_finite_schema F). term_formed (f a)"
    "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=t"
    "\<forall>s e p. (s,e,p)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
      (e,evaluate_pattern f p)\<in>positive_meaning P"
proof -
  obtain c S where member: "(c,S)\<in>system_clause_family P site"
    and rule_instance: "schema_rule_instance S (positive_meaning P) t"
    using holds positive_variable_rule_family[OF call] by blast
  obtain F where rule: "(c,F)\<in>set rules" and S: "S=decode_finite_schema F"
    using member family by (auto simp: system_clause_family_def)
  have rule_instance': "schema_rule_instance (decode_finite_schema F) (positive_meaning P) t"
    using rule_instance S by simp
  obtain f where assignment: "\<forall>a\<in>schema_variables (decode_finite_schema F). term_formed (f a)"
    and shape: "t=evaluate_pattern f (schema_conclusion (decode_finite_schema F))"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
      (d,evaluate_pattern f p)\<in>positive_meaning P"
    using rule_instance' ordinary_schema_rule_valuation[OF rule_formed[OF rule] rule_ordinary[OF rule]] by blast
  show thesis by (rule that[OF rule assignment shape[symmetric] support])
qed

lemma holds_formed: "(site,t)\<in>positive_meaning P \<Longrightarrow> term_formed t"
  by (rule positive_meaning_term_formed)

end

section \<open>Membership in a list\<close>

definition native_member_here :: "(local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_member_here=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 0) (native_var 1))) []"

definition native_member_later :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_member_later m=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2)))
    [([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"

text \<open>
  A rule without a site of its own is a polymorphic value; its code is inlined where it is used, so the
  generated program holds it at the site type of its use.
\<close>

declare native_member_here_def [code_unfold]

definition native_member_rules :: "'u definition_site \<Rightarrow>
    (local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list" where
  "native_member_rules m=[([0],native_member_here),([1],native_member_later m)]"

locale native_member_program = native_rule_family P m "native_member_rules m"
  for P :: "'u native_system" and m :: "'u definition_site"
begin

lemma unfold:
  assumes clause: "((m,c),S)\<in>system_clauses P"
    and support: "\<forall>s e p. (s,e,p)\<in>schema_premises S \<longrightarrow> (e,evaluate_pattern f p)\<in>Y"
    and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term x (data_list_term xs)"
  shows "\<exists>y ys. xs=y#ys \<and> (x=y \<or> (m,Pair_Term x (data_list_term ys))\<in>Y)"
proof -
  obtain F where rule: "(c,F)\<in>set (native_member_rules m)" and S: "S=decode_finite_schema F"
    using clause family by blast
  have cases: "F=native_member_here \<or> F=native_member_later m"
    using rule by (auto simp: native_member_rules_def)
  then show ?thesis
  proof
    assume F: "F=native_member_here"
    show ?thesis using shape by (auto simp: S F native_member_here_def data_list_term_pair)
  next
    assume F: "F=native_member_later m"
    have premise: "(m,Pair_Term (f [0]) (f [2]))\<in>Y"
      using native_rule_support[OF support[unfolded S F native_member_later_def]] by simp
    show ?thesis using shape premise by (auto simp: S F native_member_later_def data_list_term_pair)
  qed
qed

theorem exact:
  "(m,Pair_Term x (data_list_term xs))\<in>positive_meaning P \<longleftrightarrow> x\<in>set xs \<and> (\<forall>y\<in>set xs. term_formed y)"
proof
  assume holds: "(m,Pair_Term x (data_list_term xs))\<in>positive_meaning P"
  have formed: "\<forall>y\<in>set xs. term_formed y"
    using holds_formed[OF holds] by (simp add: data_list_term_formed)
  have "x\<in>set xs" using holds
  proof (induction xs)
    case Nil
    obtain c F f where "(c,F)\<in>set (native_member_rules m)"
      and "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=Pair_Term x (data_list_term [])"
      by (rule holds_cases[OF Nil.prems]) blast
    then show ?case by (auto simp: native_member_rules_def native_member_here_def native_member_later_def)
  next
    case (Cons y ys)
    obtain c F f where rule: "(c,F)\<in>set (native_member_rules m)"
      and shape: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=Pair_Term x (data_list_term (y#ys))"
      and support: "\<forall>s e p. (s,e,p)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
        (e,evaluate_pattern f p)\<in>positive_meaning P"
      by (rule holds_cases[OF Cons.prems]) blast
    have "\<exists>y' ys'. y#ys=y'#ys' \<and> (x=y' \<or> (m,Pair_Term x (data_list_term ys'))\<in>positive_meaning P)"
      by (rule unfold[OF rule_clause[OF rule] support shape])
    then show ?case using Cons.IH by auto
  qed
  then show "x\<in>set xs \<and> (\<forall>y\<in>set xs. term_formed y)" using formed by blast
next
  assume "x\<in>set xs \<and> (\<forall>y\<in>set xs. term_formed y)"
  then show "(m,Pair_Term x (data_list_term xs))\<in>positive_meaning P"
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons y ys)
    have formed: "term_formed y" "\<forall>z\<in>set ys. term_formed z" "term_formed (data_list_term ys)"
      using Cons.prems by (auto simp: data_list_term_formed)
    show ?case
    proof (cases "x=y")
      case True
      have "(m,evaluate_pattern (native_values [x,data_list_term ys])
          (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 0) (native_var 1)))))
          \<in>positive_meaning P"
        by (rule native_step[where c="[0]" and ps="[]"])
          (use formed True in \<open>simp_all add: native_member_rules_def native_member_here_def\<close>)
      then show ?thesis using True by simp
    next
      case False
      have inner: "(m,Pair_Term x (data_list_term ys))\<in>positive_meaning P"
        using Cons False by auto
      have xf: "term_formed x" using Cons.prems by auto
      have "(m,evaluate_pattern (native_values [x,y,data_list_term ys])
          (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2)))))
          \<in>positive_meaning P"
        by (rule native_step[where c="[1]" and ps="[([0],(m,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"])
          (use formed xf inner in \<open>simp_all add: native_member_rules_def native_member_later_def\<close>)
      then show ?thesis by simp
    qed
  qed
qed

end

section \<open>Every element of a list, in a context\<close>

definition native_every_nil :: "(local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_every_nil=finite_native_rule (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Payload [])) []"

definition native_every_step :: "'u definition_site \<Rightarrow> 'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_every_step e el=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2)))
    [([0],(el,Finite_Pattern_Pair (native_var 0) (native_var 1))),
     ([1],(e,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"

declare native_every_nil_def [code_unfold]

definition native_every_rules :: "'u definition_site \<Rightarrow> 'u definition_site \<Rightarrow>
    (local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list" where
  "native_every_rules e el=[([0],native_every_nil),([1],native_every_step e el)]"

locale native_every_program = native_rule_family P e "native_every_rules e el"
  for P :: "'u native_system" and e el :: "'u definition_site"
begin

lemma unfold:
  assumes clause: "((e,c),S)\<in>system_clauses P"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern f p)\<in>Y"
    and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term x (data_list_term zs)"
  shows "zs=[] \<or> (\<exists>z zs'. zs=z#zs' \<and> (el,Pair_Term x z)\<in>Y \<and> (e,Pair_Term x (data_list_term zs'))\<in>Y)"
proof -
  obtain F where rule: "(c,F)\<in>set (native_every_rules e el)" and S: "S=decode_finite_schema F"
    using clause family by blast
  have cases: "F=native_every_nil \<or> F=native_every_step e el"
    using rule by (auto simp: native_every_rules_def)
  then show ?thesis
  proof
    assume F: "F=native_every_nil"
    show ?thesis using shape by (auto simp: S F native_every_nil_def data_list_term_payload)
  next
    assume F: "F=native_every_step e el"
    have premises_hold: "(el,Pair_Term (f [0]) (f [1]))\<in>Y" "(e,Pair_Term (f [0]) (f [2]))\<in>Y"
      using native_rule_support[OF support[unfolded S F native_every_step_def]] by simp_all
    show ?thesis using shape premises_hold by (auto simp: S F native_every_step_def data_list_term_pair)
  qed
qed

lemma relation_equation:
  "(e,t)\<in>positive_meaning P \<longleftrightarrow> (\<exists>a. t=Pair_Term a (Payload_Term []) \<and> term_formed a) \<or>
    (\<exists>a x y. t=Pair_Term a (Pair_Term x y) \<and> (el,Pair_Term a x)\<in>positive_meaning P \<and>
      (e,Pair_Term a y)\<in>positive_meaning P)"
proof
  assume holds: "(e,t)\<in>positive_meaning P"
  obtain c F f where rule: "(c,F)\<in>set (native_every_rules e el)"
    and assignment: "\<forall>a\<in>schema_variables (decode_finite_schema F). term_formed (f a)"
    and shape: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=t"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
      (d,evaluate_pattern f p)\<in>positive_meaning P"
    by (rule holds_cases[OF holds])
  have cases: "F=native_every_nil \<or> F=native_every_step e el"
    using rule by (auto simp: native_every_rules_def)
  then show "(\<exists>a. t=Pair_Term a (Payload_Term []) \<and> term_formed a) \<or>
    (\<exists>a x y. t=Pair_Term a (Pair_Term x y) \<and> (el,Pair_Term a x)\<in>positive_meaning P \<and>
      (e,Pair_Term a y)\<in>positive_meaning P)"
  proof
    assume F: "F=native_every_nil"
    have "term_formed (f [0])"
      using assignment by (simp add: F native_every_nil_def native_rule_variables)
    then show ?thesis using shape by (auto simp: F native_every_nil_def)
  next
    assume F: "F=native_every_step e el"
    have premises_hold: "(el,Pair_Term (f [0]) (f [1]))\<in>positive_meaning P"
        "(e,Pair_Term (f [0]) (f [2]))\<in>positive_meaning P"
      using native_rule_support[OF support[unfolded F native_every_step_def]] by simp_all
    then show ?thesis using shape by (auto simp: F native_every_step_def)
  qed
next
  assume "(\<exists>a. t=Pair_Term a (Payload_Term []) \<and> term_formed a) \<or>
    (\<exists>a x y. t=Pair_Term a (Pair_Term x y) \<and> (el,Pair_Term a x)\<in>positive_meaning P \<and>
      (e,Pair_Term a y)\<in>positive_meaning P)"
  then show "(e,t)\<in>positive_meaning P"
  proof
    assume "\<exists>a. t=Pair_Term a (Payload_Term []) \<and> term_formed a"
    then obtain a where t: "t=Pair_Term a (Payload_Term [])" and af: "term_formed a" by blast
    have "(e,evaluate_pattern (native_values [a])
        (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Payload []))))\<in>positive_meaning P"
      by (rule native_step[where c="[0]" and ps="[]"])
        (use af in \<open>simp_all add: native_every_rules_def native_every_nil_def octets_formed_def\<close>)
    then show ?thesis using t by simp
  next
    assume "\<exists>a x y. t=Pair_Term a (Pair_Term x y) \<and> (el,Pair_Term a x)\<in>positive_meaning P \<and>
      (e,Pair_Term a y)\<in>positive_meaning P"
    then obtain a x y where t: "t=Pair_Term a (Pair_Term x y)"
      and element: "(el,Pair_Term a x)\<in>positive_meaning P"
      and inner: "(e,Pair_Term a y)\<in>positive_meaning P" by blast
    have formed: "term_formed a" "term_formed x" "term_formed y"
      using positive_meaning_term_formed[OF element] positive_meaning_term_formed[OF inner] by simp_all
    have "(e,evaluate_pattern (native_values [a,x,y])
        (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2)))))
        \<in>positive_meaning P"
      by (rule native_step[where c="[1]" and ps="[([0],(el,Finite_Pattern_Pair (native_var 0) (native_var 1))),
          ([1],(e,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"])
        (use element inner formed in \<open>simp_all add: native_every_rules_def native_every_step_def\<close>)
    then show ?thesis using t by simp
  qed
qed

sublocale semantics: context_list_rule_relation "positive_meaning P" el e
  by unfold_locales (rule relation_equation)

lemmas exact = semantics.lists

end

section \<open>Some element of a list, in a context\<close>

definition native_some_first :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_some_first el=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2)))
    [([0],(el,Finite_Pattern_Pair (native_var 0) (native_var 1)))]"

definition native_some_rest :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_some_rest s=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2)))
    [([0],(s,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"

definition native_some_rules :: "'u definition_site \<Rightarrow> 'u definition_site \<Rightarrow>
    (local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list" where
  "native_some_rules s el=[([0],native_some_first el),([1],native_some_rest s)]"

locale native_some_program = native_rule_family P s "native_some_rules s el"
  for P :: "'u native_system" and s el :: "'u definition_site"
begin

lemma unfold:
  assumes clause: "((s,c),S)\<in>system_clauses P"
    and support: "\<forall>k d p. (k,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern f p)\<in>Y"
    and shape: "evaluate_pattern f (schema_conclusion S)=Pair_Term x (data_list_term hs)"
  shows "\<exists>h hs'. hs=h#hs' \<and> ((el,Pair_Term x h)\<in>Y \<or> (s,Pair_Term x (data_list_term hs'))\<in>Y)"
proof -
  obtain F where rule: "(c,F)\<in>set (native_some_rules s el)" and S: "S=decode_finite_schema F"
    using clause family by blast
  have cases: "F=native_some_first el \<or> F=native_some_rest s"
    using rule by (auto simp: native_some_rules_def)
  then show ?thesis
  proof
    assume F: "F=native_some_first el"
    have premise: "(el,Pair_Term (f [0]) (f [1]))\<in>Y"
      using native_rule_support[OF support[unfolded S F native_some_first_def]] by simp
    show ?thesis using shape premise by (auto simp: S F native_some_first_def data_list_term_pair)
  next
    assume F: "F=native_some_rest s"
    have premise: "(s,Pair_Term (f [0]) (f [2]))\<in>Y"
      using native_rule_support[OF support[unfolded S F native_some_rest_def]] by simp
    show ?thesis using shape premise by (auto simp: S F native_some_rest_def data_list_term_pair)
  qed
qed

theorem exact:
  "(s,Pair_Term x (data_list_term hs))\<in>positive_meaning P \<longleftrightarrow>
    term_formed x \<and> (\<forall>h\<in>set hs. term_formed h) \<and> (\<exists>h\<in>set hs. (el,Pair_Term x h)\<in>positive_meaning P)"
proof
  assume holds: "(s,Pair_Term x (data_list_term hs))\<in>positive_meaning P"
  have formed: "term_formed x" "\<forall>h\<in>set hs. term_formed h"
    using holds_formed[OF holds] by (simp_all add: data_list_term_formed)
  have "\<exists>h\<in>set hs. (el,Pair_Term x h)\<in>positive_meaning P" using holds
  proof (induction hs)
    case Nil
    obtain c F f where "(c,F)\<in>set (native_some_rules s el)"
      and "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=Pair_Term x (data_list_term [])"
      by (rule holds_cases[OF Nil.prems]) blast
    then show ?case by (auto simp: native_some_rules_def native_some_first_def native_some_rest_def)
  next
    case (Cons h hs)
    obtain c F f where rule: "(c,F)\<in>set (native_some_rules s el)"
      and shape: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=Pair_Term x (data_list_term (h#hs))"
      and support: "\<forall>k d p. (k,d,p)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning P"
      by (rule holds_cases[OF Cons.prems]) blast
    have "\<exists>h' hs'. h#hs=h'#hs' \<and> ((el,Pair_Term x h')\<in>positive_meaning P \<or>
        (s,Pair_Term x (data_list_term hs'))\<in>positive_meaning P)"
      by (rule unfold[OF rule_clause[OF rule] support shape])
    then show ?case using Cons.IH by auto
  qed
  then show "term_formed x \<and> (\<forall>h\<in>set hs. term_formed h) \<and> (\<exists>h\<in>set hs. (el,Pair_Term x h)\<in>positive_meaning P)"
    using formed by blast
next
  assume "term_formed x \<and> (\<forall>h\<in>set hs. term_formed h) \<and> (\<exists>h\<in>set hs. (el,Pair_Term x h)\<in>positive_meaning P)"
  then show "(s,Pair_Term x (data_list_term hs))\<in>positive_meaning P"
  proof (induction hs)
    case Nil
    then show ?case by simp
  next
    case (Cons h hs)
    have xf: "term_formed x" and hf: "term_formed h" and rest: "\<forall>g\<in>set hs. term_formed g"
      using Cons.prems by auto
    have wf: "term_formed (data_list_term hs)" using rest by (simp add: data_list_term_formed)
    show ?case
    proof (cases "(el,Pair_Term x h)\<in>positive_meaning P")
      case True
      have "(s,evaluate_pattern (native_values [x,h,data_list_term hs])
          (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2)))))
          \<in>positive_meaning P"
        by (rule native_step[where c="[0]" and ps="[([0],(el,Finite_Pattern_Pair (native_var 0) (native_var 1)))]"])
          (use True xf hf wf in \<open>simp_all add: native_some_rules_def native_some_first_def\<close>)
      then show ?thesis by simp
    next
      case False
      have inner: "(s,Pair_Term x (data_list_term hs))\<in>positive_meaning P"
        using Cons False by auto
      have "(s,evaluate_pattern (native_values [x,h,data_list_term hs])
          (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2)))))
          \<in>positive_meaning P"
        by (rule native_step[where c="[1]" and ps="[([0],(s,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"])
          (use inner xf hf wf in \<open>simp_all add: native_some_rules_def native_some_rest_def\<close>)
      then show ?thesis by simp
    qed
  qed
qed

end

section \<open>The value a keyed table holds for a key, checked in a context\<close>

definition native_found_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_found_rule ch=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1)
      (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 1) (native_var 2)) (native_var 3))))
    [([0],(ch,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"

definition native_skip_rule :: "'u definition_site \<Rightarrow>
    (local_address,local_address,'u definition_site) finite_factor_schema" where
  "native_skip_rule k=finite_native_rule
    (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1)
      (Finite_Pattern_Pair (native_var 2) (native_var 3))))
    [([0],(k,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 3))))]"

definition native_keyed_search_rules :: "'u definition_site \<Rightarrow> 'u definition_site \<Rightarrow>
    (local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list" where
  "native_keyed_search_rules k ch=[([0],native_found_rule ch),([1],native_skip_rule k)]"

locale native_keyed_search_program = native_rule_family P k "native_keyed_search_rules k ch"
  for P :: "'u native_system" and k ch :: "'u definition_site"
begin

lemma unfold:
  assumes clause: "((k,c),S)\<in>system_clauses P"
    and support: "\<forall>s d p. (s,d,p)\<in>schema_premises S \<longrightarrow> (d,evaluate_pattern f p)\<in>Y"
    and shape: "evaluate_pattern f (schema_conclusion S)=
      Pair_Term x (Pair_Term key (data_list_term (map (case_prod Pair_Term) rows)))"
  shows "\<exists>a v rows'. rows=(a,v)#rows' \<and> ((a=key \<and> (ch,Pair_Term x v)\<in>Y) \<or>
    (k,Pair_Term x (Pair_Term key (data_list_term (map (case_prod Pair_Term) rows'))))\<in>Y)"
proof -
  obtain F where rule: "(c,F)\<in>set (native_keyed_search_rules k ch)" and S: "S=decode_finite_schema F"
    using clause family by blast
  have cases: "F=native_found_rule ch \<or> F=native_skip_rule k"
    using rule by (auto simp: native_keyed_search_rules_def)
  then show ?thesis
  proof
    assume F: "F=native_found_rule ch"
    have premise: "(ch,Pair_Term (f [0]) (f [2]))\<in>Y"
      using native_rule_support[OF support[unfolded S F native_found_rule_def]] by simp
    show ?thesis using shape premise by (auto simp: S F native_found_rule_def data_rows_pair)
  next
    assume F: "F=native_skip_rule k"
    have premise: "(k,Pair_Term (f [0]) (Pair_Term (f [1]) (f [3])))\<in>Y"
      using native_rule_support[OF support[unfolded S F native_skip_rule_def]] by simp
    show ?thesis using shape premise by (auto simp: S F native_skip_rule_def data_rows_pair)
  qed
qed

theorem exact:
  "(k,Pair_Term x (Pair_Term key (data_list_term (map (case_prod Pair_Term) rows))))\<in>positive_meaning P \<longleftrightarrow>
    term_formed x \<and> term_formed key \<and> (\<forall>(a,v)\<in>set rows. term_formed a \<and> term_formed v) \<and>
    (\<exists>v. (key,v)\<in>set rows \<and> (ch,Pair_Term x v)\<in>positive_meaning P)"
proof
  assume holds: "(k,Pair_Term x (Pair_Term key (data_list_term (map (case_prod Pair_Term) rows))))\<in>positive_meaning P"
  have formed: "term_formed x" "term_formed key" "\<forall>(a,v)\<in>set rows. term_formed a \<and> term_formed v"
    using holds_formed[OF holds] by (simp_all add: data_rows_formed)
  have "\<exists>v. (key,v)\<in>set rows \<and> (ch,Pair_Term x v)\<in>positive_meaning P" using holds
  proof (induction rows)
    case Nil
    obtain c F f where "(c,F)\<in>set (native_keyed_search_rules k ch)"
      and "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=
        Pair_Term x (Pair_Term key (data_list_term (map (case_prod Pair_Term) [])))"
      by (rule holds_cases[OF Nil.prems]) blast
    then show ?case by (auto simp: native_keyed_search_rules_def native_found_rule_def native_skip_rule_def)
  next
    case (Cons r rows)
    obtain c F f where rule: "(c,F)\<in>set (native_keyed_search_rules k ch)"
      and shape: "evaluate_pattern f (schema_conclusion (decode_finite_schema F))=
        Pair_Term x (Pair_Term key (data_list_term (map (case_prod Pair_Term) (r#rows))))"
      and support: "\<forall>s d p. (s,d,p)\<in>schema_premises (decode_finite_schema F) \<longrightarrow>
        (d,evaluate_pattern f p)\<in>positive_meaning P"
      by (rule holds_cases[OF Cons.prems]) blast
    have "\<exists>a v rows'. r#rows=(a,v)#rows' \<and> ((a=key \<and> (ch,Pair_Term x v)\<in>positive_meaning P) \<or>
        (k,Pair_Term x (Pair_Term key (data_list_term (map (case_prod Pair_Term) rows'))))\<in>positive_meaning P)"
      by (rule unfold[OF rule_clause[OF rule] support shape])
    then show ?case using Cons.IH by auto
  qed
  then show "term_formed x \<and> term_formed key \<and> (\<forall>(a,v)\<in>set rows. term_formed a \<and> term_formed v) \<and>
      (\<exists>v. (key,v)\<in>set rows \<and> (ch,Pair_Term x v)\<in>positive_meaning P)"
    using formed by blast
next
  assume "term_formed x \<and> term_formed key \<and> (\<forall>(a,v)\<in>set rows. term_formed a \<and> term_formed v) \<and>
    (\<exists>v. (key,v)\<in>set rows \<and> (ch,Pair_Term x v)\<in>positive_meaning P)"
  then show "(k,Pair_Term x (Pair_Term key (data_list_term (map (case_prod Pair_Term) rows))))\<in>positive_meaning P"
  proof (induction rows)
    case Nil
    then show ?case by simp
  next
    case (Cons r rows)
    obtain a w where r: "r=(a,w)" by (cases r)
    have xf: "term_formed x" and kf: "term_formed key" and af: "term_formed a" and wf: "term_formed w"
      and rest: "\<forall>(b,v)\<in>set rows. term_formed b \<and> term_formed v"
      using Cons.prems r by auto
    have tf: "term_formed (data_list_term (map (case_prod Pair_Term) rows))"
      using rest by (simp add: data_rows_formed)
    obtain v where found: "(key,v)\<in>set ((a,w)#rows)" and checked: "(ch,Pair_Term x v)\<in>positive_meaning P"
      using Cons.prems r by blast
    show ?case
    proof (cases "(key,v)=(a,w)")
      case True
      have "(k,evaluate_pattern (native_values [x,key,w,data_list_term (map (case_prod Pair_Term) rows)])
          (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1)
            (Finite_Pattern_Pair (Finite_Pattern_Pair (native_var 1) (native_var 2)) (native_var 3))))))
          \<in>positive_meaning P"
        by (rule native_step[where c="[0]" and ps="[([0],(ch,Finite_Pattern_Pair (native_var 0) (native_var 2)))]"])
          (use True checked xf kf wf tf in \<open>simp_all add: native_keyed_search_rules_def native_found_rule_def\<close>)
      then show ?thesis using True r by simp
    next
      case False
      have inner: "(k,Pair_Term x (Pair_Term key (data_list_term (map (case_prod Pair_Term) rows))))\<in>positive_meaning P"
        using Cons.IH found False checked xf kf rest by auto
      have "(k,evaluate_pattern (native_values [x,key,Pair_Term a w,data_list_term (map (case_prod Pair_Term) rows)])
          (decode_finite_pattern (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1)
            (Finite_Pattern_Pair (native_var 2) (native_var 3))))))
          \<in>positive_meaning P"
        by (rule native_step[where c="[1]" and
            ps="[([0],(k,Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 3))))]"])
          (use inner xf kf af wf tf in \<open>simp_all add: native_keyed_search_rules_def native_skip_rule_def\<close>)
      then show ?thesis using r by simp
    qed
  qed
qed

end

section \<open>A program is the families at its sites\<close>

text \<open>
  A native program is presented by its definitions, each a site with its family of rules; every
  interface admits every formed term. The clauses of the program at a site are exactly the rules of
  the family listed there, so a program built from the families above instantiates their contracts at
  its sites.
\<close>

definition finite_rule_program :: "('u definition_site\<times>
    (local_address\<times>(local_address,local_address,'u definition_site) finite_factor_schema) list) list \<Rightarrow>
      'u finite_native_system" where
  "finite_rule_program ds=\<lparr>finite_system_interfaces=fset_of_list (map (\<lambda>(d,rs). (d,native_var 0)) ds),
    finite_system_clauses=fset_of_list (concat (map (\<lambda>(d,rs). map (\<lambda>(c,F). ((d,c),F)) rs) ds))\<rparr>"

lemma finite_rule_program_rows:
  "((d,c),F)\<in>set (concat (map (\<lambda>(d,rs). map (\<lambda>(c,F). ((d,c),F)) rs) ds)) \<longleftrightarrow>
    (\<exists>rs. (d,rs)\<in>set ds \<and> (c,F)\<in>set rs)"
  by (induction ds) auto

lemma finite_rule_program_clause:
  "((d,c),S)\<in>system_clauses (decode_finite_system (finite_rule_program ds)) \<longleftrightarrow>
    (\<exists>rs. (d,rs)\<in>set ds \<and> (\<exists>F. (c,F)\<in>set rs \<and> S=decode_finite_schema F))"
proof -
  have clauses: "system_clauses (decode_finite_system (finite_rule_program ds))=map_relation_values
      decode_finite_schema (set (concat (map (\<lambda>(d,rs). map (\<lambda>(c,F). ((d,c),F)) rs) ds)))"
    by (simp only: decode_finite_system_fields finite_rule_program_def finite_schema_system.select_convs
      fset_of_list.rep_eq)
  show ?thesis by (simp only: clauses map_relation_values_member finite_rule_program_rows) blast
qed

lemma finite_rule_program_interface:
  "(d,p)\<in>system_interfaces (decode_finite_system (finite_rule_program ds)) \<longleftrightarrow>
    d\<in>fst ` set ds \<and> p=Pattern_Variable [0]"
proof -
  have interfaces: "system_interfaces (decode_finite_system (finite_rule_program ds))=
      map_relation_values decode_finite_pattern (set (map (\<lambda>(d,rs). (d,native_var 0)) ds))"
    by (simp only: decode_finite_system_fields finite_rule_program_def finite_schema_system.select_convs
      fset_of_list.rep_eq)
  have listed: "(d,q)\<in>set (map (\<lambda>(d,rs). (d,native_var 0)) ds) \<longleftrightarrow> d\<in>fst ` set ds \<and> q=native_var 0" for q
    by (induction ds) auto
  show ?thesis by (simp only: interfaces map_relation_values_member listed) auto
qed

lemma finite_rule_program_definitions:
  "system_definitions (decode_finite_system (finite_rule_program ds))=fst ` set ds"
  unfolding system_definitions_def rel_dom_def finite_rule_program_interface by auto

lemma finite_rule_program_call:
  assumes formed: "schema_system_formed (decode_finite_system (finite_rule_program ds))"
    and member: "d\<in>fst ` set ds"
  shows "schema_call_formed (decode_finite_system (finite_rule_program ds)) d t \<longleftrightarrow> term_formed t"
  unfolding schema_call_formed_def finite_rule_program_interface using formed member by auto

text \<open>
  A formed rule program whose sites are distinct holds at each site exactly the family listed there, so
  every contract of that family applies to it: the family is stated once here for every rule program.
\<close>

lemma finite_rule_program_family:
  assumes formed: "schema_system_formed (decode_finite_system (finite_rule_program ds))"
    and distinct: "distinct (map fst ds)" and member: "(d,rs)\<in>set ds"
    and plain: "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}"
  shows "native_rule_family (decode_finite_system (finite_rule_program ds)) d rs"
proof (rule native_rule_family.intro)
  show "schema_system_formed (decode_finite_system (finite_rule_program ds))" by (rule formed)
  show "((d,c),S)\<in>system_clauses (decode_finite_system (finite_rule_program ds)) \<longleftrightarrow>
      (\<exists>F. (c,F)\<in>set rs \<and> S=decode_finite_schema F)" for c S
    using finite_rule_program_clause[of d c S ds] eq_key_imp_eq_value[OF distinct member] member by blast
  have site: "d\<in>fst ` set ds" using member by (rule rev_image_eqI) simp
  show "schema_call_formed (decode_finite_system (finite_rule_program ds)) d t \<longleftrightarrow> term_formed t" for t
    by (rule finite_rule_program_call[OF formed site])
  show "\<forall>r\<in>set rs. finite_schema_materials (snd r)={||}" by (rule plain)
qed

end
