theory Keyed_Fibre_Identity
  imports Factor_Key_Fibres
begin

section \<open>Two complete singleton families determine exactly one functional table\<close>

lemma own_key_fibres_singleton:
  "(\<forall>k v. (k,v)\<in>set xs \<longrightarrow> key_values k xs=[v]) \<longleftrightarrow> distinct (map fst xs)"
proof
  assume fibres: "\<forall>k v. (k,v)\<in>set xs \<longrightarrow> key_values k xs=[v]"
  show "distinct (map fst xs)"
    using fibres
  proof (induction xs)
    case Nil
    then show ?case by simp
  next
    case (Cons row xs)
    obtain k v where row: "row=(k,v)" by (cases row)
    have tail_empty: "key_values k xs=[]" using Cons.prems by (simp add: row)
    have absent: "k\<notin>fst ` set xs" using key_values_set[of k xs] tail_empty by auto
    have tail: "\<forall>j w. (j,w)\<in>set xs \<longrightarrow> key_values j xs=[w]"
    proof (intro allI impI)
      fix j w assume member: "(j,w)\<in>set xs"
      have key: "j\<in>fst ` set xs" using imageI[OF member, of fst] by simp
      have different: "k\<noteq>j" using absent key by blast
      have complete: "key_values j (row#xs)=[w]"
        by (rule Cons.prems[rule_format]) (use member in simp)
      show "key_values j xs=[w]" using complete different by (simp add: row)
    qed
    show ?case using Cons.IH[OF tail] absent by (simp add: row)
  qed
next
  assume keys: "distinct (map fst xs)"
  show "\<forall>k v. (k,v)\<in>set xs \<longrightarrow> key_values k xs=[v]"
  proof (intro allI impI)
    fix k v assume member: "(k,v)\<in>set xs"
    show "key_values k xs=[v]"
      using member by (simp only: Factor_Key_Fibres.key_values_singleton[OF keys])
  qed
qed

lemma singleton_fibres_include:
  assumes fibres: "\<forall>k v. (k,v)\<in>set xs \<longrightarrow> key_values k ys=[v]"
  shows "set xs\<subseteq>set ys"
proof
  fix z assume member: "z\<in>set xs"
  obtain k v where shape: "z=(k,v)" by (cases z)
  have row_member: "(k,v)\<in>set xs" using member by (simp only: shape)
  have fibre: "key_values k ys=[v]" by (rule fibres[rule_format, OF row_member])
  have member_value: "v\<in>set (key_values k ys)" by (simp only: fibre) simp
  show "z\<in>set ys" using member_value by (simp only: key_values_set mem_Collect_eq shape)
qed

lemma mutual_key_fibres:
  "((\<forall>k v. (k,v)\<in>set xs \<longrightarrow> key_values k ys=[v]) \<and>
    (\<forall>k v. (k,v)\<in>set ys \<longrightarrow> key_values k xs=[v])) \<longleftrightarrow>
    distinct (map fst xs) \<and> distinct (map fst ys) \<and> set xs=set ys"
proof
  assume both: "(\<forall>k v. (k,v)\<in>set xs \<longrightarrow> key_values k ys=[v]) \<and>
    (\<forall>k v. (k,v)\<in>set ys \<longrightarrow> key_values k xs=[v])"
  have same: "set xs=set ys"
    using singleton_fibres_include[OF conjunct1[OF both]]
      singleton_fibres_include[OF conjunct2[OF both]] by blast
  have self: "\<forall>k v. (k,v)\<in>set xs \<longrightarrow> key_values k xs=[v]"
    "\<forall>k v. (k,v)\<in>set ys \<longrightarrow> key_values k ys=[v]"
    using both same by blast+
  have first_keys: "distinct (map fst xs)"
    by (rule iffD1[OF own_key_fibres_singleton self(1)])
  have second_keys: "distinct (map fst ys)"
    by (rule iffD1[OF own_key_fibres_singleton self(2)])
  show "distinct (map fst xs) \<and> distinct (map fst ys) \<and> set xs=set ys"
    using first_keys second_keys same by blast
next
  assume fields: "distinct (map fst xs) \<and> distinct (map fst ys) \<and> set xs=set ys"
  have first: "distinct (map fst xs)" and second: "distinct (map fst ys)" and same: "set xs=set ys"
    using fields by blast+
  show "(\<forall>k v. (k,v)\<in>set xs \<longrightarrow> key_values k ys=[v]) \<and>
    (\<forall>k v. (k,v)\<in>set ys \<longrightarrow> key_values k xs=[v])"
    by (simp only: Factor_Key_Fibres.key_values_singleton[OF first]
      Factor_Key_Fibres.key_values_singleton[OF second] same) blast
qed

end
