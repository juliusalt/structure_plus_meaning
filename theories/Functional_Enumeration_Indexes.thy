theory Functional_Enumeration_Indexes
imports Carrier_Indexes Finite_Functional_Enumeration
begin

section \<open>A functional relation is indexed by its ordered keys\<close>

text \<open>
  A finite functional relation is the carrier of its own rows; formation is functionality, the one
  condition its contracts are claimed under. Its enumeration @{const finite_functional_rows} orders
  the keys alone, and its optional selection @{const finite_relation_option} returns the one value at a
  key: both are indexes of the relation by the identity key, discharged by
  @{thm [source] finite_functional_rows_exact} and @{thm [source] finite_relation_option_correct}.
  This is the notion's first law as an instance: only the keys are ordered, and no order is imposed on
  the values.
\<close>

lemma functional_rows_carrier_index:
  "carrier_index (\<lambda>R q v. (q,v) |\<in>| R) finite_relation_functional (UNIV::'k::linorder set) id
    finite_functional_rows (\<lambda>rows k v. (k,v)\<in>set rows)"
proof (rule carrier_index.intro)
  show "inj_on id (UNIV::'k set)" by simp
  fix R :: "('k\<times>'v) fset" and k v
  assume functional: "finite_relation_functional R"
  show "(k,v)\<in>set (finite_functional_rows R) \<longleftrightarrow> (\<exists>q\<in>UNIV. id q=k \<and> (q,v) |\<in>| R)"
    by (simp add: finite_functional_rows_exact[OF functional])
qed

interpretation functional_rows_index:
  carrier_index "\<lambda>R q v. (q,v) |\<in>| R" finite_relation_functional "UNIV::'k::linorder set" id
    finite_functional_rows "\<lambda>rows k v. (k,v)\<in>set rows"
  by (rule functional_rows_carrier_index)

lemma functional_option_carrier_index:
  "carrier_index (\<lambda>R q v. (q,v) |\<in>| R) finite_relation_functional UNIV id
    finite_relation_option (\<lambda>f k v. f k=Some v)"
proof (rule carrier_index.intro)
  show "inj_on id UNIV" by simp
  fix R :: "('k\<times>'v) fset" and k v
  assume functional: "finite_relation_functional R"
  show "finite_relation_option R k=Some v \<longleftrightarrow> (\<exists>q\<in>UNIV. id q=k \<and> (q,v) |\<in>| R)"
    by (simp add: finite_relation_option_correct[OF functional])
qed

interpretation functional_option_index:
  carrier_index "\<lambda>R q v. (q,v) |\<in>| R" finite_relation_functional UNIV id
    finite_relation_option "\<lambda>f k v. f k=Some v"
  by (rule functional_option_carrier_index)

end
