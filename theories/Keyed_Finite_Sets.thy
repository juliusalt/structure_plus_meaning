theory Keyed_Finite_Sets
  imports Finite_Sorted_Set_Execution Ordered_Member_Trees
begin

section \<open>A finite set is listed and indexed through an ordered key with a left inverse\<close>

text \<open>
  A finite set whose members have an ordered key is listed in the order of the keys, and a key
  with a left inverse recovers the members from that listing. Listing, union, equality and
  membership then cost a sort or a lookup instead of a comparison of every member with every
  other; every operation below returns the original set, the original union or the original
  truth value.
\<close>

definition keyed_rows :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> 'a fset \<Rightarrow> 'a list" where
  "keyed_rows key unkey A=map unkey (sorted_list_of_fset (fimage key A))"

lemma keyed_rows_set:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "set (keyed_rows key unkey A)=fset A"
proof -
  have "set (keyed_rows key unkey A)=unkey ` key ` fset A"
    by (simp add: keyed_rows_def image_image)
  also have "\<dots>=fset A" by (simp add: image_image inverse)
  finally show ?thesis .
qed

lemma keyed_rows_fset:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "fset_of_list (keyed_rows key unkey A)=A"
  by (rule fset_eqI) (simp add: fset_of_list_elem keyed_rows_set[OF inverse])

definition keyed_set :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> 'a list \<Rightarrow> 'a fset" where
  "keyed_set key unkey xs=fset_of_list (map unkey (sorted_list_of_set (set (map key xs))))"

lemma keyed_set_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_set key unkey xs=fset_of_list xs"
proof -
  have sorted: "set (sorted_list_of_set (key ` set xs))=key ` set xs" by simp
  have "set (map unkey (sorted_list_of_set (set (map key xs))))=set xs"
    by (simp only: set_map sorted image_image inverse image_ident)
  then show ?thesis
    by (simp only: keyed_set_def) (rule fset_eqI, simp only: fset_of_list_elem)
qed

text \<open>
  The set of a listing is formed with its duplicates removed after one sort, so later
  operations meet each member once.
\<close>

definition keyed_union :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> 'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "keyed_union key unkey A B=keyed_set key unkey (keyed_rows key unkey A@keyed_rows key unkey B)"

lemma keyed_union_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_union key unkey A B=A |\<union>| B"
  by (rule fset_eqI) (simp add: keyed_union_def keyed_set_exact[OF inverse] fset_of_list_elem
    keyed_rows_set[OF inverse])

definition keyed_equal :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a fset \<Rightarrow> 'a fset \<Rightarrow> bool" where
  "keyed_equal key A B \<longleftrightarrow> sorted_list_of_fset (fimage key A)=sorted_list_of_fset (fimage key B)"

lemma keyed_equal_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_equal key A B \<longleftrightarrow> A=B"
proof
  assume "keyed_equal key A B"
  then have "map unkey (sorted_list_of_fset (fimage key A))=map unkey (sorted_list_of_fset (fimage key B))"
    by (simp add: keyed_equal_def)
  then have "fset_of_list (keyed_rows key unkey A)=fset_of_list (keyed_rows key unkey B)"
    by (simp add: keyed_rows_def)
  then show "A=B" by (simp only: keyed_rows_fset[OF inverse])
qed (simp add: keyed_equal_def)

text \<open>
  Membership in a keyed set is asked of the ordered index of its keys. The key must
  determine the member; the left inverse is the witness of that.
\<close>

lemma keyed_member_lookup:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "RBT.lookup (ordered_member_tree (fimage key A)) (key x)\<noteq>None \<longleftrightarrow> x |\<in>| A"
proof -
  have injective: "inj key" by (rule inj_on_inverseI[of _ unkey]) (rule inverse)
  have "RBT.lookup (ordered_member_tree (fimage key A)) (key x)\<noteq>None \<longleftrightarrow> key x\<in>key ` fset A"
    by (simp only: ordered_member_tree_exact fimage.rep_eq)
  also have "\<dots>\<longleftrightarrow> x |\<in>| A" by (simp add: inj_image_mem_iff[OF injective])
  finally show ?thesis .
qed

lemma keyed_members_subset:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "fBall B (\<lambda>q. RBT.lookup (ordered_member_tree (fimage key A)) (key q)\<noteq>None) \<longleftrightarrow> B |\<subseteq>| A"
proof
  assume all: "fBall B (\<lambda>q. RBT.lookup (ordered_member_tree (fimage key A)) (key q)\<noteq>None)"
  show "B |\<subseteq>| A"
  proof (rule fsubsetI)
    fix x assume "x |\<in>| B"
    then have "RBT.lookup (ordered_member_tree (fimage key A)) (key x)\<noteq>None" by (rule fbspec[OF all])
    then show "x |\<in>| A" by (simp only: keyed_member_lookup[OF inverse])
  qed
next
  assume included: "B |\<subseteq>| A"
  show "fBall B (\<lambda>q. RBT.lookup (ordered_member_tree (fimage key A)) (key q)\<noteq>None)"
  proof (rule fBallI)
    fix x assume "x |\<in>| B"
    then have "x |\<in>| A" by (rule fsubsetD[OF included])
    then show "RBT.lookup (ordered_member_tree (fimage key A)) (key x)\<noteq>None"
      by (simp only: keyed_member_lookup[OF inverse])
  qed
qed


end
