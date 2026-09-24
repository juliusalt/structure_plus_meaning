theory RRA_Finite_Fresh_Addresses
  imports RRA_Finite_Artifacts
begin

section \<open>Executable fresh addresses use the actual finite reserved boundary\<close>

text \<open>
  One pass reads the index each reserved address starts with; the fresh address is the code of the
  least index not read. The search stops at the first index not read, and the successor of the
  greatest index read bounds it.
\<close>

definition finite_read_indices :: "local_address fset \<Rightarrow> nat fset" where
  "finite_read_indices U=fimage (fst \<circ> the) (ffilter (\<lambda>r. r\<noteq>None) (fimage read_index_address U))"

lemma finite_read_indices_exact:
  "fset (finite_read_indices U)=index_blocked (fset U)"
proof
  show "fset (finite_read_indices U)\<subseteq>index_blocked (fset U)"
  proof
    fix j assume "j\<in>fset (finite_read_indices U)"
    then obtain a where a: "a\<in>fset U" "read_index_address a\<noteq>None" "j=fst (the (read_index_address a))"
      by (auto simp: finite_read_indices_def fimage.rep_eq ffilter.rep_eq)
    then obtain b where "read_index_address a=Some (j,b)" by (cases "read_index_address a") auto
    then show "j\<in>index_blocked (fset U)" using a(1) by (auto simp: index_blocked_read)
  qed
  show "index_blocked (fset U)\<subseteq>fset (finite_read_indices U)"
  proof
    fix j assume "j\<in>index_blocked (fset U)"
    then obtain a b where a: "a\<in>fset U" "read_index_address a=Some (j,b)" by (auto simp: index_blocked_read)
    have "read_index_address a |\<in>| fimage read_index_address U" using a(1) by (rule fimageI)
    then have "Some (j,b) |\<in>| ffilter (\<lambda>r. r\<noteq>None) (fimage read_index_address U)"
      using a(2) by (simp add: ffilter.rep_eq)
    then have "(fst \<circ> the) (Some (j,b)) |\<in>| finite_read_indices U"
      unfolding finite_read_indices_def by (rule fimageI)
    then show "j\<in>fset (finite_read_indices U)" by simp
  qed
qed

fun least_absent_from :: "(nat \<Rightarrow> bool) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "least_absent_from P 0 j=j"
| "least_absent_from P (Suc n) j=(if P j then least_absent_from P n (Suc j) else j)"

lemma least_absent_from_least:
  assumes "\<not> P (j+n)"
  shows "least_absent_from P n j=(LEAST k. j\<le>k \<and> \<not> P k)"
  using assms
proof (induction n arbitrary: j)
  case 0
  then have absent: "\<not> P j" by simp
  have "(LEAST k. j\<le>k \<and> \<not> P k)=j" by (rule Least_equality) (use absent in auto)
  then show ?case by simp
next
  case (Suc n)
  show ?case
  proof (cases "P j")
    case True
    have same: "(LEAST k. j\<le>k \<and> \<not> P k)=(LEAST k. Suc j\<le>k \<and> \<not> P k)"
    proof (rule arg_cong[where f=Least], rule ext)
      fix k show "(j\<le>k \<and> \<not> P k)=(Suc j\<le>k \<and> \<not> P k)" using True by (cases "k=j") auto
    qed
    have "least_absent_from P n (Suc j)=(LEAST k. Suc j\<le>k \<and> \<not> P k)"
      by (rule Suc.IH) (use Suc.prems in simp)
    then show ?thesis using True same by simp
  next
    case False
    have "(LEAST k. j\<le>k \<and> \<not> P k)=j" by (rule Least_equality) (use False in auto)
    then show ?thesis using False by simp
  qed
qed

definition finite_fresh_address :: "local_address fset \<Rightarrow> local_address" where
  "finite_fresh_address U=(let R=finite_read_indices U in
    index_address (least_absent_from (\<lambda>j. j |\<in>| R) (Suc (fMax (finsert 0 R))) 0))"

lemma finite_fresh_address_exact:
  "finite_fresh_address U=fresh_address (insert [] (fset U))"
proof -
  let ?R="finite_read_indices U"
  have outside: "\<not> Suc (fMax (finsert 0 ?R)) |\<in>| ?R"
  proof
    assume member: "Suc (fMax (finsert 0 ?R)) |\<in>| ?R"
    have "Suc (fMax (finsert 0 ?R))\<le>Max (fset (finsert 0 ?R))"
      by (rule Max_ge) (use member in simp_all)
    then show False by (simp add: fMax.F.rep_eq)
  qed
  have least: "least_absent_from (\<lambda>j. j |\<in>| ?R) (Suc (fMax (finsert 0 ?R))) 0=
      (LEAST k. 0\<le>k \<and> \<not> k |\<in>| ?R)"
    by (rule least_absent_from_least) (use outside in simp)
  show ?thesis unfolding finite_fresh_address_def Let_def least fresh_address_def
    by (simp only: finite_read_indices_exact index_blocked_insert_empty le0 simp_thms)
qed

fun finite_fresh_addresses :: "local_address fset \<Rightarrow> nat \<Rightarrow> local_address list" where
  "finite_fresh_addresses U 0=[]"
| "finite_fresh_addresses U (Suc n)=finite_fresh_address U # finite_fresh_addresses (finsert (finite_fresh_address U) U) n"

lemma finite_fresh_addresses_exact:
  "finite_fresh_addresses U n=fresh_addresses (insert [] (fset U)) n"
  by (induction n arbitrary: U) (simp_all add: finite_fresh_address_exact insert_commute)

lemma finite_fresh_addresses_properties:
  "length (finite_fresh_addresses U n)=n"
  "distinct (finite_fresh_addresses U n)"
  "set (finite_fresh_addresses U n)\<inter>fset U={}"
  "\<forall>a\<in>set (finite_fresh_addresses U n). octets_formed a"
  using fresh_addresses_disjoint[of "insert [] (fset U)" n]
    fresh_addresses_formed[of "insert [] (fset U)" n]
  by (auto simp: finite_fresh_addresses_exact)

definition finite_four_addresses :: "local_address fset \<Rightarrow>
    local_address\<times>local_address\<times>local_address\<times>local_address" where
  "finite_four_addresses U=(let xs=finite_fresh_addresses U 4 in (xs!0,xs!1,xs!2,xs!3))"

lemma finite_four_addresses_properties:
  assumes result: "finite_four_addresses U=(b,r,p,q)"
  shows "distinct [b,r,p,q]" "{b,r,p,q}\<inter>fset U={}"
    "\<forall>a\<in>{b,r,p,q}. octets_formed a"
proof -
  obtain w x y z where list: "finite_fresh_addresses U 4=[w,x,y,z]"
    using finite_fresh_addresses_properties(1)[of U 4]
    by (auto simp: numeral_eq_Suc length_Suc_conv)
  have same: "b=w" "r=x" "p=y" "q=z"
    using result by (simp_all add: finite_four_addresses_def list)
  show "distinct [b,r,p,q]" "{b,r,p,q}\<inter>fset U={}"
    "\<forall>a\<in>{b,r,p,q}. octets_formed a"
    using finite_fresh_addresses_properties(2-4)[of U 4] by (simp_all add: list same)
qed

text \<open>
  The existing fresh-address operation supplies the exact construction and
  its separation proof. The finite boundary additionally reserves the empty
  root, which blocks no index, so the executable address is the abstract one of
  the reserved set with or without it. No choice operator or ambient allocator
  supplies a result.
\<close>

end
