theory RRA_Finite_Fresh_Addresses
  imports RRA_Finite_Artifacts
begin

section \<open>Executable fresh addresses use the actual finite reserved boundary\<close>

definition finite_fresh_address :: "local_address fset \<Rightarrow> local_address" where
  "finite_fresh_address U=unary_address (fMax (finsert 0 (fimage length U)))"

lemma finite_fresh_address_exact:
  "finite_fresh_address U=fresh_address (insert [] (fset U))"
  by (simp add: finite_fresh_address_def fresh_address_def fMax.F.rep_eq fimage.rep_eq)

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

export_code finite_fresh_addresses finite_four_addresses checking SML

text \<open>
  The existing fresh-address operation supplies the exact construction and
  its separation proof. The finite boundary additionally reserves the empty
  root, so its maximum is defined even for an empty input family. No choice
  operator or ambient allocator supplies a result.
\<close>

end
