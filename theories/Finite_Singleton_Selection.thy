theory Finite_Singleton_Selection
  imports "HOL-Library.FSet"
begin

section \<open>A singleton is recognized independently of repeated list encodings\<close>

fun list_singleton_option where
  "list_singleton_option []=None"
| "list_singleton_option (x#xs)=(if list_all (\<lambda>y. y=x) xs then Some x else None)"

lemma list_singleton_option_some:
  "list_singleton_option xs=Some a \<longleftrightarrow> set xs={a}"
  by (cases xs; auto simp: list_all_iff; force)

definition set_singleton_option where
  "set_singleton_option A=(if \<exists>a. A={a} then Some (the_elem A) else None)"

lemma set_singleton_option_some:
  "set_singleton_option A=Some a \<longleftrightarrow> A={a}"
  by (auto simp: set_singleton_option_def split: if_splits)

lemma set_singleton_option_set [code]:
  "set_singleton_option (set xs)=list_singleton_option xs"
  by (metis set_singleton_option_some list_singleton_option_some option.exhaust)

definition finite_singleton_option where
  "finite_singleton_option R=set_singleton_option (fset R)"

lemma finite_singleton_option_some:
  "finite_singleton_option R=Some a \<longleftrightarrow> R={|a|}"
  by (simp add: finite_singleton_option_def set_singleton_option_some fset_inject[symmetric])

lemma finite_singleton_option_singleton [simp]:
  "finite_singleton_option {|a|}=Some a"
  by (simp only: finite_singleton_option_some)

text \<open>
  The executable list comparison checks every supplied value. Repeating the
  same value still presents one set member. Empty and distinct
  value families return None. The equation applies to every list presentation,
  so callers do not depend on a singleton's storage already being deduplicated.
\<close>

end
