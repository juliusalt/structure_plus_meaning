theory Established_Premises
imports "HOL-Library.FSet"
begin

section \<open>A check is made where its premise is established\<close>

text \<open>
  This is the notion stated in DECISIONS.md, "The in-place refinements apply two notions: a check made
  where its premise is established, and a generator of the accepted candidates", checked. A traversal
  checks a condition of what it reads at every step it makes. A premise established at one point implies
  the condition at every step after it; under the premise a body that makes no such check computes the
  operation, and the check is made once, where the premise is established, and nowhere inside.

  The premise is established at one of three places: at the operation's entry, by checking it, the other
  branch returning the operation's own value outside the premise, its refusal; at an enclosing operation
  whose established premise implies it; or by the contract of the constructor that made the value. The
  locale @{text established_premise} states obligation (1), exactness, which a use proves, for a
  recursive traversal by its own induction. At the second and third places a use gets exactness at the
  established value, with its establishing fact stated once where it is about, never at a use. At the
  entry the extension @{text checked_premise} adds obligation (2), the refusal, and a use gets the code
  equation @{text checked_at_entry}, the check hoisted through any consumer (@{text checked_through})
  and through a union over a family (@{text checked_union}).

  The arguments @{text x} are exactly the premise's arguments, those after it lying inside the value:
  the code equation is stated at the arity where the premise's arguments end, so a partial application
  checks once however often it is then applied. A premise on an argument that is not the first is
  instantiated with the constant applied to the arguments before it. No attribute is declared here and
  nothing is stated about cost: which check is hoisted, and what it saves, are observations of a use.
\<close>

locale established_premise =
  fixes original :: "'a \<Rightarrow> 'b" and premise :: "'a \<Rightarrow> bool" and body :: "'a \<Rightarrow> 'b"
  assumes exact: "premise x \<Longrightarrow> original x = body x"

locale checked_premise = established_premise original premise body
  for original :: "'a \<Rightarrow> 'b" and premise :: "'a \<Rightarrow> bool" and body :: "'a \<Rightarrow> 'b" +
  fixes refusal :: "'a \<Rightarrow> 'b"
  assumes refused: "\<not> premise x \<Longrightarrow> original x = refusal x"
begin

theorem checked_at_entry: "original x = (if premise x then body x else refusal x)"
  by (cases "premise x") (simp_all add: exact refused)

theorem checked_through: "t (original x) = (if premise x then t (body x) else t (refusal x))"
  by (cases "premise x") (simp_all add: exact refused)

end

text \<open>
  The check hoisted out of a union over a family: a family whose every member is refused by the empty
  set when the premise fails unites to the empty set, and to the union of its bodies when it holds.
\<close>

theorem checked_union:
  "ffUnion (fimage (\<lambda>y. if P then T y else {||}) Y) = (if P then ffUnion (fimage T Y) else {||})"
proof (cases P)
  case True
  then show ?thesis by simp
next
  case False
  have "ffUnion (fimage (\<lambda>y. {||}) Y) = {||}"
    unfolding fset_eq_iff by (simp add: ffUnion.rep_eq fimage.rep_eq)
  with False show ?thesis by simp
qed

end
