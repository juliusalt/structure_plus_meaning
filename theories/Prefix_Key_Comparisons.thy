theory Prefix_Key_Comparisons
  imports Linear_Comparisons
begin

section \<open>A structural comparison computes the order of a prefix key\<close>

text \<open>
  This is the notion of DECISIONS.md, "A structural comparison computes a prefix key's order; which
  component it meets first is its view's", checked. A \emph{view} of a type presents each value as a
  \emph{node}: a \emph{head} and a list of \emph{children}, in the order the view meets them. A
  \emph{prefix key} of the view lists a node's head followed by the keys of its children in that order;
  the key is a parameter with its one-level equation, so the theorems speak of each use's own key. A
  \emph{structural comparison} of the view compares the heads and, where they are equal, the children in
  the view's order. The notion fixes no order of the components, which is each use's convention, and
  claims nothing of cost.
\<close>

subsection \<open>The lists of children\<close>

text \<open>
  Two lemmas over the lists of a node's children carry the inductions below: each takes the property of
  every child as a hypothesis and applies it at each child explicitly.
\<close>

lemma listed_key_prefix:
  assumes prefix: "\<And>c u xs ys. c\<in>set cs \<Longrightarrow> key c@xs=key u@ys \<Longrightarrow> c=u \<and> xs=ys"
    and lengths: "length cs=length ds"
    and keys: "concat (map key cs)@xs=concat (map key ds)@ys"
  shows "cs=ds \<and> xs=ys"
  using prefix lengths keys
proof (induction cs arbitrary: ds xs ys)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  from Cons.prems(2) obtain d ds' where ds: "ds=d#ds'" and lengths: "length cs=length ds'"
    by (cases ds) simp_all
  have split: "key c@(concat (map key cs)@xs)=key d@(concat (map key ds')@ys)"
    using Cons.prems(3) by (simp only: ds list.map concat.simps append_assoc)
  note child=Cons.prems(1)[OF list.set_intros(1) split]
  have sub: "\<And>c' u zs ws. c'\<in>set cs \<Longrightarrow> key c'@zs=key u@ws \<Longrightarrow> c'=u \<and> zs=ws"
    by (rule Cons.prems(1)[OF list.set_intros(2)])
  have rest: "cs=ds' \<and> xs=ys" by (rule Cons.IH[OF sub lengths conjunct2[OF child]])
  show ?case using conjunct1[OF child] rest ds by simp
qed

lemma listed_key_compare:
  assumes compare: "\<And>c u xs ys. c\<in>set cs \<Longrightarrow> compare_linear (key c@xs) (key u@ys)=
      (case compare c u of Linear_Equal \<Rightarrow> compare_linear xs ys | r \<Rightarrow> r)"
    and lengths: "length cs=length ds"
  shows "compare_linear (concat (map key cs)@xs) (concat (map key ds)@ys)=
    (case compare_listed compare cs ds of Linear_Equal \<Rightarrow> compare_linear xs ys | r \<Rightarrow> r)"
  using compare lengths
proof (induction cs arbitrary: ds xs ys)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  from Cons.prems(2) obtain d ds' where ds: "ds=d#ds'" and lengths: "length cs=length ds'"
    by (cases ds) simp_all
  have child: "compare_linear (key c@(concat (map key cs)@xs)) (key d@(concat (map key ds')@ys))=
      (case compare c d of Linear_Equal \<Rightarrow> compare_linear (concat (map key cs)@xs) (concat (map key ds')@ys)
        | r \<Rightarrow> r)"
    by (rule Cons.prems(1)[OF list.set_intros(1)])
  have sub: "\<And>c' u zs ws. c'\<in>set cs \<Longrightarrow> compare_linear (key c'@zs) (key u@ws)=
      (case compare c' u of Linear_Equal \<Rightarrow> compare_linear zs ws | r \<Rightarrow> r)"
    by (rule Cons.prems(1)[OF list.set_intros(2)])
  have rest: "compare_linear (concat (map key cs)@xs) (concat (map key ds')@ys)=
      (case compare_listed compare cs ds' of Linear_Equal \<Rightarrow> compare_linear xs ys | r \<Rightarrow> r)"
    by (rule Cons.IH[OF sub lengths])
  show ?case
    by (cases "compare c d")
      (simp_all only: ds list.map concat.simps append_assoc child rest compare_listed.simps
        linear_comparison.case)
qed

subsection \<open>A prefix key is prefix-free\<close>

locale prefix_key =
  fixes head :: "'a \<Rightarrow> 'h" and children :: "'a \<Rightarrow> 'a list" and key :: "'a \<Rightarrow> 'h list"
  assumes key_node: "key t=head t#concat (map key (children t))"
    and head_arity: "head t=head u \<Longrightarrow> length (children t)=length (children u)"
    and node_determined: "head t=head u \<Longrightarrow> children t=children u \<Longrightarrow> t=u"
begin

lemma key_nonempty: "key t\<noteq>[]"
  by (simp only: key_node list.distinct(2) not_False_eq_True)

lemma child_key_shorter:
  assumes child: "c\<in>set (children t)"
  shows "length (key c)<length (key t)"
proof -
  obtain p q where split: "children t=p@c#q" using child by (meson split_list)
  show ?thesis by (simp add: key_node[of t] split)
qed

theorem key_prefix: "key t@xs=key u@ys \<Longrightarrow> t=u \<and> xs=ys"
proof (induction "length (key t)" arbitrary: t u xs ys rule: less_induct)
  case less
  have node: "head t#(concat (map key (children t))@xs)=head u#(concat (map key (children u))@ys)"
    using less.prems by (simp only: key_node append_Cons)
  have heads: "head t=head u" and rest: "concat (map key (children t))@xs=concat (map key (children u))@ys"
    using node by simp_all
  have prefix: "\<And>c v zs ws. c\<in>set (children t) \<Longrightarrow> key c@zs=key v@ws \<Longrightarrow> c=v \<and> zs=ws"
    by (rule less.hyps[OF child_key_shorter])
  have listed: "children t=children u \<and> xs=ys"
    by (rule listed_key_prefix[where key=key, OF prefix head_arity[OF heads] rest])
  have "t=u" by (rule node_determined[OF heads conjunct1[OF listed]])
  then show ?case using conjunct2[OF listed] by (rule conjI)
qed

corollary key_injective: "key t=key u \<longleftrightarrow> t=u"
  using key_prefix[of t "[]" u "[]"] by auto

end

subsection \<open>A structural comparison returns the key's order\<close>

locale prefix_key_comparison = prefix_key head children key
  for head :: "'a \<Rightarrow> 'h::linorder" and children :: "'a \<Rightarrow> 'a list" and key :: "'a \<Rightarrow> 'h list" +
  fixes compare :: "'a \<Rightarrow> 'a \<Rightarrow> linear_comparison"
  assumes compare_node: "compare t u=(case compare_linear (head t) (head u) of
      Linear_Equal \<Rightarrow> compare_listed compare (children t) (children u) | c \<Rightarrow> c)"
begin

theorem compare_keys: "compare_linear (key t@xs) (key u@ys)=
    (case compare t u of Linear_Equal \<Rightarrow> compare_linear xs ys | c \<Rightarrow> c)"
proof (induction "length (key t)" arbitrary: t u xs ys rule: less_induct)
  case less
  have children: "\<And>c v zs ws. c\<in>set (children t) \<Longrightarrow> compare_linear (key c@zs) (key v@ws)=
      (case compare c v of Linear_Equal \<Rightarrow> compare_linear zs ws | r \<Rightarrow> r)"
    by (rule less.hyps[OF child_key_shorter])
  show ?case
  proof (cases "compare_linear (head t) (head u)")
    case Linear_Equal
    note equal=this
    have heads: "head t=head u" using equal by (simp only: compare_linear_cases(2))
    have listed: "compare_linear (concat (map key (children t))@xs) (concat (map key (children u))@ys)=
        (case compare_listed compare (children t) (children u) of Linear_Equal \<Rightarrow> compare_linear xs ys
          | r \<Rightarrow> r)"
      by (rule listed_key_compare[where key=key and compare=compare, OF children head_arity[OF heads]])
    show ?thesis
      by (simp only: key_node append_Cons compare_linear_prefix compare_node equal linear_comparison.case
        listed)
  qed (simp_all only: key_node append_Cons compare_linear_prefix compare_node linear_comparison.case)
qed

corollary compare_order: "compare t u=compare_linear (key t) (key u)"
  using compare_keys[of t "[]" u "[]"]
  by (cases "compare t u") (simp_all only: append_Nil2 compare_linear_ends(1) linear_comparison.case)

corollary compare_equal: "compare t u=Linear_Equal \<longleftrightarrow> t=u"
  by (simp only: compare_order compare_linear_cases(2) key_injective)

corollary key_less_eq: "key t\<le>key u \<longleftrightarrow> compare t u\<noteq>Linear_Greater"
  by (simp only: compare_order compare_linear_order(1))

corollary key_less: "key t<key u \<longleftrightarrow> compare t u=Linear_Less"
  by (simp only: compare_order compare_linear_order(2))

end

text \<open>
  \<open>compare_keys\<close> is the argument: two keys continued by anything compare as their values do, and
  the continuations matter only where the values are equal, so a comparison reads nothing past the first
  differing child. Its corollaries at empty continuations give the key's order, equality and the code
  equations of an order defined through the key. A use interprets both locales at its view and proves
  only the one-level equations of that view, by cases.
\<close>

end
