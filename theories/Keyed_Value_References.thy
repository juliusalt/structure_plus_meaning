theory Keyed_Value_References
  imports Complete_Value_References "HOL-Library.RBT" Linear_Comparisons
begin

section \<open>First-occurrence references are found through an injective ordered key\<close>

fun keyed_reference_run ::
  "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a list \<Rightarrow> ('k,nat) rbt \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'k list \<Rightarrow> nat list \<times> 'k list" where
  "keyed_reference_run key [] M n js ks=(rev js,rev ks)"
| "keyed_reference_run key (x#xs) M n js ks=(case RBT.lookup M (key x) of
      Some i \<Rightarrow> keyed_reference_run key xs M n (i#js) ks
    | None \<Rightarrow> keyed_reference_run key xs (RBT.insert (key x) n M) (Suc n) (n#js) (key x#ks))"

lemma value_reference_index_snoc:
  "value_reference_index y (T@[x])=(case value_reference_index y T of
    None \<Rightarrow> (if y=x then Some (length T) else None) | Some i \<Rightarrow> Some i)"
  by (induction T) (auto split: option.splits)

lemma keyed_reference_run_table:
  assumes key: "inj key"
    and length: "n=length T"
    and keys: "ks=rev (map key T)"
    and index: "\<And>y. RBT.lookup M (key y)=value_reference_index y T"
  shows "keyed_reference_run key xs M n js ks=
    (rev js@fst (value_reference_sequence xs T),map key (snd (value_reference_sequence xs T)))"
  using length keys index
proof (induction xs arbitrary: M n js ks T)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  show ?case
  proof (cases "RBT.lookup M (key x)")
    case (Some i)
    have found: "value_reference_index x T=Some i" using Cons.prems(3)[of x] Some by simp
    have "keyed_reference_run key xs M n (i#js) ks=
        (rev (i#js)@fst (value_reference_sequence xs T),map key (snd (value_reference_sequence xs T)))"
      by (rule Cons.IH[OF Cons.prems])
    then show ?thesis
      by (simp add: Some value_reference_step_def found case_prod_unfold Let_def)
  next
    case None
    have absent: "value_reference_index x T=None" using Cons.prems(3)[of x] None by simp
    have index: "RBT.lookup (RBT.insert (key x) n M) (key y)=value_reference_index y (T@[x])" for y
    proof (cases "y=x")
      case True
      then show ?thesis using absent Cons.prems(1) by (simp add: value_reference_index_snoc)
    next
      case False
      then have "key y\<noteq>key x" using key by (auto dest: injD)
      then show ?thesis
        using False Cons.prems(3)[of y] by (simp add: value_reference_index_snoc split: option.splits)
    qed
    have "keyed_reference_run key xs (RBT.insert (key x) n M) (Suc n) (n#js) (key x#ks)=
        (rev (n#js)@fst (value_reference_sequence xs (T@[x])),map key (snd (value_reference_sequence xs (T@[x]))))"
      by (rule Cons.IH) (use Cons.prems index in simp_all)
    then show ?thesis
      using Cons.prems(1) by (simp add: None value_reference_step_def absent case_prod_unfold Let_def)
  qed
qed

theorem keyed_reference_run_exact:
  assumes "inj key"
  shows "keyed_reference_run key xs RBT.empty 0 [] []=
    (fst (value_reference_sequence xs []),map key (snd (value_reference_sequence xs [])))"
  using keyed_reference_run_table[OF assms, of 0 "[]" "[]" RBT.empty xs "[]"] by simp

section \<open>Precomputed keys are searched by one comparison per tree node\<close>

lemma keyed_reference_run_keys:
  "keyed_reference_run key xs M n js ks=keyed_reference_run id (map key xs) M n js ks"
  by (induction xs arbitrary: M n js ks) (simp_all split: option.splits)

fun rbt_compared_lookup :: "('k \<Rightarrow> 'k \<Rightarrow> linear_comparison) \<Rightarrow> ('k,'v) RBT_Impl.rbt \<Rightarrow> 'k \<Rightarrow> 'v option" where
  "rbt_compared_lookup c RBT_Impl.Empty k=None"
| "rbt_compared_lookup c (RBT_Impl.Branch b l x y r) k=(case c k x of
    Linear_Less \<Rightarrow> rbt_compared_lookup c l k
  | Linear_Greater \<Rightarrow> rbt_compared_lookup c r k
  | Linear_Equal \<Rightarrow> Some y)"

lemma rbt_compared_lookup_exact:
  assumes same: "\<And>a b. c a b=compare_linear a b"
  shows "rbt_compared_lookup c t k=rbt_lookup t k"
proof (induction t)
  case Empty
  then show ?case by simp
next
  case (Branch b l x y r)
  then show ?case
    by (cases k x rule: linorder_cases) (simp_all add: same compare_linear_def)
qed

fun keyed_reference_compared_run ::
  "('k::linorder \<Rightarrow> 'k \<Rightarrow> linear_comparison) \<Rightarrow> 'k list \<Rightarrow> ('k,nat) rbt \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> 'k list \<Rightarrow>
    nat list \<times> 'k list" where
  "keyed_reference_compared_run c [] M n js ks=(rev js,rev ks)"
| "keyed_reference_compared_run c (k#xs) M n js ks=(case rbt_compared_lookup c (RBT.impl_of M) k of
      Some i \<Rightarrow> keyed_reference_compared_run c xs M n (i#js) ks
    | None \<Rightarrow> keyed_reference_compared_run c xs (RBT.insert k n M) (Suc n) (n#js) (k#ks))"

lemma keyed_reference_compared_run_exact:
  assumes same: "\<And>a b. c a b=compare_linear a b"
  shows "keyed_reference_compared_run c keys M n js ks=keyed_reference_run id keys M n js ks"
  by (induction keys arbitrary: M n js ks)
    (simp_all add: rbt_compared_lookup_exact[OF same] RBT.lookup.rep_eq split: option.splits)

text \<open>An injective key identifies each value, so an ordered tree from keys to
  first indices answers every table search. The run returns exactly the indices
  of the reference sequence and the keys of its complete first-occurrence table,
  including every repeated value. Neither the table order nor any index changes.
  Keys computed beforehand give the same run, and a comparison with three outcomes
  decides each tree node with one comparison, returning exactly the original
  lookup.\<close>

end
