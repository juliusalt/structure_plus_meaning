theory Finite_Iteration_Histories
  imports "HOL-Library.While_Combinator"
begin

section \<open>Every recorded state precedes one actual iteration step\<close>

fun iteration_prefix :: "('a\<Rightarrow>bool)\<Rightarrow>('a\<Rightarrow>'a)\<Rightarrow>'a\<Rightarrow>'a list\<Rightarrow>'a\<Rightarrow>bool" where
  "iteration_prefix b f x [] y=(y=x)"
| "iteration_prefix b f x (s#ss) y=(s=x \<and> b x \<and> iteration_prefix b f (f x) ss y)"

lemma iteration_prefix_append:
  "iteration_prefix b f x (xs@ys) y \<longleftrightarrow>
    (\<exists>z. iteration_prefix b f x xs z \<and> iteration_prefix b f z ys y)"
  by (induction xs arbitrary: x) auto

lemma iteration_prefix_result:
  "iteration_prefix b f x xs y \<Longrightarrow> y=(f ^^ length xs) x"
proof (induction xs arbitrary: x)
  case Nil
  then show ?case by simp
next
  case (Cons s ss)
  have tail: "iteration_prefix b f (f x) ss y" using Cons.prems by simp
  have result: "y=(f ^^ length ss) (f x)" by (rule Cons.IH[OF tail])
  show ?case using result by (simp only: length_Cons funpow_Suc_right comp_apply)
qed

lemma iteration_prefix_invariant:
  assumes initial: "I x"
    and step: "\<And>s. I s \<Longrightarrow> b s \<Longrightarrow> I (f s)"
    and path: "iteration_prefix b f x xs y"
  shows "I y \<and> (\<forall>s\<in>set xs. I s)"
  using path initial by (induction xs arbitrary: x) (auto intro: step)

lemma iteration_prefix_map:
  assumes injective: "inj h"
    and guard: "\<And>s. b s=b' (h s)"
    and step: "\<And>s. h (f s)=f' (h s)"
  shows "iteration_prefix b' f' (h x) (map h xs) (h y) \<longleftrightarrow> iteration_prefix b f x xs y"
  by (induction xs arbitrary: x)
    (auto simp: guard[symmetric] step[symmetric] dest: injD[OF injective])

definition iteration_history_step :: "('a\<Rightarrow>'a)\<Rightarrow>('a\<times>'a list)\<Rightarrow>('a\<times>'a list)" where
  "iteration_history_step f=(\<lambda>(s,rs). (f s,s#rs))"

definition while_history where
  "while_history b f x=map_option (\<lambda>(s,rs). (s,rev rs))
    (while_option (\<lambda>p. b (fst p)) (iteration_history_step f) (x,[]))"

lemma while_history_projection:
  "map_option fst (while_history b f x)=while_option b f x"
proof -
  have projected: "map_option fst
      (while_option (\<lambda>p. b (fst p)) (iteration_history_step f) (x,[]))=while_option b f (fst (x,[]))"
    using while_option_commute[where f=fst and b="\<lambda>p. b (fst p)" and
      c="iteration_history_step f" and b'=b and c'=f and s="(x,[])"]
    by (auto simp: iteration_history_step_def split: prod.splits)
  show ?thesis using projected
    by (cases "while_option (\<lambda>p. b (fst p)) (iteration_history_step f) (x,[])")
      (auto simp: while_history_def split: prod.splits)
qed

lemma while_history_terminates:
  "(\<exists>y xs. while_history b f x=Some (y,xs)) \<longleftrightarrow>
    (\<exists>y. while_option b f x=Some y)"
proof -
  have total: "(\<exists>y. while_option b f x=Some y) \<longleftrightarrow>
      (\<exists>p. while_history b f x=Some p)"
    by (subst while_history_projection[symmetric])
      (simp only: map_option_eq_Some; blast)
  show ?thesis using total by (simp only: split_paired_Ex)
qed

theorem while_history_correct:
  assumes result: "while_history b f x=Some (y,xs)"
  shows "iteration_prefix b f x xs y" "\<not>b y"
proof -
  obtain rs where run: "while_option (\<lambda>p. b (fst p)) (iteration_history_step f) (x,[])=Some (y,rs)"
    and fields: "xs=rev rs"
    using result by (auto simp: while_history_def split: option.splits prod.splits)
  have path: "iteration_prefix b f x (rev rs) y"
    using while_option_rule[where P="\<lambda>(s,rs). iteration_prefix b f x (rev rs) s",
      OF _ run]
    by (auto simp: iteration_history_step_def iteration_prefix_append split: prod.splits)
  show "iteration_prefix b f x xs y" by (simp only: fields path)
  show "\<not>b y" using while_option_stop[OF run] by simp
qed

section \<open>Every offered occurrence retains its expected state and progress check\<close>

type_synonym 'a iteration_review = "('a\<times>'a\<times>bool) list\<times>'a\<times>'a\<times>bool"

fun iteration_review ::
    "('a\<Rightarrow>bool)\<Rightarrow>('a\<Rightarrow>'a)\<Rightarrow>'a\<Rightarrow>'a list\<Rightarrow>'a\<Rightarrow>'a iteration_review" where
  "iteration_review b f x [] y=([],x,y,\<not>b y)"
| "iteration_review b f x (s#ss) y=(case iteration_review b f (f s) ss y of
    (rows,expected,actual,stopped) \<Rightarrow> ((x,s,b s)#rows,expected,actual,stopped))"

definition iteration_review_holds where
  "iteration_review_holds R=(case R of (rows,expected,actual,stopped) \<Rightarrow>
    list_all (\<lambda>(x,s,progress). x=s \<and> progress) rows \<and> expected=actual \<and> stopped)"

theorem iteration_review_exact:
  "iteration_review_holds (iteration_review b f x xs y) \<longleftrightarrow>
    iteration_prefix b f x xs y \<and> \<not>b y"
  by (induction xs arbitrary: x) (auto simp: iteration_review_holds_def split_def)

end
