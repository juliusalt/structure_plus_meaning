theory Lambda_Applications
  imports Lambda_Reduction
begin

section \<open>Application spines and the location of a beta step\<close>

abbreviation lambda_apps :: "lambda_term \<Rightarrow> lambda_term list \<Rightarrow> lambda_term" where
  "lambda_apps p ps \<equiv> foldl Lambda_Application p ps"

lemma lambda_apps_same_tail [iff]: "lambda_apps p ps=lambda_apps q ps \<longleftrightarrow> p=q"
  by (induction ps rule: rev_induct) auto

lemma lambda_variable_eq_apps [iff]:
  "Lambda_Variable n=lambda_apps p ps \<longleftrightarrow> Lambda_Variable n=p \<and> ps=[]"
  by (induction ps arbitrary: p) auto

lemma lambda_abstraction_eq_apps [iff]:
  "Lambda_Abstraction p=lambda_apps q qs \<longleftrightarrow> Lambda_Abstraction p=q \<and> qs=[]"
  by (induction qs rule: rev_induct) auto

lemma lambda_apps_eq_abstraction [iff]:
  "lambda_apps p ps=Lambda_Abstraction q \<longleftrightarrow> p=Lambda_Abstraction q \<and> ps=[]"
  by (induction ps rule: rev_induct) auto

lemma lambda_application_eq_apps:
  "Lambda_Application p q=lambda_apps r rs \<longleftrightarrow>
    (if rs=[] then Lambda_Application p q=r
     else (\<exists>ss. rs=ss@[q] \<and> p=lambda_apps r ss))"
  by (cases rs rule: rev_cases) auto

lemma lambda_abstraction_app_neq_variable_apps [iff]:
  "Lambda_Application (Lambda_Abstraction p) q\<noteq>lambda_apps (Lambda_Variable n) ps"
  by (induction ps arbitrary: p q rule: rev_induct) auto

lemma lambda_apps_last:
  "Lambda_Application (lambda_apps p ps) q=lambda_apps p (ps@[q])"
  by simp

lemma lambda_apps_lift [simp]:
  "lambda_lift (lambda_apps p ps) k=lambda_apps (lambda_lift p k) (map (\<lambda>q. lambda_lift q k) ps)"
  by (induction ps arbitrary: p) simp_all

lemma lambda_apps_substitute [simp]:
  "lambda_substitute (lambda_apps p ps) q k=
    lambda_apps (lambda_substitute p q k) (map (\<lambda>r. lambda_substitute r q k) ps)"
  by (induction ps arbitrary: p) simp_all

inductive lambda_list_beta :: "lambda_term list \<Rightarrow> lambda_term list \<Rightarrow> bool" where
  head: "lambda_beta p q \<Longrightarrow> lambda_list_beta (p#ps) (q#ps)"
| tail: "lambda_list_beta ps qs \<Longrightarrow> lambda_list_beta (p#ps) (p#qs)"

lemma lambda_list_beta_nil_left [simp]: "\<not> lambda_list_beta [] ps"
  by (auto elim: lambda_list_beta.cases)

lemma lambda_list_beta_nil_right [simp]: "\<not> lambda_list_beta ps []"
  by (auto elim: lambda_list_beta.cases)

lemma lambda_list_beta_cons [simp]:
  "lambda_list_beta (p#ps) (q#qs) \<longleftrightarrow>
    (lambda_beta p q \<and> ps=qs) \<or> (p=q \<and> lambda_list_beta ps qs)"
  by (auto elim: lambda_list_beta.cases intro: lambda_list_beta.intros)

lemma lambda_list_beta_append_left:
  assumes "lambda_list_beta ps qs"
  shows "lambda_list_beta (ps@rs) (qs@rs)"
  using assms by (induction rule: lambda_list_beta.induct)
    (auto intro: lambda_list_beta.intros)

lemma lambda_list_beta_append_right:
  assumes "lambda_list_beta ps qs"
  shows "lambda_list_beta (rs@ps) (rs@qs)"
  using assms by (induction rs) (auto intro: lambda_list_beta.intros)

lemma lambda_list_beta_append:
  "(lambda_list_beta ps qs \<and> rs=ss) \<or> (ps=qs \<and> lambda_list_beta rs ss) \<Longrightarrow>
    lambda_list_beta (ps@rs) (qs@ss)"
  by (auto intro: lambda_list_beta_append_left lambda_list_beta_append_right)

lemma lambda_list_beta_snoc:
  assumes "lambda_list_beta (ps@[p]) (qs@[q])"
  shows "(lambda_list_beta ps qs \<and> p=q) \<or> (ps=qs \<and> lambda_beta p q)"
  using assms
proof (induction ps arbitrary: qs)
  case Nil
  then show ?case by (cases qs) auto
next
  case (Cons a ps)
  then show ?case by (cases qs) auto
qed

lemma lambda_apps_beta_cases [elim!]:
  assumes major: "lambda_beta (lambda_apps h ps) q"
    and head: "\<And>h'. lambda_beta h h' \<Longrightarrow> q=lambda_apps h' ps \<Longrightarrow> R"
    and argument: "\<And>ps'. lambda_list_beta ps ps' \<Longrightarrow> q=lambda_apps h ps' \<Longrightarrow> R"
    and contract: "\<And>b a as. h=Lambda_Abstraction b \<Longrightarrow> ps=a#as \<Longrightarrow>
      q=lambda_apps (lambda_substitute b a 0) as \<Longrightarrow> R"
  shows R
proof -
  from major have
    "(\<exists>h'. lambda_beta h h' \<and> q=lambda_apps h' ps) \<or>
     (\<exists>ps'. lambda_list_beta ps ps' \<and> q=lambda_apps h ps') \<or>
     (\<exists>b a as. h=Lambda_Abstraction b \<and> ps=a#as \<and>
       q=lambda_apps (lambda_substitute b a 0) as)"
    apply (induction u=="lambda_apps h ps" q arbitrary: h ps rule: lambda_beta.induct)
       apply (case_tac h)
         apply simp
        apply (simp add: lambda_application_eq_apps)
        apply (split if_split_asm)
         apply simp
         apply blast
        apply simp
       apply (simp add: lambda_application_eq_apps)
       apply (split if_split_asm)
        apply simp
       apply simp
      apply (drule lambda_application_eq_apps[THEN iffD1])
      apply (split if_split_asm)
       apply simp
       apply blast
      apply (force intro!: disjI1[THEN lambda_list_beta_append])
     apply (drule lambda_application_eq_apps[THEN iffD1])
     apply (split if_split_asm)
      apply simp
      apply blast
     apply (clarify, auto 0 3 intro!: exI intro: lambda_list_beta_append)
    done
  with head argument contract show ?thesis by blast
qed

lemma lambda_variable_apps_beta:
  assumes "lambda_beta (lambda_apps (Lambda_Variable n) ps) q"
  shows "\<exists>qs. lambda_list_beta ps qs \<and> q=lambda_apps (Lambda_Variable n) qs"
  using assms by (auto elim: lambda_apps_beta_cases)

lemma lambda_apps_beta [simp]:
  "lambda_beta p q \<Longrightarrow> lambda_beta (lambda_apps p ps) (lambda_apps q ps)"
  by (induction ps rule: rev_induct) auto

lemma lambda_apps_reduces:
  "lambda_reduces p q \<Longrightarrow> lambda_reduces (lambda_apps p ps) (lambda_apps q ps)"
  by (induction ps rule: rev_induct) (auto intro: lambda_reduces_left)

lemma lambda_apps_list_beta:
  assumes "lambda_list_beta ps qs"
  shows "lambda_beta (lambda_apps p ps) (lambda_apps p qs)"
  using assms by (induction arbitrary: p rule: lambda_list_beta.induct) auto

text \<open>
  A spine is ordinary repeated ordered application. The auxiliary list relation
  changes exactly one argument by the existing beta rule. The decomposition
  proof follows Tobias Nipkow's HOL/Proofs/Lambda/ListApplication and ListBeta
  developments (1998), here over this repository's source datatype. These
  lemmas prepare standardization; they add no source computation rule.
\<close>

end
