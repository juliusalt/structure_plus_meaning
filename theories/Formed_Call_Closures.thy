theory Formed_Call_Closures
  imports Keyed_Native_Evaluation Factor_Constructed_Program_Applications
begin

section \<open>The closure of formed requests reads constructed applications\<close>

text \<open>
  The closure of a demand reads the applications of every call it reaches, and that reading checks the
  call's argument formed (@{thm [source] finite_program_applications_listed}), walking the whole argument
  at every demanded call. A premise call of an application of a formed program is formed
  (\<open>finite_program_call_premise_formed\<close> below), so once the requests are checked formed the
  check is established at every call the traversal reaches: a check made where its premise is established
  (\<open>Established_Premises\<close>). Under that premise the traversal reads the constructed applications
  (@{thm [source] finite_constructed_applications_exact}) and returns the same calls
  (\<open>keyed_call_closure_formed\<close>); the check is made once, on the requests, at the entry of the
  closure: the closure is an instance of the notion's \<open>checked_premise\<close>
  (\<open>native_call_closure_checked_premise\<close>), and its code equation is the notion's
  \<open>checked_at_entry\<close> at that instance (\<open>native_call_closure_code\<close>).
\<close>

text \<open>
  A traversal of demanded sites depends on its reading only at the sites it reaches: when the roots satisfy
  a condition that every successor of a satisfying site satisfies, two readings agreeing on the satisfying
  sites return the same sites.
\<close>

theorem finite_demanded_sites_cong:
  assumes roots: "\<And>d. d |\<in>| roots \<Longrightarrow> Q d"
    and closed: "\<And>d x e. Q d \<Longrightarrow> x |\<in>| read d \<Longrightarrow> e |\<in>| succ x \<Longrightarrow> Q e"
    and agree: "\<And>d. Q d \<Longrightarrow> read d=read' d"
  shows "finite_demanded_sites read succ roots=finite_demanded_sites read' succ roots"
proof -
  let ?b="\<lambda>(S,T). T\<noteq>{||}"
  let ?P="\<lambda>(S::'a fset,T). \<forall>d. d |\<in>| T \<longrightarrow> Q d"
  have commute: "map_option id (while_option ?b (finite_demanded_sites_step read succ) ({||},roots))=
      while_option ?b (finite_demanded_sites_step read' succ) (id ({||},roots))"
  proof (rule while_option_commute_invariant[where P="?P"])
    show "?P (finite_demanded_sites_step read succ s)" if inv: "?P s" and active: "?b s" for s
    proof -
      obtain S T where shape: "s=(S,T)" by (cases s)
      have successor: "Q e" if reached: "e |\<in>| finite_row_successors read succ T" for e
      proof -
        obtain d x where "d |\<in>| T" "x |\<in>| read d" "e |\<in>| succ x"
          using reached by (auto simp: finite_row_successors_member)
        then show "Q e" using inv shape closed by blast
      qed
      show ?thesis using successor by (auto simp: shape finite_demanded_sites_step_def Let_def)
    qed
    show "?b s=?b (id s)" for s by simp
    show "id (finite_demanded_sites_step read succ s)=finite_demanded_sites_step read' succ (id s)"
      if inv: "?P s" and active: "?b s" for s
    proof -
      obtain S T where shape: "s=(S,T)" by (cases s)
      have same: "read d=read' d" if "d |\<in>| T" for d using inv shape that agree by blast
      show ?thesis
        by (simp add: shape finite_demanded_sites_step_def Let_def finite_row_successors_cong[OF same])
    qed
    show "?P ({||},roots)" using roots by simp
  qed
  show ?thesis using commute by (simp add: finite_demanded_sites_def option.map_id)
qed

lemma finite_program_call_premise_formed:
  assumes read: "x |\<in>| finite_program_applications P {|q|}" and premise: "e |\<in>| finite_application_premise_calls x"
  shows "finite_term_formed (snd e)"
proof -
  obtain d c t V H where x: "x=(d,c,t,V,H)" by (cases x) auto
  have admitted: "finite_admitted_schema_instance P d c V t H"
    using read by (simp add: x finite_program_application_member)
  obtain s where member: "(s,fst e,snd e) |\<in>| H"
    using premise by (auto simp: x finite_application_premise_calls_def)
  have "finite_schema_call_formed P (fst e) (snd e)"
    using admitted member by (auto simp: finite_admitted_schema_instance_def)
  then show ?thesis by (simp add: finite_schema_call_formed_def finite_pattern_accepts_def) blast
qed

definition formed_call_closure ::
    "local_address option finite_native_system \<Rightarrow> (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      (local_address option definition_site\<times>finite_factor_term) fset" where
  "formed_call_closure P R=(case keyed_demanded_sites native_call_key native_call_unkey
    (\<lambda>q. finite_constructed_applications P (fst q) (snd q)) finite_application_premise_calls R of None \<Rightarrow> R | Some S \<Rightarrow> S)"

theorem keyed_call_closure_formed:
  assumes system: "finite_system_formed P" and requests: "fBall R (\<lambda>q. finite_term_formed (snd q))"
  shows "keyed_call_closure native_call_key native_call_unkey P R=formed_call_closure P R"
proof -
  let ?Q="\<lambda>q::local_address option definition_site\<times>finite_factor_term. finite_term_formed (snd q)"
  have agree: "finite_program_applications P {|q|}=finite_constructed_applications P (fst q) (snd q)"
    if formed: "?Q q" for q
  proof -
    obtain d t where q: "q=(d,t)" by (cases q)
    show ?thesis using finite_constructed_applications_exact[OF system] formed by (simp add: q)
  qed
  have closed: "?Q e" if "x |\<in>| finite_program_applications P {|d|}" "e |\<in>| finite_application_premise_calls x"
    for d x e
    by (rule finite_program_call_premise_formed[OF that])
  have roots: "?Q d" if "d |\<in>| R" for d using requests that by blast
  have same: "finite_demanded_sites (\<lambda>q. finite_program_applications P {|q|}) finite_application_premise_calls R=
      finite_demanded_sites (\<lambda>q. finite_constructed_applications P (fst q) (snd q)) finite_application_premise_calls R"
    by (rule finite_demanded_sites_cong[where Q="?Q", OF roots closed agree])
  show ?thesis
    by (simp only: keyed_call_closure_def formed_call_closure_def keyed_demanded_sites_exact[OF native_call_inverse] same)
qed

text \<open>
  The keyed closure at the call key is one constant, so that its code equation can check the requests at
  its entry: every use of the closure at the call key reads it (\<open>keyed_call_closure_native\<close>),
  and every result is the original closure's.
\<close>

definition native_call_closure ::
    "local_address option finite_native_system \<Rightarrow> (local_address option definition_site\<times>finite_factor_term) fset \<Rightarrow>
      (local_address option definition_site\<times>finite_factor_term) fset" where
  "native_call_closure P R=keyed_call_closure native_call_key native_call_unkey P R"

text \<open>
  The native closure of a set of calls is the program's call closure at the call key, which contains its
  requests, so the evaluation of the closure answers each of them.
\<close>

lemma native_call_closure_requests: "R |\<subseteq>| native_call_closure P R"
  by (simp only: native_call_closure_def keyed_call_closure_exact[OF native_call_inverse]
    finite_program_call_closure_requests)

lemma keyed_call_closure_native [code_unfold]: "keyed_call_closure native_call_key native_call_unkey=native_call_closure"
  by (rule ext)+ (simp only: native_call_closure_def)

lemma native_call_closure_checked_premise:
  "checked_premise (native_call_closure P) (\<lambda>R. finite_system_formed P \<and> fBall R (\<lambda>q. finite_term_formed (snd q)))
    (formed_call_closure P)
    (\<lambda>R. case keyed_demanded_sites native_call_key native_call_unkey (\<lambda>q. finite_program_applications P {|q|})
      finite_application_premise_calls R of None \<Rightarrow> R | Some S \<Rightarrow> S)"
proof (unfold_locales, goal_cases)
  case (1 R)
  then show ?case using keyed_call_closure_formed[of P R] by (simp add: native_call_closure_def)
next
  case (2 R)
  then show ?case by (simp add: native_call_closure_def keyed_call_closure_def)
qed

lemma native_call_closure_code [code]:
  "native_call_closure P R=(if finite_system_formed P \<and> fBall R (\<lambda>q. finite_term_formed (snd q))
    then formed_call_closure P R
    else (case keyed_demanded_sites native_call_key native_call_unkey (\<lambda>q. finite_program_applications P {|q|})
      finite_application_premise_calls R of None \<Rightarrow> R | Some S \<Rightarrow> S))"
  by (fact checked_premise.checked_at_entry[OF native_call_closure_checked_premise[of P], of R])

end
