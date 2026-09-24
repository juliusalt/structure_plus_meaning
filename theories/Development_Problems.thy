theory Development_Problems
  imports Isabelle_Entities
begin

section \<open>A problem is a structural subject with a contract, dependencies and an origin\<close>

text \<open>
  A problem concerns constants of the seeded state: its subject is the set of positions
  those constants occupy in the state's name table, and its contract is the term its
  answer must establish. A problem is therefore identified by what it concerns and what it
  demands, never by a name or by a position in a list. Its origin records how it entered
  the state and its authority records whose it is. A problem whose subject is empty is not
  yet tied to the state; the state retains it as an explicit incompleteness rather than
  inventing a subject for it.
\<close>

datatype development_origin =
    Development_Obligation | Development_Residual | Development_Demand
  | Development_Repair | Development_Direction | Development_Incompleteness

datatype development_authority = Development_Truth | Development_Owner | Development_Generated

datatype development_contract =
    Development_Refinement isabelle_term
  | Development_Proof isabelle_term
  | Development_Presentation isabelle_term
  | Development_Definition isabelle_term
  | Development_Amendment isabelle_term

text \<open>
  A contract is its kind and its term: the kind is the constructor (a locus's kind prefix reads it), and
  the term is what every kind carries.
\<close>

fun development_contract_term :: "development_contract \<Rightarrow> isabelle_term" where
  "development_contract_term (Development_Refinement t)=t"
| "development_contract_term (Development_Proof t)=t"
| "development_contract_term (Development_Presentation t)=t"
| "development_contract_term (Development_Definition t)=t"
| "development_contract_term (Development_Amendment t)=t"

datatype development_problem = Development_Problem
  (problem_subject: "nat fset")
  (problem_contract: development_contract)
  (problem_origin: development_origin)
  (problem_authority: development_authority)

text \<open>
  A problem is presented outside the state as its row in the context that holds it
  (@{text Development_Row_Data}); nothing here presents it.
\<close>

section \<open>Dependencies are ordinary finite inference rules\<close>

text \<open>
  A problem depends on the problems whose answers its own answer needs. These are the rule
  families of the existing finite inference account, so settlement is its least closure,
  backward demand is the existing demand construction, and an unsupported cycle settles
  nothing. A row fires only once its own problem is answered: an answer does not settle a
  problem whose prerequisites are unsettled, and a problem with no prerequisites is not
  settled before it is answered. Readiness is computed from the actual dependencies; no list
  order enters.
\<close>

type_synonym development_dependencies = "(development_problem\<times>(nat\<times>development_problem) fset) fset"

definition development_answered_rules ::
    "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow> development_dependencies" where
  "development_answered_rules D answered=ffilter (\<lambda>(p,H). p |\<in>| answered) D"

definition development_settled ::
    "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow> development_problem set" where
  "development_settled D answered=finite_inference_result (development_answered_rules D answered) {||}"

theorem development_settled_exact:
  "development_settled D answered=
    inference_closure (finite_inference_rules (development_answered_rules D answered)) {}"
  by (simp add: development_settled_def finite_inference_result_exact)

theorem development_settled_answered:
  assumes settled: "p\<in>development_settled D answered"
  shows "p |\<in>| answered"
proof -
  let ?R="finite_inference_rules (development_answered_rules D answered)"
  have "p\<in>inference_consequences ?R (inference_closure ?R {})"
    using settled inference_closure_unfold[of ?R "{}"] by (simp only: development_settled_exact) blast
  then obtain H where "?R p H" by (auto simp: inference_consequences_def)
  then obtain G where "(p,G) |\<in>| development_answered_rules D answered"
    by (auto simp: finite_inference_rules_def)
  then show ?thesis by (simp add: development_answered_rules_def)
qed

definition development_decompositions ::
    "development_dependencies \<Rightarrow> development_problem \<Rightarrow> (nat\<times>development_problem) fset fset" where
  "development_decompositions D p=fimage snd (ffilter (\<lambda>(q,H). q=p) D)"

definition development_premises ::
    "development_dependencies \<Rightarrow> development_problem \<Rightarrow> development_problem fset" where
  "development_premises D p=ffUnion (fimage (fimage snd) (development_decompositions D p))"

theorem development_premises_member:
  "q |\<in>| development_premises D p \<longleftrightarrow>
    (\<exists>H. H |\<in>| development_decompositions D p \<and> q |\<in>| fimage snd H)"
  by (auto simp: development_premises_def ffUnion.rep_eq fimage.rep_eq)

text \<open>
  A problem with more than one decomposition would have its premises joined here, which is
  not what a choice between decompositions means. The state retains such a problem as an
  explicit distinction to resolve instead of joining them silently.
\<close>

definition development_ambiguous ::
    "development_dependencies \<Rightarrow> development_problem list \<Rightarrow> development_problem list" where
  "development_ambiguous D ps=filter (\<lambda>p. 1<fcard (development_decompositions D p)) ps"

definition development_ready ::
    "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow> development_problem \<Rightarrow> bool" where
  "development_ready D answered p \<longleftrightarrow> p |\<notin>| answered \<and>
    fBall (development_premises D p) (\<lambda>q. q\<in>development_settled D answered)"

theorem development_ready_exact:
  "development_ready D answered p \<longleftrightarrow> p |\<notin>| answered \<and>
    fBall (development_premises D p)
      (\<lambda>q. q\<in>inference_closure (finite_inference_rules (development_answered_rules D answered)) {})"
  by (simp add: development_ready_def development_settled_exact)

theorem an_unsettled_premise_refuses_readiness:
  assumes premise: "q |\<in>| development_premises D p" and unsettled: "q\<notin>development_settled D answered"
  shows "\<not> development_ready D answered p"
proof
  assume "development_ready D answered p"
  then have "fBall (development_premises D p) (\<lambda>q. q\<in>development_settled D answered)"
    by (simp add: development_ready_def)
  then have "q\<in>development_settled D answered" by (rule fbspec[OF _ premise])
  then show False using unsettled by simp
qed

text \<open>
  Readiness is also what makes a group of problems independent work: a ready problem's
  prerequisites are settled, hence answered, while a ready problem is unanswered, so no ready
  problem is a prerequisite of another.
\<close>

theorem development_ready_independent:
  assumes first: "development_ready D answered p" and second: "development_ready D answered q"
  shows "q |\<notin>| development_premises D p"
proof
  assume premise: "q |\<in>| development_premises D p"
  have "q\<in>development_settled D answered"
    using first premise by (auto simp: development_ready_def)
  then have "q |\<in>| answered" by (rule development_settled_answered)
  then show False using second by (simp add: development_ready_def)
qed

definition development_ready_problems ::
    "development_dependencies \<Rightarrow> development_problem fset \<Rightarrow> development_problem list \<Rightarrow>
      development_problem list" where
  "development_ready_problems D answered ps=filter (development_ready D answered) ps"

section \<open>The state retains what a seeded problem still lacks\<close>

text \<open>
  A problem with no subject is not yet tied to a constant of the state, and a problem whose
  subject names a constant the state does not declare reaches outside it. Both are retained
  as computed observations; so is every problem the process did not generate under its own
  authority.
\<close>

definition development_without_subject :: "development_problem list \<Rightarrow> development_problem list" where
  "development_without_subject ps=filter (\<lambda>p. problem_subject p={||}) ps"

definition development_residual_problems :: "development_problem list \<Rightarrow> development_problem list" where
  "development_residual_problems ps=filter (\<lambda>p. problem_origin p=Development_Residual) ps"

definition development_undeclared_subjects ::
    "isabelle_context \<Rightarrow> development_problem list \<Rightarrow> nat fset" where
  "development_undeclared_subjects C ps=
    ffilter (\<lambda>c. c\<notin>set (List.map_filter isabelle_declared_constant (snd C)))
      (ffUnion (fset_of_list (map problem_subject ps)))"

theorem development_undeclared_subjects_exact:
  "c |\<in>| development_undeclared_subjects C ps \<longleftrightarrow>
    (\<exists>p\<in>set ps. c |\<in>| problem_subject p) \<and>
    c\<notin>set (List.map_filter isabelle_declared_constant (snd C))"
  by (auto simp: development_undeclared_subjects_def ffUnion.rep_eq fset_of_list_elem fimage.rep_eq)

type_synonym development_problem_assessment =
  "development_problem list\<times>development_problem list\<times>development_problem list\<times>
    development_problem list\<times>nat fset"

definition development_problem_assessment ::
    "isabelle_context \<Rightarrow> development_dependencies \<Rightarrow> development_problem fset \<Rightarrow>
      development_problem list \<Rightarrow> development_problem_assessment" where
  "development_problem_assessment C D answered ps=(development_ready_problems D answered ps,
    development_without_subject ps, development_residual_problems ps, development_ambiguous D ps,
    development_undeclared_subjects C ps)"

end
