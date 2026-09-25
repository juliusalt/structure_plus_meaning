theory Criticism_Samples
  imports Shared_Native_Evaluation Factor_Implemented_Base_Evaluation Finite_Observation_Repairs Finite_Derived_Observations
    Presentation_Equivariance Factor_Program_Entry_Values Factor_Executable_Environment_Values_Base
    Native_Collection_Programs Factor_Finite_Exact_Patterns Factor_Constructed_Judgment_Sources
begin

section \<open>A demand contains its requests\<close>

text \<open>
  The native closure of a set of calls is the program's call closure at the call key, which contains its
  requests, so the evaluation of the closure answers each of them.
\<close>

lemma native_call_closure_requests: "R |\<subseteq>| native_call_closure P R"
  by (simp only: native_call_closure_def keyed_call_closure_exact[OF native_call_inverse]
    finite_program_call_closure_requests)

section \<open>The sample: every entry evaluated natively at both sides of every pair\<close>

text \<open>
  A criticism sample takes a finite program, a list of its entry sites and a list of pairs of argument
  terms. Its demand is the call of every entry at every side of every pair, and the native evaluator
  evaluates that demand once. The pairs are argument terms and nothing more: that the two sides of a
  pair present one subject is a lemma of each instance, never an input of the sample.
\<close>

type_synonym criticism_call = "local_address option definition_site\<times>finite_factor_term"

definition criticism_sides :: "(finite_factor_term\<times>finite_factor_term) list \<Rightarrow> finite_factor_term fset" where
  "criticism_sides ps=fset_of_list (map fst ps@map snd ps)"

definition criticism_calls ::
    "local_address option definition_site list \<Rightarrow> (finite_factor_term\<times>finite_factor_term) list \<Rightarrow>
      criticism_call fset" where
  "criticism_calls ds ps=fset_of_list (List.product ds (map fst ps@map snd ps))"

lemma criticism_calls_member:
  "q |\<in>| criticism_calls ds ps \<longleftrightarrow> fst q\<in>set ds \<and> snd q |\<in>| criticism_sides ps"
  by (cases q) (simp add: criticism_calls_def criticism_sides_def fset_of_list.rep_eq)

definition criticism_evaluation ::
    "local_address option finite_native_system \<Rightarrow> local_address option definition_site list \<Rightarrow>
      (finite_factor_term\<times>finite_factor_term) list \<Rightarrow> criticism_call fset\<times>criticism_call fset option" where
  "criticism_evaluation P ds ps=native_call_evaluation P (criticism_calls ds ps)"

definition criticism_table ::
    "local_address option finite_native_system \<Rightarrow> local_address option definition_site list \<Rightarrow>
      (finite_factor_term\<times>finite_factor_term) list \<Rightarrow> criticism_call fset option" where
  "criticism_table P ds ps=snd (criticism_evaluation P ds ps)"

text \<open>
  The table holds exactly the sample's calls that the decoded program's positive meaning holds, by the
  evaluator's contract and the closure's containing its requests. An evaluation the evaluator cannot
  answer is no table: it is kept apart from an empty one.
\<close>

theorem criticism_table_exact:
  assumes table: "criticism_table P ds ps=Some A" and call: "q |\<in>| criticism_calls ds ps"
  shows "q |\<in>| A \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
proof -
  let ?D="native_call_closure P (criticism_calls ds ps)"
  have evaluation: "finite_program_evaluation P ?D=Some A"
    using table by (simp add: criticism_table_def criticism_evaluation_def native_call_evaluation_def Let_def)
  have demanded: "q |\<in>| ?D" by (rule fsubsetD[OF native_call_closure_requests call])
  show ?thesis using finite_program_evaluation_exact(2)[OF evaluation] demanded by auto
qed

theorem criticism_table_unavailable:
  "criticism_table P ds ps=None \<longleftrightarrow>
    \<not>finite_program_evaluation_ready P (native_call_closure P (criticism_calls ds ps))"
  by (simp add: criticism_table_def criticism_evaluation_def native_call_evaluation_def
    finite_program_evaluation_def Let_def)

section \<open>A table exact at the sample's calls\<close>

text \<open>
  What the record and the refutations read of a table is one property: at every call of the sample the
  table holds the call exactly when the decoded program's positive meaning does. The plain table has it
  (@{thm [source] criticism_table_exact}); a table over a base has it where the base's decision is exact
  (below). Each use of a table states its meaning once over this property.
\<close>

definition criticism_exact_table ::
    "local_address option finite_native_system \<Rightarrow> local_address option definition_site list \<Rightarrow>
      (finite_factor_term\<times>finite_factor_term) list \<Rightarrow> criticism_call fset \<Rightarrow> bool" where
  "criticism_exact_table P ds ps A \<longleftrightarrow> (\<forall>q. q |\<in>| criticism_calls ds ps \<longrightarrow>
    (q |\<in>| A \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)))"

lemma criticism_exact_tableD:
  assumes "criticism_exact_table P ds ps A" "q |\<in>| criticism_calls ds ps"
  shows "q |\<in>| A \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
  using assms unfolding criticism_exact_table_def by blast

lemma criticism_table_exact_table:
  assumes "criticism_table P ds ps=Some A"
  shows "criticism_exact_table P ds ps A"
  using criticism_table_exact[OF assms] by (simp add: criticism_exact_table_def)

section \<open>The sample over a base\<close>

text \<open>
  DECISIONS.md, "The native evaluator evaluates above an implemented base", build S1. The sample's calls
  are closed over the program above a base (@{const implemented_base_program}) and evaluated there, the
  demand's base calls seeded by a decision (@{const native_base_evaluation}). The base's decision enters
  only through its exactness at the demand's base calls; the empty base is the plain sample.
\<close>

definition criticism_base_demand ::
    "local_address option definition_site fset \<Rightarrow> local_address option finite_native_system \<Rightarrow>
      local_address option definition_site list \<Rightarrow> (finite_factor_term\<times>finite_factor_term) list \<Rightarrow>
      criticism_call fset" where
  "criticism_base_demand B P ds ps=native_call_closure (implemented_base_program B P) (criticism_calls ds ps)"

definition criticism_base_evaluation ::
    "local_address option definition_site fset \<Rightarrow> (criticism_call \<Rightarrow> bool) \<Rightarrow>
      local_address option finite_native_system \<Rightarrow> local_address option definition_site list \<Rightarrow>
      (finite_factor_term\<times>finite_factor_term) list \<Rightarrow> criticism_call fset\<times>criticism_call fset option" where
  "criticism_base_evaluation B decide P ds ps=native_base_evaluation B decide P (criticism_calls ds ps)"

definition criticism_base_table ::
    "local_address option definition_site fset \<Rightarrow> (criticism_call \<Rightarrow> bool) \<Rightarrow>
      local_address option finite_native_system \<Rightarrow> local_address option definition_site list \<Rightarrow>
      (finite_factor_term\<times>finite_factor_term) list \<Rightarrow> criticism_call fset option" where
  "criticism_base_table B decide P ds ps=snd (criticism_base_evaluation B decide P ds ps)"

lemma criticism_base_evaluation_demand:
  "criticism_base_evaluation B decide P ds ps=(criticism_base_demand B P ds ps,
    implemented_base_evaluation B decide P (criticism_base_demand B P ds ps))"
  by (simp add: criticism_base_evaluation_def criticism_base_demand_def native_base_evaluation_def Let_def)

definition criticism_decision_exact ::
    "local_address option definition_site fset \<Rightarrow> (criticism_call \<Rightarrow> bool) \<Rightarrow>
      local_address option finite_native_system \<Rightarrow> local_address option definition_site list \<Rightarrow>
      (finite_factor_term\<times>finite_factor_term) list \<Rightarrow> bool" where
  "criticism_decision_exact B decide P ds ps \<longleftrightarrow> (\<forall>q. q |\<in>| criticism_base_demand B P ds ps \<longrightarrow> fst q |\<in>| B \<longrightarrow>
    (decide q \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)))"

theorem criticism_base_table_exact:
  assumes table: "criticism_base_table B decide P ds ps=Some A"
    and decided: "criticism_decision_exact B decide P ds ps" and call: "q |\<in>| criticism_calls ds ps"
  shows "q |\<in>| A \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
proof -
  have "criticism_base_evaluation B decide P ds ps=(criticism_base_demand B P ds ps,Some A)"
    using table by (simp add: criticism_base_table_def criticism_base_evaluation_demand)
  then have result: "native_base_evaluation B decide P (criticism_calls ds ps)=(criticism_base_demand B P ds ps,Some A)"
    by (simp only: criticism_base_evaluation_def)
  have exact: "\<And>q. q |\<in>| criticism_base_demand B P ds ps \<Longrightarrow> fst q |\<in>| B \<Longrightarrow>
      decide q \<longleftrightarrow> decode_finite_call_term q\<in>positive_meaning (decode_finite_system P)"
    using decided unfolding criticism_decision_exact_def by blast
  show ?thesis by (rule native_base_evaluation_exact(3)[OF result exact call])
qed

lemma criticism_base_table_exact_table:
  assumes "criticism_base_table B decide P ds ps=Some A" "criticism_decision_exact B decide P ds ps"
  shows "criticism_exact_table P ds ps A"
  using criticism_base_table_exact[OF assms] by (simp add: criticism_exact_table_def)

theorem criticism_base_table_unavailable:
  "criticism_base_table B decide P ds ps=None \<longleftrightarrow>
    \<not>implemented_base_ready B P (criticism_base_demand B P ds ps)"
  by (simp add: criticism_base_table_def criticism_base_evaluation_demand implemented_base_evaluation_def)

text \<open>The empty base is the plain sample, and every decision is exact there.\<close>

lemma criticism_base_demand_empty:
  "criticism_base_demand {||} P ds ps=native_call_closure P (criticism_calls ds ps)"
  by (simp add: criticism_base_demand_def)

theorem criticism_base_evaluation_empty:
  "criticism_base_evaluation {||} decide P ds ps=criticism_evaluation P ds ps"
  by (simp add: criticism_base_evaluation_def criticism_evaluation_def native_base_evaluation_empty)

corollary criticism_base_table_empty:
  "criticism_base_table {||} decide P ds ps=criticism_table P ds ps"
  by (simp add: criticism_base_table_def criticism_table_def criticism_base_evaluation_empty)

lemma criticism_decision_exact_empty: "criticism_decision_exact {||} decide P ds ps"
  by (simp add: criticism_decision_exact_def)

subsection \<open>An unavailable sample is diagnosed, never recorded as a failure\<close>

text \<open>
  The clauses a demand reaches whose heads leave a premise variable unbound, each with its site, its key
  and its premise-only variables (@{const finite_schema_head_missing}): a program covers a demand's heads
  exactly when there is none. The diagnosis of a sample over a base is computed from the program, the
  base and the sample alone: whether the program is formed, whether the demand is closed over the program
  above the base, and the uncovered clauses outside the base the demand reaches. It is the whole reason a
  table is missing.
\<close>

definition finite_uncovered_clauses where
  "finite_uncovered_clauses P D=ffilter (\<lambda>(d,c,V). V\<noteq>{||})
    (fimage (\<lambda>((d,c),S). (d,c,finite_schema_head_missing S))
      (ffilter (\<lambda>z. fst (fst z) |\<in>| fimage fst D) (finite_system_clauses P)))"

lemma finite_uncovered_clauses_member:
  "(d,c,V) |\<in>| finite_uncovered_clauses P D \<longleftrightarrow>
    (\<exists>S. ((d,c),S) |\<in>| finite_system_clauses P \<and> d |\<in>| fimage fst D \<and>
      V=finite_schema_head_missing S \<and> V\<noteq>{||})"
  unfolding finite_uncovered_clauses_def by force

theorem finite_uncovered_clauses_covered:
  "finite_program_head_covered P D \<longleftrightarrow> finite_uncovered_clauses P D={||}"
proof -
  have uncovered: "finite_uncovered_clauses P D={||} \<longleftrightarrow> (\<forall>d c S. ((d,c),S) |\<in>| finite_system_clauses P \<longrightarrow>
      d |\<in>| fimage fst D \<longrightarrow> finite_schema_head_missing S={||})"
  proof
    assume empty: "finite_uncovered_clauses P D={||}"
    show "\<forall>d c S. ((d,c),S) |\<in>| finite_system_clauses P \<longrightarrow>
        d |\<in>| fimage fst D \<longrightarrow> finite_schema_head_missing S={||}"
    proof (intro allI impI)
      fix d c S assume "((d,c),S) |\<in>| finite_system_clauses P" "d |\<in>| fimage fst D"
      then show "finite_schema_head_missing S={||}"
        using finite_uncovered_clauses_member[of d c "finite_schema_head_missing S" P D] empty by auto
    qed
  next
    assume all: "\<forall>d c S. ((d,c),S) |\<in>| finite_system_clauses P \<longrightarrow>
        d |\<in>| fimage fst D \<longrightarrow> finite_schema_head_missing S={||}"
    have "x |\<notin>| finite_uncovered_clauses P D" for x
    proof -
      obtain d c V where x: "x=(d,c,V)" by (rule prod_cases3)
      show ?thesis using all by (auto simp: x finite_uncovered_clauses_member)
    qed
    then show "finite_uncovered_clauses P D={||}" by (simp add: fset_eq_iff)
  qed
  show ?thesis unfolding uncovered finite_program_head_covered_def fBall_member by auto
qed

definition criticism_diagnosis where
  "criticism_diagnosis B P ds ps=(let D=criticism_base_demand B P ds ps; Q=implemented_base_program B P in
    (finite_system_formed P,finite_program_demand_closed Q D,finite_uncovered_clauses Q D))"

theorem criticism_base_table_diagnosed:
  "criticism_base_table B decide P ds ps=None \<longleftrightarrow> criticism_diagnosis B P ds ps\<noteq>(True,True,{||})"
  by (auto simp: criticism_base_table_unavailable criticism_diagnosis_def implemented_base_ready_def
    finite_uncovered_clauses_covered Let_def)

corollary criticism_table_diagnosed:
  "criticism_table P ds ps=None \<longleftrightarrow> criticism_diagnosis {||} P ds ps\<noteq>(True,True,{||})"
  using criticism_base_table_diagnosed[of "{||}" "\<lambda>_. False" P ds ps] by (simp add: criticism_base_table_empty)

section \<open>The record: every difference is a comparison failure against the candidate\<close>

text \<open>
  The sides are the candidates, the pairing in both directions is the comparison relation and the
  entries are the facets. The observation of an entry at a side is derived from the actual calls of the
  table; the record is the conflicts of that observation over the pairing, and the refuted entries are
  those outside its sound facets.
\<close>

definition criticism_paired :: "(finite_factor_term\<times>finite_factor_term) list \<Rightarrow>
    finite_factor_term \<Rightarrow> finite_factor_term \<Rightarrow> bool" where
  "criticism_paired ps c c' \<longleftrightarrow> (c,c')\<in>set ps \<or> (c',c)\<in>set ps"

lemma criticism_paired_sides:
  assumes "criticism_paired ps c c'"
  shows "c |\<in>| criticism_sides ps" "c' |\<in>| criticism_sides ps"
  using assms by (auto simp: criticism_paired_def criticism_sides_def fset_of_list_elem intro: rev_image_eqI)

definition criticism_observations ::
    "local_address option definition_site list \<Rightarrow> (finite_factor_term\<times>finite_factor_term) list \<Rightarrow>
      criticism_call fset \<Rightarrow> (local_address option definition_site\<times>finite_factor_term\<times>unit) fset" where
  "criticism_observations ds ps A=finite_derived_observations (fimage (\<lambda>t. (t,t)) (criticism_sides ps))
    (fimage (\<lambda>d. (d,d)) (fset_of_list ds)) {|((),())|} (\<lambda>d t w. (d,t) |\<in>| A)"

lemma criticism_observations_member:
  "(d,t,w) |\<in>| criticism_observations ds ps A \<longleftrightarrow> d\<in>set ds \<and> t |\<in>| criticism_sides ps \<and> (d,t) |\<in>| A"
proof
  assume "(d,t,w) |\<in>| criticism_observations ds ps A"
  then show "d\<in>set ds \<and> t |\<in>| criticism_sides ps \<and> (d,t) |\<in>| A"
    by (auto simp: criticism_observations_def finite_derived_observation_member fset_of_list_elem)
next
  assume member: "d\<in>set ds \<and> t |\<in>| criticism_sides ps \<and> (d,t) |\<in>| A"
  show "(d,t,w) |\<in>| criticism_observations ds ps A"
    unfolding criticism_observations_def finite_derived_observation_member
    using member by (intro exI[of _ d] exI[of _ t] exI[of _ "()"]) (auto simp: fset_of_list_elem intro: rev_image_eqI)
qed

theorem criticism_observation_at_call:
  assumes entry: "d\<in>set ds" and side: "t |\<in>| criticism_sides ps"
  shows "(d,t,()) |\<in>| criticism_observations ds ps A \<longleftrightarrow> (d,t) |\<in>| A"
proof -
  have formed: "finite_observation_subjects_formed (fimage (\<lambda>t. (t,t)) (criticism_sides ps))
      (fimage (\<lambda>d. (d,d)) (fset_of_list ds)) {|((),())|}"
    by (auto simp: finite_observation_subjects_formed_def single_valued_def)
  have "(d,t,()) |\<in>| finite_derived_observations (fimage (\<lambda>t. (t,t)) (criticism_sides ps))
      (fimage (\<lambda>d. (d,d)) (fset_of_list ds)) {|((),())|} (\<lambda>d t w. (d,t) |\<in>| A) \<longleftrightarrow> (d,t) |\<in>| A"
    using finite_derived_observation_at_subject[OF formed, where c=t and s=t and f=d and u=d and w="()"
      and v="()" and P="\<lambda>d t w. (d,t) |\<in>| A"] entry side by (simp add: fset_of_list_elem)
  then show ?thesis by (simp add: criticism_observations_def)
qed

definition criticism_record ::
    "local_address option definition_site list \<Rightarrow> (finite_factor_term\<times>finite_factor_term) list \<Rightarrow>
      criticism_call fset \<Rightarrow>
      (finite_factor_term\<times>finite_factor_term\<times>local_address option definition_site\<times>unit) fset" where
  "criticism_record ds ps A=finite_observation_conflicts (criticism_sides ps) (criticism_paired ps)
    (fset_of_list ds) (criticism_observations ds ps A)"

theorem criticism_record_exact:
  "(c,c',d,w) |\<in>| criticism_record ds ps A \<longleftrightarrow>
    criticism_paired ps c c' \<and> d\<in>set ds \<and> (d,c) |\<in>| A \<and> (d,c') |\<notin>| A"
  using criticism_paired_sides[of ps c c']
  by (auto simp: criticism_record_def finite_observation_conflicts_exact observation_conflicts_def
    candidate_losses_def candidate_profile_def finite_table_observations_def criticism_observations_member
    fset_of_list_elem)

theorem exact_table_record_meaning:
  assumes exact: "criticism_exact_table P ds ps A"
  shows "(c,c',d,w) |\<in>| criticism_record ds ps A \<longleftrightarrow> criticism_paired ps c c' \<and> d\<in>set ds \<and>
    (d,decode_finite_term c)\<in>positive_meaning (decode_finite_system P) \<and>
    (d,decode_finite_term c')\<notin>positive_meaning (decode_finite_system P)"
proof (cases "criticism_paired ps c c' \<and> d\<in>set ds")
  case True
  then have calls: "(d,c) |\<in>| criticism_calls ds ps" "(d,c') |\<in>| criticism_calls ds ps"
    using criticism_paired_sides[of ps c c'] by (simp_all add: criticism_calls_member)
  show ?thesis using criticism_exact_tableD[OF exact calls(1)] criticism_exact_tableD[OF exact calls(2)] True
    by (simp add: criticism_record_exact decode_finite_call_term_def)
next
  case False
  then show ?thesis by (auto simp: criticism_record_exact)
qed

theorem criticism_record_meaning:
  assumes table: "criticism_table P ds ps=Some A"
  shows "(c,c',d,w) |\<in>| criticism_record ds ps A \<longleftrightarrow> criticism_paired ps c c' \<and> d\<in>set ds \<and>
    (d,decode_finite_term c)\<in>positive_meaning (decode_finite_system P) \<and>
    (d,decode_finite_term c')\<notin>positive_meaning (decode_finite_system P)"
  by (rule exact_table_record_meaning[OF criticism_table_exact_table[OF table]])

definition criticism_refuted ::
    "local_address option definition_site list \<Rightarrow> (finite_factor_term\<times>finite_factor_term) list \<Rightarrow>
      criticism_call fset \<Rightarrow> local_address option definition_site fset" where
  "criticism_refuted ds ps A=fset_of_list ds |-| finite_sound_observation_facets (criticism_sides ps)
    (criticism_paired ps) (fset_of_list ds) (criticism_observations ds ps A)"

theorem criticism_refuted_exact:
  "d |\<in>| criticism_refuted ds ps A \<longleftrightarrow> (\<exists>c c'. (c,c',d,()) |\<in>| criticism_record ds ps A)"
proof
  assume "d |\<in>| criticism_refuted ds ps A"
  then show "\<exists>c c'. (c,c',d,()) |\<in>| criticism_record ds ps A"
    by (auto simp: criticism_refuted_def minus_fset.rep_eq fset_of_list.rep_eq finite_sound_observation_facets_exact
      finite_table_observations_def criticism_observations_member criticism_record_exact split: if_splits)
next
  assume "\<exists>c c'. (c,c',d,()) |\<in>| criticism_record ds ps A"
  then obtain c c' where paired: "criticism_paired ps c c'" and entry: "d\<in>set ds"
    and holds: "(d,c) |\<in>| A" and fails: "(d,c') |\<notin>| A"
    by (auto simp: criticism_record_exact)
  have sides: "c |\<in>| criticism_sides ps" "c' |\<in>| criticism_sides ps"
    by (rule criticism_paired_sides[OF paired])+
  have lost: "\<not>finite_table_observations (criticism_observations ds ps A) d c\<subseteq>
      finite_table_observations (criticism_observations ds ps A) d c'"
    using entry holds fails sides by (auto simp: finite_table_observations_def criticism_observations_member)
  show "d |\<in>| criticism_refuted ds ps A"
    using paired entry sides lost
    by (auto simp: criticism_refuted_def minus_fset.rep_eq fset_of_list.rep_eq finite_sound_observation_facets_exact)
qed

text \<open>A recorded row persists when further observations are added to the facets it is compared under.\<close>

theorem criticism_record_persists:
  assumes "set ds\<subseteq>G"
  shows "fset (criticism_record ds ps A)\<subseteq>observation_conflicts (fset (criticism_sides ps))
    (criticism_paired ps) G (finite_table_observations (criticism_observations ds ps A))"
  unfolding criticism_record_def finite_observation_conflicts_exact
  by (rule adding_observations_cannot_remove_a_conflict) (simp add: assms fset_of_list.rep_eq)

section \<open>A difference refutes; agreement establishes nothing\<close>

text \<open>
  Stated once for any presented relation. An observation that differs at two presentations standing in
  an admissible renaming correspondence of a class is exact to no equivariant presented predicate of
  that class; at the identity's correspondence, two presentations of one subject, it is exact to no
  presented predicate at all, and no presented relation contract has it as its operation. Nothing here
  concludes anything from the absence of a difference.
\<close>

theorem criticism_refutes:
  assumes presented: "presentation_class R D X" and action: "renaming_action admissible act D"
    and renaming: "admissible h" and corresponds: "renaming_correspondence R act h p q"
    and differs: "observe p \<noteq> observe q"
  shows "\<not>(\<exists>P. (\<forall>t. observe t \<longleftrightarrow> presented_predicate R P t) \<and> renaming_equivariant admissible act D P)"
proof
  assume "\<exists>P. (\<forall>t. observe t \<longleftrightarrow> presented_predicate R P t) \<and> renaming_equivariant admissible act D P"
  then obtain P where exact: "\<And>t. observe t \<longleftrightarrow> presented_predicate R P t"
    and equivariant: "renaming_equivariant admissible act D P" by blast
  have "\<forall>h. admissible h \<longrightarrow> rel_fun (renaming_correspondence R act h) (=) observe observe"
    using presented_predicate_renaming[OF presented action exact] equivariant by blast
  then have "observe p=observe q" using renaming corresponds by (auto simp: rel_fun_def)
  then show False using differs by simp
qed

corollary criticism_refutes_presentation:
  assumes presented: "presentation_class R D X"
    and transported: "presentation_transport R R p q" and differs: "observe p \<noteq> observe q"
  shows "\<not>(\<exists>P. \<forall>t. observe t \<longleftrightarrow> presented_predicate R P t)"
proof -
  have action: "renaming_action (bij::(unit \<Rightarrow> unit) \<Rightarrow> bool) (\<lambda>h a. a) D"
    by (rule permutation_renaming_action)
  have corresponds: "renaming_correspondence R (\<lambda>(h::unit \<Rightarrow> unit) a. a) id p q"
    using renaming_correspondence_id[OF presented action] transported by blast
  have equivariant: "renaming_equivariant (bij::(unit \<Rightarrow> unit) \<Rightarrow> bool) (\<lambda>h a. a) D P" for P
    by (simp add: renaming_equivariant_def)
  show ?thesis using criticism_refutes[OF presented action bij_id corresponds differs] equivariant by blast
qed

corollary criticism_refutes_relation_contract:
  assumes left: "presentation_transport R R p p'" and right: "presentation_transport S S q q'"
    and differs: "observe p q \<noteq> observe p' q'"
  shows "\<not>presented_relation_contract R D A S E B relation observe"
proof
  assume contract: "presented_relation_contract R D A S E B relation observe"
  obtain a where a: "R a p" "R a p'" using left by (auto simp: presentation_transport_def)
  obtain b where b: "S b q" "S b q'" using right by (auto simp: presentation_transport_def)
  have "observe p q \<longleftrightarrow> observe p' q'"
    by (rule presented_relation_contract.invariance[OF contract a(1) b(1) a(2) b(2)])
  then show False using differs by simp
qed

text \<open>
  A recorded row of a sample whose every pair stands in the correspondence refutes the invariance of its
  entry's meaning along the correspondence.
\<close>

theorem exact_table_row_refutes:
  assumes presented: "presentation_class R D X" and action: "renaming_action admissible act D"
    and renaming: "admissible h"
    and pairs: "\<And>p q. (p,q)\<in>set ps \<Longrightarrow>
      renaming_correspondence R act h (decode_finite_term p) (decode_finite_term q)"
    and exact: "criticism_exact_table P ds ps A" and row: "(c,c',d,w) |\<in>| criticism_record ds ps A"
  shows "\<not>(\<exists>Q. (\<forall>t. (d,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> presented_predicate R Q t) \<and>
    renaming_equivariant admissible act D Q)"
proof -
  have paired: "criticism_paired ps c c'"
    and holds: "(d,decode_finite_term c)\<in>positive_meaning (decode_finite_system P)"
    and fails: "(d,decode_finite_term c')\<notin>positive_meaning (decode_finite_system P)"
    using row by (simp_all add: exact_table_record_meaning[OF exact])
  have differ: "((d,decode_finite_term c)\<in>positive_meaning (decode_finite_system P)) \<noteq>
      ((d,decode_finite_term c')\<in>positive_meaning (decode_finite_system P))"
    using holds fails by simp
  from paired consider (forward) "(c,c')\<in>set ps" | (backward) "(c',c)\<in>set ps"
    by (auto simp: criticism_paired_def)
  then show ?thesis
  proof cases
    case forward
    show ?thesis by (rule criticism_refutes[OF presented action renaming pairs[OF forward] differ])
  next
    case backward
    show ?thesis by (rule criticism_refutes[OF presented action renaming pairs[OF backward] not_sym[OF differ]])
  qed
qed

theorem criticism_row_refutes:
  assumes presented: "presentation_class R D X" and action: "renaming_action admissible act D"
    and renaming: "admissible h"
    and pairs: "\<And>p q. (p,q)\<in>set ps \<Longrightarrow>
      renaming_correspondence R act h (decode_finite_term p) (decode_finite_term q)"
    and table: "criticism_table P ds ps=Some A" and row: "(c,c',d,w) |\<in>| criticism_record ds ps A"
  shows "\<not>(\<exists>Q. (\<forall>t. (d,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> presented_predicate R Q t) \<and>
    renaming_equivariant admissible act D Q)"
  by (rule exact_table_row_refutes[OF presented action renaming pairs criticism_table_exact_table[OF table] row])

corollary exact_table_row_refutes_presentation:
  assumes presented: "presentation_class R D X"
    and pairs: "\<And>p q. (p,q)\<in>set ps \<Longrightarrow>
      presentation_transport R R (decode_finite_term p) (decode_finite_term q)"
    and exact: "criticism_exact_table P ds ps A" and row: "(c,c',d,w) |\<in>| criticism_record ds ps A"
  shows "\<not>(\<exists>Q. \<forall>t. (d,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> presented_predicate R Q t)"
proof -
  have action: "renaming_action (bij::(unit \<Rightarrow> unit) \<Rightarrow> bool) (\<lambda>h a. a) D"
    by (rule permutation_renaming_action)
  have corresponds: "renaming_correspondence R (\<lambda>(h::unit \<Rightarrow> unit) a. a) id
      (decode_finite_term p) (decode_finite_term q)" if "(p,q)\<in>set ps" for p q
    using renaming_correspondence_id[OF presented action] pairs[OF that] by blast
  have equivariant: "renaming_equivariant (bij::(unit \<Rightarrow> unit) \<Rightarrow> bool) (\<lambda>h a. a) D Q" for Q
    by (simp add: renaming_equivariant_def)
  show ?thesis
    using exact_table_row_refutes[OF presented action bij_id corresponds exact row] equivariant by blast
qed

corollary criticism_row_refutes_presentation:
  assumes presented: "presentation_class R D X"
    and pairs: "\<And>p q. (p,q)\<in>set ps \<Longrightarrow>
      presentation_transport R R (decode_finite_term p) (decode_finite_term q)"
    and table: "criticism_table P ds ps=Some A" and row: "(c,c',d,w) |\<in>| criticism_record ds ps A"
  shows "\<not>(\<exists>Q. \<forall>t. (d,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> presented_predicate R Q t)"
  by (rule exact_table_row_refutes_presentation[OF presented pairs criticism_table_exact_table[OF table] row])

section \<open>Part (b): every collection enumerated in the reverse of its canonical order\<close>

text \<open>
  The second presentation of an environment lists its artifact rows, its binding rows and, in every
  artifact, its carrier, incidence and attachment lists in the reverse of the canonical order: the
  existing reversal of the two outer collections (@{const reversed_environment_term}, whose contract is
  @{thm [source] reversed_environment_value_exact}), with each artifact row's own lists reversed as well.
  What is new is the change of each artifact row, lifted over the collection pointwise: a counted list
  keeps its multiplicities under reversal, and every complete enumeration of an artifact is admitted.
\<close>

definition reversed_artifact_rows :: "artifact_value_rows \<Rightarrow> artifact_value_rows" where
  "reversed_artifact_rows q=(case q of (A,E,B,F) \<Rightarrow> (rev A,rev E,rev B,rev F))"

definition deep_reversed_environment_term ::
    "local_address option finite_artifact_environment \<Rightarrow> factor_term" where
  "deep_reversed_environment_term C=Pair_Term
    (data_list_term (map (\<lambda>q. environment_artifact_rows_term (fst q,reversed_artifact_rows (snd q)))
      (rev (finite_environment_artifact_rows C))))
    (data_list_term (map binding_data (rev (sorted_list_of_fset (finite_environment_bindings C)))))"

lemma deep_reversed_environment_term_self_contained [simp]:
  "self_contained_term (deep_reversed_environment_term C)"
  by (simp add: deep_reversed_environment_term_def data_list_term_self_contained environment_artifact_rows_term_def)

lemma artifact_rows_term_reversed:
  assumes present: "artifact_value_presents R (artifact_rows_term q)"
  shows "artifact_value_presents R (artifact_rows_term (reversed_artifact_rows q))"
proof -
  obtain A E B F where q: "q=(A,E,B,F)" by (cases q)
  have enumeration: "artifact_enumeration R A E B F"
    using present by (simp add: q artifact_rows_term_def artifact_value_presents_data)
  have distinct: "distinct A" "distinct E" "distinct F" using enumeration by (simp_all add: artifact_enumeration_def)
  have counts: "count_list (rev B)=count_list B" by (rule ext) (simp add: count_mset[symmetric])
  have "artifact_enumeration R (rev A) (rev E) (rev B) (rev F)"
    using artifact_enumeration_order[of "rev A" A "rev E" E "rev F" F "rev B" B R] distinct counts enumeration
    by simp
  then show ?thesis by (simp add: q reversed_artifact_rows_def artifact_rows_term_def artifact_value_presents_data)
qed

lemma data_collection_presents_pointwise:
  assumes present: "data_collection_presents read A (data_list_term (map g ys))"
    and changed: "\<And>x y. read x (g y) \<Longrightarrow> read x (h y)"
  shows "data_collection_presents read A (data_list_term (map h ys))"
proof -
  obtain xs ts where distinct: "distinct xs" and members: "set xs=A" and read: "list_all2 read xs ts"
    and term_eq: "data_list_term (map g ys)=data_list_term ts"
    using present by (auto simp: data_collection_presents_def)
  have ts: "ts=map g ys" using term_eq by (simp add: data_list_term_injective)
  have "list_all2 (\<lambda>x y. read x (g y)) xs ys"
    using read by (simp add: ts list_all2_map2)
  then have "list_all2 (\<lambda>x y. read x (h y)) xs ys" by (rule list_all2_mono) (rule changed)
  then have changed_rows: "list_all2 read xs (map h ys)" by (simp add: list_all2_map2)
  show ?thesis unfolding data_collection_presents_def
    by (intro exI[of _ xs] exI[of _ "map h ys"]) (use distinct members changed_rows in simp)
qed

theorem deep_reversed_environment_presents:
  assumes formed: "finite_environment_formed C"
  shows "environment_value_presents (decode_finite_environment C) (deep_reversed_environment_term C)"
proof -
  have outer: "environment_value_presents (decode_finite_environment C) (reversed_environment_term C)"
    using reversed_environment_value_exact[of "decode_finite_environment C" C] formed by simp
  then have env: "environment_formed (decode_finite_environment C)"
    and artifacts: "data_collection_presents environment_artifact_entry_presents
      (environment_artifacts (decode_finite_environment C))
      (data_list_term (map environment_artifact_rows_term (rev (finite_environment_artifact_rows C))))"
    and bindings: "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings (decode_finite_environment C))
      (data_list_term (map binding_data (rev (sorted_list_of_fset (finite_environment_bindings C)))))"
    by (auto simp del: rev_map simp: environment_value_presents_def reversed_environment_term_def)
  have artifacts': "data_collection_presents environment_artifact_entry_presents
      (environment_artifacts (decode_finite_environment C))
      (data_list_term (map (\<lambda>q. environment_artifact_rows_term (fst q,reversed_artifact_rows (snd q)))
        (rev (finite_environment_artifact_rows C))))"
  proof (rule data_collection_presents_pointwise[OF artifacts])
    fix x y assume "environment_artifact_entry_presents x (environment_artifact_rows_term y)"
    then obtain v where v: "artifact_value_presents (snd x) v"
      and t: "environment_artifact_rows_term y=Pair_Term (use_data_term (fst x)) v"
      by (auto simp: environment_artifact_entry_presents_def)
    have rows: "v=artifact_rows_term (snd y)" and use: "use_data_term (fst y)=use_data_term (fst x)"
      using t by (simp_all add: environment_artifact_rows_term_def)
    show "environment_artifact_entry_presents x
        (environment_artifact_rows_term (fst y,reversed_artifact_rows (snd y)))"
      using artifact_rows_term_reversed[of "snd x" "snd y"] v rows use
      by (auto simp: environment_artifact_entry_presents_def environment_artifact_rows_term_def)
  qed
  show ?thesis using env artifacts' bindings
    by (auto simp del: rev_map simp: environment_value_presents_def deep_reversed_environment_term_def)
qed

text \<open>
  The argument shapes of part (b): an environment, a site of it, a program entry of it and pairs of
  shapes over one environment, each presented around a presentation of the environment. Each shape is
  a class of its own whose subject is the environment, recovered from any presentation by the
  uniqueness of the environment, site and entry values.
\<close>

datatype criticism_shape = Environment_Argument | Site_Argument "local_address option" local_address
  | Entry_Argument "local_address option" local_address "local_address option\<times>local_address"
  | Pair_Argument criticism_shape criticism_shape

fun argument_term :: "factor_term \<Rightarrow> criticism_shape \<Rightarrow> factor_term" where
  "argument_term e Environment_Argument=e"
| "argument_term e (Site_Argument u r)=Pair_Term e (site_data_term u r)"
| "argument_term e (Entry_Argument u r d)=Pair_Term (Pair_Term e (site_data_term u r)) (site_data_term (fst d) (snd d))"
| "argument_term e (Pair_Argument a b)=Pair_Term (argument_term e a) (argument_term e b)"

fun argument_presents :: "criticism_shape \<Rightarrow> local_address option artifact_environment \<Rightarrow> factor_term \<Rightarrow> bool" where
  "argument_presents Environment_Argument E t \<longleftrightarrow> environment_value_presents E t"
| "argument_presents (Site_Argument u r) E t \<longleftrightarrow> site_value_presents E u r t"
| "argument_presents (Entry_Argument u r d) E t \<longleftrightarrow> program_entry_value_presents E u r d t"
| "argument_presents (Pair_Argument a b) E t \<longleftrightarrow>
    (\<exists>p q. t=Pair_Term p q \<and> argument_presents a E p \<and> argument_presents b E q)"

fun argument_positions :: "local_address option artifact_environment \<Rightarrow> criticism_shape \<Rightarrow> bool" where
  "argument_positions E Environment_Argument \<longleftrightarrow> True"
| "argument_positions E (Site_Argument u r) \<longleftrightarrow> (u,r)\<in>environment_positions E"
| "argument_positions E (Entry_Argument u r d) \<longleftrightarrow> (u,r)\<in>environment_positions E \<and> d\<in>environment_positions E"
| "argument_positions E (Pair_Argument a b) \<longleftrightarrow> argument_positions E a \<and> argument_positions E b"

lemma argument_presents_term:
  assumes presented: "environment_value_presents E e" and positions: "argument_positions E s"
  shows "argument_presents s E (argument_term e s)"
  using positions by (induction s)
    (auto simp: presented site_value_presents_def program_entry_value_presents_def)

lemma argument_presents_recovery:
  assumes "argument_presents s E t" "argument_presents s F t"
  shows "E=F"
  using assms
proof (induction s arbitrary: t)
  case Environment_Argument
  then show ?case by (metis argument_presents.simps(1) environment_value_presents_unique)
next
  case (Site_Argument u r)
  then show ?case by (metis argument_presents.simps(2) site_value_presents_unique)
next
  case (Entry_Argument u r d)
  then show ?case by (metis argument_presents.simps(3) program_entry_value_presents_unique)
next
  case (Pair_Argument a b t)
  obtain p q where t: "t=Pair_Term p q" and left: "argument_presents a E p"
    using Pair_Argument.prems(1) by auto
  obtain p' q' where t': "t=Pair_Term p' q'" and left': "argument_presents a F p'"
    using Pair_Argument.prems(2) by auto
  show ?case using Pair_Argument.IH(1)[OF left] left' t t' by simp
qed

theorem argument_presentation_class:
  "presentation_class (argument_presents s) (\<lambda>E. \<exists>t. argument_presents s E t) (\<lambda>t. \<exists>E. argument_presents s E t)"
  by unfold_locales (blast intro: argument_presents_recovery)+

lemma argument_term_self_contained: "self_contained_term e \<Longrightarrow> self_contained_term (argument_term e s)"
  by (induction s) simp_all

definition canonical_argument_value ::
    "local_address option finite_artifact_environment \<Rightarrow> criticism_shape \<Rightarrow> finite_factor_term" where
  "canonical_argument_value C s=the (finite_self_contained_term (argument_term (finite_environment_term C) s))"

definition reversed_argument_value ::
    "local_address option finite_artifact_environment \<Rightarrow> criticism_shape \<Rightarrow> finite_factor_term" where
  "reversed_argument_value C s=the (finite_self_contained_term (argument_term (deep_reversed_environment_term C) s))"

lemma decode_canonical_argument_value [simp]:
  "decode_finite_term (canonical_argument_value C s)=argument_term (finite_environment_term C) s"
  unfolding canonical_argument_value_def
  by (rule decode_finite_self_contained_term) (simp add: argument_term_self_contained)

lemma decode_reversed_argument_value [simp]:
  "decode_finite_term (reversed_argument_value C s)=argument_term (deep_reversed_environment_term C) s"
  unfolding reversed_argument_value_def
  by (rule decode_finite_self_contained_term) (simp add: argument_term_self_contained)

theorem argument_values_present_one_subject:
  assumes formed: "finite_environment_formed C" and positions: "argument_positions (decode_finite_environment C) s"
  shows "argument_presents s (decode_finite_environment C) (decode_finite_term (canonical_argument_value C s))"
    "argument_presents s (decode_finite_environment C) (decode_finite_term (reversed_argument_value C s))"
proof -
  have canonical: "environment_value_presents (decode_finite_environment C) (finite_environment_term C)"
    using finite_environment_value_exact[of "decode_finite_environment C" C] formed by simp
  show "argument_presents s (decode_finite_environment C) (decode_finite_term (canonical_argument_value C s))"
    using argument_presents_term[OF canonical positions] by simp
  show "argument_presents s (decode_finite_environment C) (decode_finite_term (reversed_argument_value C s))"
    using argument_presents_term[OF deep_reversed_environment_presents[OF formed] positions] by simp
qed

corollary argument_values_transport:
  assumes "finite_environment_formed C" "argument_positions (decode_finite_environment C) s"
  shows "presentation_transport (argument_presents s) (argument_presents s)
    (decode_finite_term (canonical_argument_value C s)) (decode_finite_term (reversed_argument_value C s))"
  using argument_values_present_one_subject[OF assms] by (auto simp: presentation_transport_def)

definition reversal_pairs ::
    "criticism_shape \<Rightarrow> local_address option finite_artifact_environment list \<Rightarrow>
      (finite_factor_term\<times>finite_factor_term) list" where
  "reversal_pairs s Cs=map (\<lambda>C. (canonical_argument_value C s,reversed_argument_value C s)) Cs"

theorem exact_table_reversal_row_refutes:
  assumes formed: "\<forall>C\<in>set Cs. finite_environment_formed C \<and> argument_positions (decode_finite_environment C) s"
    and exact: "criticism_exact_table P ds (reversal_pairs s Cs) A"
    and row: "(c,c',d,w) |\<in>| criticism_record ds (reversal_pairs s Cs) A"
  shows "\<not>(\<exists>Q. \<forall>t. (d,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> presented_predicate (argument_presents s) Q t)"
proof (rule exact_table_row_refutes_presentation[OF argument_presentation_class _ exact row])
  fix p q assume "(p,q)\<in>set (reversal_pairs s Cs)"
  then obtain C where C: "C\<in>set Cs" and p: "p=canonical_argument_value C s" and q: "q=reversed_argument_value C s"
    by (auto simp: reversal_pairs_def)
  show "presentation_transport (argument_presents s) (argument_presents s) (decode_finite_term p) (decode_finite_term q)"
    using argument_values_transport[of C s] formed C by (simp add: p q)
qed

theorem reversal_row_refutes:
  assumes formed: "\<forall>C\<in>set Cs. finite_environment_formed C \<and> argument_positions (decode_finite_environment C) s"
    and table: "criticism_table P ds (reversal_pairs s Cs)=Some A"
    and row: "(c,c',d,w) |\<in>| criticism_record ds (reversal_pairs s Cs) A"
  shows "\<not>(\<exists>Q. \<forall>t. (d,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> presented_predicate (argument_presents s) Q t)"
  by (rule exact_table_reversal_row_refutes[OF formed criticism_table_exact_table[OF table] row])

section \<open>Controls\<close>

text \<open>
  Two artifacts at two uses: the canonical environment value lists the row of the first use first, the
  reversed one the row of the second. One entry reads the first artifact row literally, and the sample
  records a row at its pair; one entry asks for two artifact rows, invariant over every enumeration, and
  records none. A program whose rule calls an undefined site has no evaluation, and a program whose entry
  holds nowhere has an empty table.
\<close>

definition control_environment :: "local_address option finite_artifact_environment" where
  "control_environment=finite_enumerated_environment
    [(Some [0],finite_empty_artifact),(Some [1],finite_empty_artifact)] []"

definition control_first_row :: finite_factor_term where
  "control_first_row=(case finite_environment_value control_environment of
    Finite_Pair (Finite_Pair r x) y \<Rightarrow> r | t \<Rightarrow> t)"

definition control_first_entry :: "local_address option definition_site" where
  "control_first_entry=(Some [4,3,5],[0])"

definition control_invariant_entry :: "local_address option definition_site" where
  "control_invariant_entry=(Some [4,3,5],[1])"

definition control_missing_entry :: "local_address option definition_site" where
  "control_missing_entry=(Some [4,3,5],[2])"

definition control_program :: "local_address option finite_native_system" where
  "control_program=finite_rule_program
    [(control_first_entry,[([0],finite_native_rule (Finite_Pattern_Pair
        (Finite_Pattern_Pair (finite_exact_term_pattern control_first_row) (native_var 0)) (native_var 1)) [])]),
     (control_invariant_entry,[([0],finite_native_rule (Finite_Pattern_Pair
        (Finite_Pattern_Pair (native_var 0) (Finite_Pattern_Pair (native_var 1) (native_var 2))) (native_var 3)) [])])]"

definition control_unavailable_program :: "local_address option finite_native_system" where
  "control_unavailable_program=finite_rule_program
    [(control_first_entry,[([0],finite_native_rule (native_var 0) [([0],(control_missing_entry,native_var 0))])])]"

definition control_empty_program :: "local_address option finite_native_system" where
  "control_empty_program=finite_rule_program
    [(control_first_entry,[([0],finite_native_rule (Finite_Pattern_Payload [7]) [])])]"

definition control_pairs :: "(finite_factor_term\<times>finite_factor_term) list" where
  "control_pairs=reversal_pairs Environment_Argument [control_environment]"

definition control_reading :: "unit \<Rightarrow> bool list" where
  "control_reading _=(let p=canonical_argument_value control_environment Environment_Argument;
      q=reversed_argument_value control_environment Environment_Argument;
      ds=[control_first_entry,control_invariant_entry] in
    case criticism_table control_program ds control_pairs of None \<Rightarrow> [False]
    | Some A \<Rightarrow> [p\<noteq>q,criticism_record ds control_pairs A={|(p,q,control_first_entry,())|},
        criticism_refuted ds control_pairs A={|control_first_entry|},
        (control_first_entry,p) |\<in>| A,(control_invariant_entry,p) |\<in>| A,(control_invariant_entry,q) |\<in>| A])"

definition control_unavailable :: "unit \<Rightarrow> bool list" where
  "control_unavailable _=[criticism_table control_unavailable_program [control_first_entry] control_pairs=None]"

definition control_empty :: "unit \<Rightarrow> bool list" where
  "control_empty _=[criticism_table control_empty_program [control_first_entry] control_pairs=Some {||}]"

ML \<open>
  local
    fun run name f expected =
      let
        val (time, result) = Timing.timing f ()
        val shown = ML_Syntax.print_list Bool.toString result
      in
        if result = expected then writeln ("CRITICISM_CONTROL " ^ name ^ " " ^ shown ^ " " ^ Timing.message time)
        else error ("Criticism control " ^ name ^ " differs: " ^ shown)
      end
  in
    val _ = run "reading" @{code control_reading} [true, true, true, true, true, true]
    val _ = run "unavailable" @{code control_unavailable} [true]
    val _ = run "empty" @{code control_empty} [true]
  end
\<close>

subsection \<open>A control over a base\<close>

text \<open>
  The program of @{text Factor_Implemented_Base_Evaluation}'s control: its root (None,[3]) holds of a term
  where the witness (None,[2]) does, and the witness's clause has the premise-only variable [1]. The sample
  calls the root at the empty payload and at a payload that is no octet list, so its two sides differ. The
  plain sample is unavailable, its diagnosis naming the witness's clause and variable; over the base
  holding the witness, whose decision is that the argument is formed, proved exact at the demand's base
  call, the table and its record stand beside the program's meaning. One evaluation executes the control.
\<close>

definition criticism_base_control_pairs :: "(finite_factor_term\<times>finite_factor_term) list" where
  "criticism_base_control_pairs=[(Finite_Payload [],Finite_Payload [256])]"

ML \<open>val criticism_base_control_start = Timing.start ()\<close>

lemma criticism_base_control_executed:
  "criticism_diagnosis {||} implemented_base_control [(None,[3])] criticism_base_control_pairs=
      (True,True,{|((None,[2]),[0],{|[1]|})|}) \<and>
    criticism_base_demand {|(None,[2])|} implemented_base_control [(None,[3])] criticism_base_control_pairs=
      {|((None,[3]),Finite_Payload []),((None,[3]),Finite_Payload [256]),((None,[2]),Finite_Payload [])|} \<and>
    criticism_base_table {|(None,[2])|} implemented_base_control_decision implemented_base_control [(None,[3])]
      criticism_base_control_pairs=Some {|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|} \<and>
    criticism_record [(None,[3])] criticism_base_control_pairs
      {|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|}=
      {|(Finite_Payload [],Finite_Payload [256],(None,[3]),())|}"
  by eval

ML \<open>writeln ("CRITICISM_CONTROL base " ^ Timing.message (Timing.result criticism_base_control_start))\<close>

lemma criticism_base_control_plain:
  "criticism_table implemented_base_control [(None,[3])] criticism_base_control_pairs=None"
  using criticism_base_control_executed by (simp add: criticism_table_diagnosed)

lemma criticism_base_control_decided:
  "criticism_decision_exact {|(None,[2])|} implemented_base_control_decision implemented_base_control
    [(None,[3])] criticism_base_control_pairs"
  unfolding criticism_decision_exact_def
proof (intro allI impI)
  fix q
  assume demand: "q |\<in>| criticism_base_demand {|(None,[2])|} implemented_base_control [(None,[3])]
      criticism_base_control_pairs"
    and base: "fst q |\<in>| {|(None,[2])|}"
  have demanded: "criticism_base_demand {|(None,[2])|} implemented_base_control [(None,[3])]
      criticism_base_control_pairs=
      {|((None,[3]),Finite_Payload []),((None,[3]),Finite_Payload [256]),((None,[2]),Finite_Payload [])|}"
    using criticism_base_control_executed by blast
  have witness: "q=((None,[2]),Finite_Payload [])"
    using demand base unfolding demanded by auto
  show "implemented_base_control_decision q \<longleftrightarrow>
      decode_finite_call_term q\<in>positive_meaning (decode_finite_system implemented_base_control)"
    using implemented_base_control_witness
    by (simp add: witness implemented_base_control_decision_def decode_finite_call_term_def octets_formed_def)
qed

theorem criticism_base_control_meaning:
  "((None,[3]),Payload_Term [])\<in>positive_meaning (decode_finite_system implemented_base_control)"
  "((None,[3]),Payload_Term [256])\<notin>positive_meaning (decode_finite_system implemented_base_control)"
  "(c,c',d,w) |\<in>| criticism_record [(None,[3])] criticism_base_control_pairs
      {|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|} \<longleftrightarrow>
    criticism_paired criticism_base_control_pairs c c' \<and> d\<in>set [(None,[3])] \<and>
    (d,decode_finite_term c)\<in>positive_meaning (decode_finite_system implemented_base_control) \<and>
    (d,decode_finite_term c')\<notin>positive_meaning (decode_finite_system implemented_base_control)"
proof -
  have table: "criticism_base_table {|(None,[2])|} implemented_base_control_decision implemented_base_control
      [(None,[3])] criticism_base_control_pairs=Some {|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|}"
    using criticism_base_control_executed by blast
  have exact: "criticism_exact_table implemented_base_control [(None,[3])] criticism_base_control_pairs
      {|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|}"
    by (rule criticism_base_table_exact_table[OF table criticism_base_control_decided])
  have calls: "((None,[3]),Finite_Payload []) |\<in>| criticism_calls [(None,[3])] criticism_base_control_pairs"
    "((None,[3]),Finite_Payload [256]) |\<in>| criticism_calls [(None,[3])] criticism_base_control_pairs"
    by (simp_all add: criticism_calls_member criticism_sides_def criticism_base_control_pairs_def)
  show "((None,[3]),Payload_Term [])\<in>positive_meaning (decode_finite_system implemented_base_control)"
    using criticism_exact_tableD[OF exact calls(1)] by (simp add: decode_finite_call_term_def)
  show "((None,[3]),Payload_Term [256])\<notin>positive_meaning (decode_finite_system implemented_base_control)"
    using criticism_exact_tableD[OF exact calls(2)] by (simp add: decode_finite_call_term_def)
  show "(c,c',d,w) |\<in>| criticism_record [(None,[3])] criticism_base_control_pairs
      {|((None,[3]),Finite_Payload []),((None,[2]),Finite_Payload [])|} \<longleftrightarrow>
    criticism_paired criticism_base_control_pairs c c' \<and> d\<in>set [(None,[3])] \<and>
    (d,decode_finite_term c)\<in>positive_meaning (decode_finite_system implemented_base_control) \<and>
    (d,decode_finite_term c')\<notin>positive_meaning (decode_finite_system implemented_base_control)"
    by (rule exact_table_record_meaning[OF exact])
qed

end
