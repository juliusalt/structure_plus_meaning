theory Keyed_Native_Evaluation
  imports Keyed_Finite_Sets Ordered_Finite_Terms Factor_Workflow_Execution_Sharing
    Factor_Finite_Application_Proofs Factor_Finite_Native_Proof_Construction
begin

section \<open>Inference steps look up settled calls through their keys\<close>

text \<open>
  Each inference step asks, for every rule, whether its premises are settled, and then joins
  the new heads to the settled set and compares the result with its predecessor. With the
  settled calls indexed by an ordered key once per step, each question is a lookup; the join
  and the comparison use the keyed listings. Every step returns the original step's set, so the
  history is the original history.
\<close>

definition keyed_inference_enabled ::
    "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('a\<times>('i\<times>'a) fset) fset \<Rightarrow> 'a fset \<Rightarrow> ('a\<times>('i\<times>'a) fset) fset" where
  "keyed_inference_enabled key F X=(let M=ordered_member_tree (fimage key X) in
    ffilter (\<lambda>(a,H). finite_premise_functional H \<and>
      fBall (fimage snd H) (\<lambda>q. RBT.lookup M (key q)\<noteq>None)) F)"

lemma keyed_inference_enabled_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_inference_enabled key F X=finite_inference_enabled F (fset X)"
  by (simp only: keyed_inference_enabled_def finite_inference_enabled_def Let_def
    keyed_members_subset[OF inverse] less_eq_fset.rep_eq)

definition keyed_inference_next ::
    "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('a\<times>('i\<times>'a) fset) fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset" where
  "keyed_inference_next key unkey F K X=keyed_union key unkey K (fimage fst (keyed_inference_enabled key F X))"

lemma keyed_inference_next_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_inference_next key unkey F K=finite_inference_next F K"
  by (rule ext) (simp only: keyed_inference_next_def keyed_union_exact[OF inverse]
    keyed_inference_enabled_exact[OF inverse] finite_inference_next_def)

definition keyed_inference_history ::
    "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('a\<times>('i\<times>'a) fset) fset \<Rightarrow> 'a fset \<Rightarrow> _" where
  "keyed_inference_history key unkey F K=while_history
    (\<lambda>X. \<not>keyed_equal key (keyed_inference_next key unkey F K X) X)
    (keyed_inference_next key unkey F K) {||}"

lemma keyed_inference_history_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_inference_history key unkey F K=finite_inference_history F K"
proof -
  have test: "(\<lambda>X. \<not>keyed_equal key (finite_inference_next F K X) X)=
      (\<lambda>X. finite_inference_next F K X\<noteq>X)"
    by (rule ext) (simp only: keyed_equal_exact[OF inverse])
  show ?thesis
    by (simp only: keyed_inference_history_def finite_inference_history_def
      keyed_inference_next_exact[OF inverse] test)
qed

definition keyed_inference_witnesses where
  "keyed_inference_witnesses key project F X=(let M=ordered_member_tree (fimage key X) in
    ffilter (\<lambda>w. case project w of (a,H) \<Rightarrow> finite_premise_functional H \<and>
      fBall (fimage snd H) (\<lambda>q. RBT.lookup M (key q)\<noteq>None)) F)"

lemma keyed_inference_witnesses_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_inference_witnesses key project F X=finite_inference_witnesses project F X"
proof (rule fset_eqI)
  fix w
  show "w |\<in>| keyed_inference_witnesses key project F X \<longleftrightarrow> w |\<in>| finite_inference_witnesses project F X"
    by (simp only: keyed_inference_witnesses_def Let_def ffmember_filter finite_inference_witness_member
      keyed_members_subset[OF inverse])
qed

definition keyed_labelled_history where
  "keyed_labelled_history key unkey project F K=map_option (\<lambda>(A,Xs).
    (A,map (\<lambda>X. (X,keyed_inference_witnesses key project F X)) Xs))
      (keyed_inference_history key unkey (fimage project F) K)"

lemma keyed_labelled_history_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_labelled_history key unkey project F K=finite_inference_labelled_history project F K"
  by (simp only: keyed_labelled_history_def finite_inference_labelled_history_def
    keyed_inference_history_exact[OF inverse] keyed_inference_witnesses_exact[OF inverse])

section \<open>The settled calls are the final state of the keyed steps\<close>

definition keyed_inference_settled ::
    "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('k \<Rightarrow> 'a) \<Rightarrow> ('a\<times>('i\<times>'a) fset) fset \<Rightarrow> 'a fset \<Rightarrow> 'a fset option" where
  "keyed_inference_settled key unkey F K=while_option
    (\<lambda>X. \<not>keyed_equal key (keyed_inference_next key unkey F K X) X)
    (keyed_inference_next key unkey F K) {||}"

lemma keyed_inference_settled_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_inference_settled key unkey F K=map_option fst (finite_inference_history F K)"
proof -
  have "keyed_inference_settled key unkey F K=map_option fst (keyed_inference_history key unkey F K)"
    by (simp only: keyed_inference_history_def keyed_inference_settled_def while_history_projection)
  also have "\<dots>=map_option fst (finite_inference_history F K)"
    by (simp only: keyed_inference_history_exact[OF inverse])
  finally show ?thesis .
qed

lemma keyed_inference_settled_result:
  assumes inverse: "\<And>x. unkey (key x)=x"
  obtains A where "keyed_inference_settled key unkey F K=Some A" "fset A=finite_inference_result F K"
proof -
  obtain A Xs where history: "finite_inference_history F K=Some (A,Xs)"
    using finite_inference_history_total by blast
  have "fset A=inference_closure (finite_inference_rules F) (fset K)"
    by (rule finite_inference_history_correct(1)[OF history])
  then have result: "fset A=finite_inference_result F K" by (simp only: finite_inference_result_exact)
  have "keyed_inference_settled key unkey F K=Some A"
    by (simp add: keyed_inference_settled_exact[OF inverse] history)
  then show thesis using result by (rule that)
qed

section \<open>A program history reads its demand through the same keys\<close>

definition keyed_program_history where
  "keyed_program_history key unkey P D=(let W=finite_program_applications P D; M=ordered_member_tree (fimage key D) in
    if finite_system_formed P \<and> finite_program_head_covered P D \<and>
      fBall (fimage finite_program_application_rule W)
        (\<lambda>(q,H). fBall (fimage snd H) (\<lambda>r. RBT.lookup M (key r)\<noteq>None))
    then keyed_labelled_history key unkey finite_program_application_rule W {||} else None)"

lemma keyed_program_history_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_program_history key unkey P D=finite_program_history P D"
proof -
  have closed: "fBall (fimage finite_program_application_rule (finite_program_applications P D))
      (\<lambda>(q,H). fBall (fimage snd H) (\<lambda>r. RBT.lookup (ordered_member_tree (fimage key D)) (key r)\<noteq>None)) \<longleftrightarrow>
    finite_program_demand_closed P D"
    by (simp only: finite_program_demand_closed_def finite_program_rule_table_def
      keyed_members_subset[OF inverse])
  show ?thesis
    by (simp only: keyed_program_history_def finite_program_history_def Let_def closed
      finite_program_evaluation_ready_def keyed_labelled_history_exact[OF inverse])
qed

definition keyed_program_proofs where
  "keyed_program_proofs key unkey P D=map_option (\<lambda>(A,Hs).
    (A,fold (\<lambda>(X,W) T. finite_application_proofs W T) Hs {||})) (keyed_program_history key unkey P D)"

lemma keyed_program_proofs_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_program_proofs key unkey P D=finite_program_proofs P D"
  by (simp only: keyed_program_proofs_def finite_program_proofs_def keyed_program_history_exact[OF inverse])

section \<open>A program evaluation settles its demand through the same keys\<close>

definition keyed_program_evaluation where
  "keyed_program_evaluation key unkey P D=(let F=finite_program_rule_table P D; M=ordered_member_tree (fimage key D) in
    if finite_system_formed P \<and> finite_program_head_covered P D \<and>
      fBall F (\<lambda>(q,H). fBall (fimage snd H) (\<lambda>r. RBT.lookup M (key r)\<noteq>None))
    then map_option (\<lambda>A. let T=ordered_member_tree (fimage key A) in
      ffilter (\<lambda>q. RBT.lookup T (key q)\<noteq>None) D) (keyed_inference_settled key unkey F {||})
    else None)"

lemma keyed_program_evaluation_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "keyed_program_evaluation key unkey P D=finite_program_evaluation P D"
proof -
  have closed: "fBall (finite_program_rule_table P D)
      (\<lambda>(q,H). fBall (fimage snd H) (\<lambda>r. RBT.lookup (ordered_member_tree (fimage key D)) (key r)\<noteq>None)) \<longleftrightarrow>
    finite_program_demand_closed P D"
    by (simp only: finite_program_demand_closed_def keyed_members_subset[OF inverse])
  obtain A where settled: "keyed_inference_settled key unkey (finite_program_rule_table P D) {||}=Some A"
    and result: "fset A=finite_inference_result (finite_program_rule_table P D) {||}"
    by (rule keyed_inference_settled_result[OF inverse])
  have selected: "ffilter (\<lambda>q. RBT.lookup (ordered_member_tree (fimage key A)) (key q)\<noteq>None) D=
      ffilter (\<lambda>q. q\<in>finite_inference_result (finite_program_rule_table P D) {||}) D"
  proof (rule fset_eqI)
    fix q
    show "q |\<in>| ffilter (\<lambda>q. RBT.lookup (ordered_member_tree (fimage key A)) (key q)\<noteq>None) D \<longleftrightarrow>
        q |\<in>| ffilter (\<lambda>q. q\<in>finite_inference_result (finite_program_rule_table P D) {||}) D"
      by (simp only: ffmember_filter keyed_member_lookup[OF inverse] result[symmetric])
  qed
  show ?thesis
    by (simp only: keyed_program_evaluation_def finite_program_evaluation_def Let_def closed
      finite_program_evaluation_ready_def settled option.map selected)
qed

section \<open>Workflow stages evaluate, check and generate through keyed calls\<close>

text \<open>
  The calls of a native program are its definition sites paired with terms, and the ordered
  presentation of a term with the site is a key whose left inverse recovers the call. The
  equations below restate the source-shared equations of each workflow operation with the
  keyed evaluation, history and comparisons; every result is the original result.
\<close>

definition native_call_key :: "local_address option definition_site\<times>finite_factor_term \<Rightarrow>
    local_address option definition_site\<times>ordered_factor_term" where
  "native_call_key q=(fst q,Ordered_Factor_Term (snd q))"

definition native_call_unkey :: "local_address option definition_site\<times>ordered_factor_term \<Rightarrow>
    local_address option definition_site\<times>finite_factor_term" where
  "native_call_unkey k=(fst k,unordered_factor_term (snd k))"

lemma native_call_inverse: "native_call_unkey (native_call_key q)=q"
  by (simp add: native_call_key_def native_call_unkey_def)

lemma finite_native_generation_keyed_code [code]:
  "finite_native_generation E u r x=(case finite_native_source E u r of None \<Rightarrow> None
    | Some P \<Rightarrow> let D=finite_program_term_demand P {|x|} in
      map_option (\<lambda>A. (P,D,A,finite_program_generation_rows P
        (finite_native_seed_rows P x A))) (keyed_program_evaluation native_call_key native_call_unkey P D))"
  by (simp only: finite_native_generation_source_shared_code keyed_program_evaluation_exact[OF native_call_inverse])

lemma evaluate_workflow_stage_keyed_code [code]:
  "evaluate_workflow_stage S x=(case workflow_scope_result S x of None \<Rightarrow> None
    | Some ys \<Rightarrow> (case finite_native_source (workflow_source S)
        (workflow_source_use S) (workflow_source_root S) of None \<Rightarrow> None
      | Some P \<Rightarrow> if workflow_entry S |\<notin>| finite_system_definitions P then None else
        let D=finite_program_call_closure P
          (fimage (Pair (workflow_entry S)) (fset_of_list (map (Finite_Pair x) ys))) in
        map_option (\<lambda>(A,T). (P,D,A,T,
          filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A) ys))
          (keyed_program_proofs native_call_key native_call_unkey P D)))"
  by (simp only: evaluate_workflow_stage_source_shared_code keyed_program_proofs_exact[OF native_call_inverse])

lemma workflow_stage_reference_keyed_code [code]:
  "workflow_stage_reference S x=(case workflow_scope_result S x of None \<Rightarrow> None
    | Some ys \<Rightarrow> (case finite_native_source (workflow_source S)
        (workflow_source_use S) (workflow_source_root S) of None \<Rightarrow> None
      | Some P \<Rightarrow> if workflow_entry S |\<notin>| finite_system_definitions P then None else
        let D=finite_program_call_closure P
          (fimage (Pair (workflow_entry S)) (fset_of_list (map (Finite_Pair x) ys))) in
        map_option (\<lambda>A. filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A) ys)
          (keyed_program_evaluation native_call_key native_call_unkey P D)))"
  by (simp only: workflow_stage_reference_source_shared_code keyed_program_evaluation_exact[OF native_call_inverse])

text \<open>
  The evidence of a stage is checked against an independent evaluation of the original
  source. That evaluation settles the demand through the same keyed steps, and the checked
  demand and answers are compared through their keyed listings; every compared value and the
  truth of the evidence are unchanged.
\<close>

lemma workflow_stage_evidence_keyed_code [code]:
  "workflow_stage_evidence S input result=(case result of (P,D,A,T,ys) \<Rightarrow>
    (case workflow_scope_result S input of None \<Rightarrow> False | Some scope \<Rightarrow>
      finite_native_source (workflow_source S) (workflow_source_use S) (workflow_source_root S)=Some P \<and>
      workflow_entry S |\<in>| finite_system_definitions P \<and>
      keyed_equal native_call_key D (finite_program_call_closure P
        (fimage (Pair (workflow_entry S)) (fset_of_list (map (Finite_Pair input) scope)))) \<and>
      keyed_program_evaluation native_call_key native_call_unkey P D=Some A \<and>
      keyed_equal native_call_key (fimage fst T) A \<and> finite_inspection_rows_hold (finite_proof_inspection P T) \<and>
      ys=filter (\<lambda>y. (workflow_entry S,Finite_Pair input y) |\<in>| A) scope))"
  by (simp only: workflow_stage_evidence_source_shared_code keyed_program_evaluation_exact[OF native_call_inverse]
    keyed_equal_exact[OF native_call_inverse])

text \<open>
  Each operation computes its original result: the keyed history is the original history, the
  keyed settlement is the original closure, and the keyed comparisons decide the original
  equalities. Only the listings and lookups that compute them change.
\<close>

end
