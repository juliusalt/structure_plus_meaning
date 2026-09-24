theory Positioned_Native_Evaluation
  imports Keyed_Native_Evaluation Member_Tree_Indexes Inference_Embeddings Shared_Call_Closures
begin

section \<open>A demanded call is compared through its key once and settled by its position\<close>

text \<open>
  Settling a demand asks, for every premise of every rule of its table, whether that premise is
  settled already, and it asks that again in every round. Asked through a key, each question costs
  comparisons of whole terms. The keys of the demand are found once instead: its ordered key
  listing gives every demanded call a position, the rule table is renamed by the map that sends a
  demanded call to its position and every other call to itself, and the rounds then compare
  positions. The closure of the renamed table is the image of the original closure under that map
  (\<open>finite_inference_result_renaming\<close>), so the answer is the original answer; what changes is that
  a call is compared through its key once, when the table is renamed and when the answer is read
  back at the demand, instead of once per premise occurrence per round.
\<close>

definition demand_positions :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> 'a fset \<Rightarrow> ('k,nat) rbt" where
  "demand_positions key D=(let ks=sorted_list_of_fset (fimage key D) in
    RBT.bulkload (zip ks [0..<length ks]))"

subsection \<open>The positions of a demand are an index of the demand\<close>

text \<open>
  The positions of a demand are the index notion's instance with positions as values, not with unit
  values: the evaluation's correctness rests on a demanded key being found at its own position
  (@{text demand_positions_index}, which makes the positioned map injective), and membership alone does
  not carry that. A finite set of keys is the carrier of the relation of each key to its position in the
  canonical listing; its index is the red-black tree of those rows, the tree's instance
  (@{text tree_map_carrier_index}) read through the listing. The demand is the same carrier read through
  a call's key, which distinguishes where it has a left inverse; at the native call key it does by
  @{thm [source] native_call_inverse}.
\<close>

lemma key_positions_carrier_index:
  "carrier_index (\<lambda>K k i. (k,i)\<in>set (zip (sorted_list_of_fset K) [0..<length (sorted_list_of_fset K)]))
    (\<lambda>_. True) (UNIV::'k::linorder set) id
    (\<lambda>K. RBT.bulkload (zip (sorted_list_of_fset K) [0..<length (sorted_list_of_fset K)])) tree_search"
  by (rule carrier_index_through_key[OF tree_map_carrier_index]) (simp_all add: sorted_list_of_fset.rep_eq)

interpretation key_positions_index:
  carrier_index "\<lambda>K k i. (k,i)\<in>set (zip (sorted_list_of_fset K) [0..<length (sorted_list_of_fset K)])"
    "\<lambda>_. True" "UNIV::'k::linorder set" id
    "\<lambda>K. RBT.bulkload (zip (sorted_list_of_fset K) [0..<length (sorted_list_of_fset K)])" tree_search
  by (rule key_positions_carrier_index)

lemma demand_positions_rows:
  "RBT.lookup (demand_positions key D) k=Some i \<longleftrightarrow>
    (k,i)\<in>set (zip (sorted_list_of_fset (fimage key D)) [0..<length (sorted_list_of_fset (fimage key D))])"
  using key_positions_index.query_search[where c="fimage key D" and q=k and v=i] by (simp add: demand_positions_def Let_def)

text \<open>
  The listing is distinct, so the rows are the graph of the map of the zip, and the lookup is that map.
\<close>

lemma demand_positions_lookup:
  "RBT.lookup (demand_positions key D)=
    map_of (zip (sorted_list_of_fset (fimage key D))
      [0..<length (sorted_list_of_fset (fimage key D))])"
proof (rule ext)
  fix k
  let ?Z="zip (sorted_list_of_fset (fimage key D)) [0..<length (sorted_list_of_fset (fimage key D))]"
  have keys: "distinct (map fst ?Z)" by simp
  have same: "RBT.lookup (demand_positions key D) k=Some i \<longleftrightarrow> map_of ?Z k=Some i" for i
    using demand_positions_rows[of key D k i] map_of_is_SomeI[OF keys, of k i] map_of_SomeD[of ?Z k i]
    by blast
  show "RBT.lookup (demand_positions key D) k=map_of ?Z k"
  proof (cases "map_of ?Z k")
    case None
    have "RBT.lookup (demand_positions key D) k=None"
    proof (cases "RBT.lookup (demand_positions key D) k")
      case (Some j)
      with same[of j] None show ?thesis by simp
    qed
    with None show ?thesis by (simp only:)
  next
    case (Some j)
    then show ?thesis using same[of j] by simp
  qed
qed

lemma zip_positions_member: "(\<exists>i. (k,i)\<in>set (zip xs [0..<length xs])) \<longleftrightarrow> k\<in>set xs"
proof
  assume "\<exists>i. (k,i)\<in>set (zip xs [0..<length xs])"
  then show "k\<in>set xs" by (auto dest: set_zip_leftD)
next
  assume "k\<in>set xs"
  then obtain n where n: "n<length xs" "xs!n=k" by (auto simp: in_set_conv_nth)
  have "(xs!n,[0..<length xs]!n)\<in>set (zip xs [0..<length xs])" using n(1) by (force simp: set_zip)
  then show "\<exists>i. (k,i)\<in>set (zip xs [0..<length xs])" using n(2) by blast
qed

lemma demand_positions_member:
  "RBT.lookup (demand_positions key D) k\<noteq>None \<longleftrightarrow> k\<in>fset (fimage key D)"
proof -
  let ?ks="sorted_list_of_fset (fimage key D)"
  have "RBT.lookup (demand_positions key D) k\<noteq>None \<longleftrightarrow> (\<exists>i. (k,i)\<in>set (zip ?ks [0..<length ?ks]))"
    using key_positions_index.lookup_found[where look=RBT.lookup and c="fimage key D" and q=k]
    by (simp add: demand_positions_def Let_def)
  also have "\<dots> \<longleftrightarrow> k\<in>set ?ks" by (rule zip_positions_member)
  finally show ?thesis by simp
qed

lemma demand_positions_index:
  assumes lookup: "RBT.lookup (demand_positions key D) k=Some i"
  shows "sorted_list_of_fset (fimage key D)!i=k"
proof -
  have "(k,i)\<in>set (zip (sorted_list_of_fset (fimage key D))
      [0..<length (sorted_list_of_fset (fimage key D))])"
    using lookup by (simp only: demand_positions_rows)
  then show ?thesis by (auto simp: in_set_zip)
qed

lemma demand_positions_carrier_index:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "carrier_index (\<lambda>D q i. (key q,i)\<in>set (zip (sorted_list_of_fset (fimage key D))
      [0..<length (sorted_list_of_fset (fimage key D))])) (\<lambda>_. True) UNIV key (demand_positions key) tree_search"
proof -
  have positions: "demand_positions key=(\<lambda>D. RBT.bulkload (zip (sorted_list_of_fset (fimage key D))
      [0..<length (sorted_list_of_fset (fimage key D))]))"
    by (rule ext) (simp only: demand_positions_def Let_def)
  show ?thesis unfolding positions
  proof (rule carrier_index_through_key[OF key_positions_carrier_index])
    show "inj_on key UNIV" by (rule distinguishes_by_left_inverse[where unkey=unkey]) (rule inverse)
    fix D k and i :: nat
    show "(k,i)\<in>set (zip (sorted_list_of_fset (fimage key D)) [0..<length (sorted_list_of_fset (fimage key D))]) \<longleftrightarrow>
        (\<exists>q\<in>UNIV. key q=k \<and> (key q,i)\<in>set (zip (sorted_list_of_fset (fimage key D))
          [0..<length (sorted_list_of_fset (fimage key D))]))"
    proof
      assume row: "(k,i)\<in>set (zip (sorted_list_of_fset (fimage key D)) [0..<length (sorted_list_of_fset (fimage key D))])"
      then have "k\<in>set (sorted_list_of_fset (fimage key D))" by (rule set_zip_leftD)
      then obtain q where "k=key q" by auto
      then show "\<exists>q\<in>UNIV. key q=k \<and> (key q,i)\<in>set (zip (sorted_list_of_fset (fimage key D))
          [0..<length (sorted_list_of_fset (fimage key D))])" using row by blast
    qed blast
  qed simp
qed

interpretation native_demand_positions:
  carrier_index "\<lambda>D q i. (native_call_key q,i)\<in>set (zip (sorted_list_of_fset (fimage native_call_key D))
      [0..<length (sorted_list_of_fset (fimage native_call_key D))])" "\<lambda>_. True" UNIV native_call_key
    "demand_positions native_call_key" tree_search
  by (rule demand_positions_carrier_index[OF native_call_inverse])

lemma demand_positions_members_subset:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "fBall B (\<lambda>q. RBT.lookup (demand_positions key A) (key q)\<noteq>None) \<longleftrightarrow> B |\<subseteq>| A"
proof -
  have injective: "inj key" by (rule distinguishes_by_left_inverse[where unkey=unkey]) (rule inverse)
  let ?ks="sorted_list_of_fset (fimage key A)"
  have "(\<forall>q\<in>fset B. RBT.lookup (demand_positions key A) (key q)\<noteq>None) \<longleftrightarrow>
      (\<forall>q\<in>fset B. \<exists>i. (key q,i)\<in>set (zip ?ks [0..<length ?ks]))"
    by (rule carrier_index.lookup_queries_found[OF demand_positions_carrier_index[OF inverse], where look=RBT.lookup])
      simp_all
  also have "\<dots> \<longleftrightarrow> (\<forall>q\<in>fset B. key q\<in>set ?ks)" by (simp only: zip_positions_member)
  finally show ?thesis by (auto simp: less_eq_fset.rep_eq fimage.rep_eq inj_image_mem_iff[OF injective])
qed

text \<open>
  A demanded key receives its own position and an undemanded one keeps itself, in the second
  component that the demanded case leaves empty. The map is injective wherever the key is:
  distinct demanded keys stand at distinct positions of the listing, an undemanded key is
  separated from every demanded one by that component, and two undemanded keys are the keys
  themselves. Under the guard below every call the table mentions is demanded, so the rounds see
  positions only; the other branch is what makes the map injective on the whole type, which is
  what the renaming asks for.
\<close>

definition positioned_key :: "('k::linorder,nat) rbt \<Rightarrow> 'k \<Rightarrow> nat\<times>'k option" where
  "positioned_key N k=(case RBT.lookup N k of Some i \<Rightarrow> (i,None) | None \<Rightarrow> (0,Some k))"

definition positioned_call :: "('a \<Rightarrow> 'k::linorder) \<Rightarrow> ('k,nat) rbt \<Rightarrow> 'a \<Rightarrow> nat\<times>'k option" where
  "positioned_call key N q=positioned_key N (key q)"

lemma positioned_key_injective: "inj (positioned_key (demand_positions key D))"
proof (rule injI)
  fix k k'
  assume equal: "positioned_key (demand_positions key D) k=positioned_key (demand_positions key D) k'"
  consider (both) i j where "RBT.lookup (demand_positions key D) k=Some i"
      "RBT.lookup (demand_positions key D) k'=Some j"
    | (neither) "RBT.lookup (demand_positions key D) k=None"
      "RBT.lookup (demand_positions key D) k'=None"
    | (mixed) "RBT.lookup (demand_positions key D) k=None \<and> RBT.lookup (demand_positions key D) k'\<noteq>None
      \<or> RBT.lookup (demand_positions key D) k\<noteq>None \<and> RBT.lookup (demand_positions key D) k'=None"
    by (cases "RBT.lookup (demand_positions key D) k";
      cases "RBT.lookup (demand_positions key D) k'") auto
  then show "k=k'"
  proof cases
    case (both i j)
    then have "i=j" using equal by (simp add: positioned_key_def)
    then show ?thesis
      using demand_positions_index[OF both(1)] demand_positions_index[OF both(2)] by simp
  next
    case neither
    then show ?thesis using equal by (simp add: positioned_key_def)
  next
    case mixed
    then show ?thesis using equal by (auto simp: positioned_key_def split: option.splits)
  qed
qed

lemma positioned_call_injective:
  assumes injective: "inj key"
  shows "inj (positioned_call key (demand_positions key D))"
proof (rule injI)
  fix q q'
  assume "positioned_call key (demand_positions key D) q=positioned_call key (demand_positions key D) q'"
  then have "positioned_key (demand_positions key D) (key q)=
      positioned_key (demand_positions key D) (key q')"
    by (simp only: positioned_call_def)
  then have "key q=key q'" by (rule injD[OF positioned_key_injective])
  then show "q=q'" by (rule injD[OF injective])
qed

section \<open>Every rule of a program's table has a functional premise family\<close>

lemma finite_program_rule_table_formed: "finite_inference_formed (finite_program_rule_table P D)"
  unfolding finite_inference_formed_def
proof (rule fBallI)
  fix x assume member: "x |\<in>| finite_program_rule_table P D"
  obtain q G where shape: "x=(q,G)" by (cases x)
  have "single_valued (fset G)"
    by (rule finite_program_rule_functional[OF member[unfolded shape]])
  then show "case x of (a,H) \<Rightarrow> finite_premise_functional H"
    by (simp only: shape case_prod_conv finite_premise_functional_exact)
qed

section \<open>The evaluation of a demand over the positions of its calls\<close>

definition positioned_program_evaluation where
  "positioned_program_evaluation key P D=(let N=demand_positions key D;
      F=finite_program_rule_table P D in
    if finite_system_formed P \<and> finite_program_head_covered P D \<and>
      fBall F (\<lambda>(q,H). fBall (fimage snd H) (\<lambda>r. RBT.lookup N (key r)\<noteq>None))
    then map_option (\<lambda>A. let T=ordered_member_tree A in
      ffilter (\<lambda>q. RBT.lookup T (positioned_call key N q)\<noteq>None) D)
      (keyed_inference_settled id id (finite_embedded_inferences (positioned_call key N) F) {||})
    else None)"

theorem positioned_program_evaluation_exact:
  assumes inverse: "\<And>x. unkey (key x)=x"
  shows "positioned_program_evaluation key P D=finite_program_evaluation P D"
proof -
  have injective: "inj key"
  proof (rule injI)
    fix x y assume "key x=key y"
    then have "unkey (key x)=unkey (key y)" by simp
    then show "x=y" by (simp only: inverse)
  qed
  let ?F="finite_program_rule_table P D"
  let ?N="demand_positions key D"
  let ?g="positioned_call key ?N"
  have ginj: "inj ?g" by (rule positioned_call_injective[OF injective])
  have formed: "finite_inference_formed ?F" by (rule finite_program_rule_table_formed)
  have closed: "fBall ?F (\<lambda>(q,H). fBall (fimage snd H) (\<lambda>r. RBT.lookup ?N (key r)\<noteq>None)) \<longleftrightarrow>
      finite_program_demand_closed P D"
    by (simp only: finite_program_demand_closed_def demand_positions_members_subset[OF inverse])
  have identity: "\<And>x. id (id x)=x" by simp
  obtain A where settled: "keyed_inference_settled id id (finite_embedded_inferences ?g ?F) {||}=Some A"
    and result: "fset A=finite_inference_result (finite_embedded_inferences ?g ?F) {||}"
    by (rule keyed_inference_settled_result[where key="id" and unkey="id", OF identity])
  have image: "finite_inference_result (finite_embedded_inferences ?g ?F) {||}=
      ?g ` finite_inference_result ?F {||}"
    using finite_inference_result_renaming[OF ginj formed, of "{||}"] by simp
  have selected: "ffilter (\<lambda>q. RBT.lookup (ordered_member_tree A) (?g q)\<noteq>None) D=
      ffilter (\<lambda>q. q\<in>finite_inference_result ?F {||}) D"
  proof (rule fset_eqI)
    fix q
    show "q |\<in>| ffilter (\<lambda>q. RBT.lookup (ordered_member_tree A) (?g q)\<noteq>None) D \<longleftrightarrow>
        q |\<in>| ffilter (\<lambda>q. q\<in>finite_inference_result ?F {||}) D"
      by (simp only: ffmember_filter member_tree_lookup result image
        inj_image_mem_iff[OF ginj])
  qed
  show ?thesis
    by (simp only: positioned_program_evaluation_def finite_program_evaluation_def Let_def closed
      finite_program_evaluation_ready_def settled option.map selected)
qed

section \<open>The stage, the reference and the evidence evaluate over positions\<close>

text \<open>
  The three operations that settle a demand without retaining its rounds take the positioned
  evaluation. The certificate path keeps the keyed history: its value is every round's state with
  the applications enabled there, and the renaming states the closure, not a correspondence of the
  rounds, so positioning it would need a contract the library does not have.
\<close>

declare finite_native_generation_keyed_code [code del]
declare workflow_stage_reference_keyed_code [code del]
declare workflow_stage_evidence_keyed_code [code del]

lemma finite_native_generation_positioned_code [code]:
  "finite_native_generation E u r x=(case finite_native_source E u r of None \<Rightarrow> None
    | Some P \<Rightarrow> let D=finite_program_term_demand P {|x|} in
      map_option (\<lambda>A. (P,D,A,finite_program_generation_rows P
        (finite_native_seed_rows P x A))) (positioned_program_evaluation native_call_key P D))"
  by (simp only: finite_native_generation_keyed_code
    keyed_program_evaluation_exact[OF native_call_inverse]
    positioned_program_evaluation_exact[OF native_call_inverse])

lemma workflow_stage_reference_positioned_code [code]:
  "workflow_stage_reference S x=(case workflow_scope_result S x of None \<Rightarrow> None
    | Some ys \<Rightarrow> (case finite_native_source (workflow_source S)
        (workflow_source_use S) (workflow_source_root S) of None \<Rightarrow> None
      | Some P \<Rightarrow> if workflow_entry S |\<notin>| finite_system_definitions P then None else
        let D=keyed_call_closure native_call_key native_call_unkey P
          (fimage (Pair (workflow_entry S)) (fset_of_list (map (Finite_Pair x) ys))) in
        map_option (\<lambda>A. filter (\<lambda>y. (workflow_entry S,Finite_Pair x y) |\<in>| A) ys)
          (positioned_program_evaluation native_call_key P D)))"
  by (simp only: workflow_stage_reference_keyed_code
    keyed_program_evaluation_exact[OF native_call_inverse]
    positioned_program_evaluation_exact[OF native_call_inverse])

lemma workflow_stage_evidence_positioned_code [code]:
  "workflow_stage_evidence S input result=(case result of (P,D,A,T,ys) \<Rightarrow>
    (case workflow_scope_result S input of None \<Rightarrow> False | Some scope \<Rightarrow>
      finite_native_source (workflow_source S) (workflow_source_use S) (workflow_source_root S)=Some P \<and>
      workflow_entry S |\<in>| finite_system_definitions P \<and>
      keyed_equal native_call_key D (keyed_call_closure native_call_key native_call_unkey P
        (fimage (Pair (workflow_entry S)) (fset_of_list (map (Finite_Pair input) scope)))) \<and>
      positioned_program_evaluation native_call_key P D=Some A \<and>
      keyed_equal native_call_key (fimage fst T) A \<and> finite_inspection_rows_hold (finite_proof_inspection P T) \<and>
      ys=filter (\<lambda>y. (workflow_entry S,Finite_Pair input y) |\<in>| A) scope))"
  by (simp only: workflow_stage_evidence_keyed_code
    keyed_program_evaluation_exact[OF native_call_inverse]
    positioned_program_evaluation_exact[OF native_call_inverse])

text \<open>
  Each operation computes its original result: the positioned closure is the image of the original
  closure under an injective map, and the answer is read back at the demand through that same map.
  Only the values the rounds compare change.
\<close>

end
