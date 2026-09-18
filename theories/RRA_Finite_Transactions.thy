theory RRA_Finite_Transactions
  imports RRA_Replacement RRA_Finite_Generation_Projections Finite_Singleton_Selection
begin

section \<open>A finite snapshot presents the snapshot of its decoded generations\<close>

text \<open>
  A selection snapshot, its loci, its lookup and a structural transaction are defined over
  exact cores, whose artifacts are not executable values. Their finite presentations are the
  finite generations that decode to those cores; every operation below is stated on them and
  proved to be the original operation on the decoded values, so a transaction is executed
  without being redefined.
\<close>

type_synonym finite_snapshot = "finite_generation fset"

definition decode_finite_snapshot :: "finite_snapshot \<Rightarrow> selection_snapshot" where
  "decode_finite_snapshot S=fimage decode_finite_generation S"

definition finite_snapshot_loci :: "finite_snapshot \<Rightarrow> finite_exact_target fset" where
  "finite_snapshot_loci S=fimage generation_locus S"

lemma decode_finite_target_inj: "inj decode_finite_target"
  by (simp add: inj_def)

lemma decode_finite_snapshot_member [simp]:
  "decode_finite_generation G\<in>fset (decode_finite_snapshot S) \<longleftrightarrow> G\<in>fset S"
  by (simp add: decode_finite_snapshot_def fimage.rep_eq inj_image_mem_iff[OF decode_finite_generation_inj])

lemma decode_finite_snapshot_loci:
  "snapshot_loci (decode_finite_snapshot S)=decode_finite_target ` fset (finite_snapshot_loci S)"
  by (simp add: snapshot_loci_def decode_finite_snapshot_def finite_snapshot_loci_def
    fimage.rep_eq image_image decode_finite_generation_selectors)

lemma decode_finite_snapshot_locus [simp]:
  "decode_finite_target l\<in>snapshot_loci (decode_finite_snapshot S) \<longleftrightarrow> l\<in>fset (finite_snapshot_loci S)"
  by (simp add: decode_finite_snapshot_loci inj_image_mem_iff[OF decode_finite_target_inj])

section \<open>Formation: formed generations, at most one at each locus\<close>

definition finite_snapshot_formed :: "finite_snapshot \<Rightarrow> bool" where
  "finite_snapshot_formed S \<longleftrightarrow> fBall S finite_generation_formed \<and>
    fcard (finite_snapshot_loci S)=fcard S"

lemma finite_snapshot_loci_injective:
  "fcard (finite_snapshot_loci S)=fcard S \<longleftrightarrow> inj_on generation_locus (fset S)"
  by (simp add: finite_snapshot_loci_def fcard.rep_eq fimage.rep_eq inj_on_iff_eq_card[OF finite_fset])

lemma decode_finite_snapshot_injective:
  "inj_on generation_locus (fset (decode_finite_snapshot S)) \<longleftrightarrow> inj_on generation_locus (fset S)"
proof -
  have composed: "generation_locus \<circ> decode_finite_generation=decode_finite_target \<circ> generation_locus"
    by (simp add: fun_eq_iff decode_finite_generation_selectors)
  have "inj_on generation_locus (fset (decode_finite_snapshot S)) \<longleftrightarrow>
      inj_on (generation_locus \<circ> decode_finite_generation) (fset S)"
    by (simp add: decode_finite_snapshot_def fimage.rep_eq
      comp_inj_on_iff[OF inj_on_subset[OF decode_finite_generation_inj subset_UNIV]])
  also have "\<dots>\<longleftrightarrow>inj_on generation_locus (fset S)"
    by (simp add: composed inj_on_def)
  finally show ?thesis .
qed

theorem finite_snapshot_formed_correct:
  "finite_snapshot_formed S \<longleftrightarrow> snapshot_formed (decode_finite_snapshot S)"
proof -
  have generations: "selection_formed (decode_finite_snapshot S) \<longleftrightarrow> fBall S finite_generation_formed"
    by (auto simp: selection_formed_def decode_finite_snapshot_def fimage.rep_eq
      finite_generation_formed_correct)
  show ?thesis
    by (simp only: finite_snapshot_formed_def snapshot_formed_def generations
      finite_snapshot_loci_injective decode_finite_snapshot_injective)
qed

section \<open>Lookup reads the one generation selected at a locus\<close>

definition finite_snapshot_lookup :: "finite_snapshot \<Rightarrow> finite_exact_target \<Rightarrow> finite_generation option" where
  "finite_snapshot_lookup S l=finite_singleton_option (ffilter (\<lambda>G. generation_locus G=l) S)"

lemma finite_snapshot_lookup_some_member:
  assumes found: "finite_snapshot_lookup S l=Some G"
  shows "G\<in>fset S \<and> generation_locus G=l"
proof -
  have "ffilter (\<lambda>G. generation_locus G=l) S={|G|}"
    using found by (simp only: finite_snapshot_lookup_def finite_singleton_option_some)
  then have "G |\<in>| ffilter (\<lambda>G. generation_locus G=l) S" by simp
  then show ?thesis by simp
qed

lemma finite_snapshot_lookup_formed:
  assumes formed: "finite_snapshot_formed S"
  shows "finite_snapshot_lookup S l=Some G \<longleftrightarrow> G\<in>fset S \<and> generation_locus G=l"
proof -
  have injective: "inj_on generation_locus (fset S)"
    using formed by (simp add: finite_snapshot_formed_def finite_snapshot_loci_injective)
  have "ffilter (\<lambda>G. generation_locus G=l) S={|G|} \<longleftrightarrow> G\<in>fset S \<and> generation_locus G=l"
  proof
    assume "ffilter (\<lambda>G. generation_locus G=l) S={|G|}"
    then have "G |\<in>| ffilter (\<lambda>G. generation_locus G=l) S" by simp
    then show "G\<in>fset S \<and> generation_locus G=l" by simp
  next
    assume member: "G\<in>fset S \<and> generation_locus G=l"
    show "ffilter (\<lambda>G. generation_locus G=l) S={|G|}"
    proof (rule fset_eqI)
      fix x
      show "x |\<in>| ffilter (\<lambda>G. generation_locus G=l) S \<longleftrightarrow> x |\<in>| {|G|}"
        using member injective by (auto simp: inj_on_def)
    qed
  qed
  then show ?thesis by (simp only: finite_snapshot_lookup_def finite_singleton_option_some)
qed

lemma finite_snapshot_lookup_none:
  assumes formed: "finite_snapshot_formed S"
  shows "finite_snapshot_lookup S l=None \<longleftrightarrow> l\<notin>fset (finite_snapshot_loci S)"
proof
  assume none: "finite_snapshot_lookup S l=None"
  show "l\<notin>fset (finite_snapshot_loci S)"
  proof
    assume "l\<in>fset (finite_snapshot_loci S)"
    then obtain G where member: "G\<in>fset S" "generation_locus G=l"
      by (auto simp: finite_snapshot_loci_def fimage.rep_eq)
    then have "finite_snapshot_lookup S l=Some G"
      by (simp add: finite_snapshot_lookup_formed[OF formed])
    then show False using none by simp
  qed
next
  assume absent: "l\<notin>fset (finite_snapshot_loci S)"
  have "ffilter (\<lambda>G. generation_locus G=l) S={||}"
    using absent by (auto simp: finite_snapshot_loci_def fimage.rep_eq fset_eq_iff)
  then show "finite_snapshot_lookup S l=None"
    by (simp add: finite_snapshot_lookup_def finite_singleton_option_def set_singleton_option_def)
qed

theorem finite_snapshot_lookup_exact:
  assumes formed: "finite_snapshot_formed S"
  shows "snapshot_lookup (decode_finite_snapshot S) (decode_finite_target l)=
    map_option decode_finite_generation (finite_snapshot_lookup S l)"
proof (cases "finite_snapshot_lookup S l")
  case None
  then have absent: "decode_finite_target l\<notin>snapshot_loci (decode_finite_snapshot S)"
    by (simp add: finite_snapshot_lookup_none[OF formed])
  have "snapshot_lookup (decode_finite_snapshot S) (decode_finite_target l)=None"
    using absent by (simp add: snapshot_lookup_none)
  then show ?thesis using None by simp
next
  case (Some G)
  then have member: "G\<in>fset S" "generation_locus G=l"
    by (simp_all add: finite_snapshot_lookup_formed[OF formed])
  have decoded: "snapshot_formed (decode_finite_snapshot S)"
    using formed by (simp only: finite_snapshot_formed_correct)
  have "snapshot_lookup (decode_finite_snapshot S) (decode_finite_target l)=Some (decode_finite_generation G)"
    using member by (simp add: snapshot_lookup_some[OF decoded] decode_finite_generation_selectors)
  then show ?thesis using Some by simp
qed

lemma map_option_decode_finite_generation_eq:
  "map_option decode_finite_generation x=map_option decode_finite_generation y \<longleftrightarrow> x=y"
  by (cases x; cases y) simp_all

section \<open>A finite transaction presents the four structural fields\<close>

record finite_transaction =
  finite_expected_selected :: finite_snapshot
  finite_expected_absent :: "finite_exact_target fset"
  finite_proposed_selected :: finite_snapshot
  finite_proposed_absent :: "finite_exact_target fset"

definition decode_finite_transaction :: "finite_transaction \<Rightarrow> structural_transaction" where
  "decode_finite_transaction T=\<lparr>expected_selected=decode_finite_snapshot (finite_expected_selected T),
    expected_absent=fimage decode_finite_target (finite_expected_absent T),
    proposed_selected=decode_finite_snapshot (finite_proposed_selected T),
    proposed_absent=fimage decode_finite_target (finite_proposed_absent T)\<rparr>"

lemma decode_finite_transaction_fields [simp]:
  "expected_selected (decode_finite_transaction T)=decode_finite_snapshot (finite_expected_selected T)"
  "expected_absent (decode_finite_transaction T)=fimage decode_finite_target (finite_expected_absent T)"
  "proposed_selected (decode_finite_transaction T)=decode_finite_snapshot (finite_proposed_selected T)"
  "proposed_absent (decode_finite_transaction T)=fimage decode_finite_target (finite_proposed_absent T)"
  by (simp_all add: decode_finite_transaction_def)

definition finite_comparison_loci :: "finite_transaction \<Rightarrow> finite_exact_target fset" where
  "finite_comparison_loci T=finite_snapshot_loci (finite_expected_selected T) |\<union>| finite_expected_absent T"

definition finite_changed_loci :: "finite_transaction \<Rightarrow> finite_exact_target fset" where
  "finite_changed_loci T=finite_snapshot_loci (finite_proposed_selected T) |\<union>| finite_proposed_absent T"

lemma decode_finite_comparison_loci:
  "comparison_loci (decode_finite_transaction T)=decode_finite_target ` fset (finite_comparison_loci T)"
  by (auto simp: comparison_loci_def finite_comparison_loci_def decode_finite_snapshot_loci fimage.rep_eq)

lemma decode_finite_changed_loci:
  "changed_loci (decode_finite_transaction T)=decode_finite_target ` fset (finite_changed_loci T)"
  by (auto simp: changed_loci_def finite_changed_loci_def decode_finite_snapshot_loci fimage.rep_eq)

definition finite_transaction_formed :: "finite_transaction \<Rightarrow> bool" where
  "finite_transaction_formed T \<longleftrightarrow>
    finite_snapshot_formed (finite_expected_selected T) \<and> finite_snapshot_formed (finite_proposed_selected T) \<and>
    fBall (finite_expected_absent T) finite_target_formed \<and> fBall (finite_proposed_absent T) finite_target_formed \<and>
    fBall (finite_snapshot_loci (finite_expected_selected T)) (\<lambda>l. l |\<notin>| finite_expected_absent T) \<and>
    fBall (finite_snapshot_loci (finite_proposed_selected T)) (\<lambda>l. l |\<notin>| finite_proposed_absent T) \<and>
    fBall (finite_changed_loci T) (\<lambda>l. l |\<in>| finite_comparison_loci T)"

lemma decoded_targets_disjoint:
  "decode_finite_target ` A\<inter>decode_finite_target ` B={} \<longleftrightarrow> (\<forall>l\<in>A. l\<notin>B)"
  by (auto simp: inj_image_mem_iff[OF decode_finite_target_inj])

lemma decoded_targets_subset:
  "decode_finite_target ` A\<subseteq>decode_finite_target ` B \<longleftrightarrow> (\<forall>l\<in>A. l\<in>B)"
  by (auto simp: inj_image_mem_iff[OF decode_finite_target_inj])

lemma decoded_targets_formed:
  "(\<forall>l\<in>fset (fimage decode_finite_target A). target_formed l) \<longleftrightarrow> fBall A finite_target_formed"
  by (auto simp: fimage.rep_eq finite_target_formed_correct)

lemma decoded_loci_absent:
  "snapshot_loci (decode_finite_snapshot W)\<inter>fset (fimage decode_finite_target D)={} \<longleftrightarrow>
    fBall (finite_snapshot_loci W) (\<lambda>l. l |\<notin>| D)"
  by (simp add: decode_finite_snapshot_loci fimage.rep_eq decoded_targets_disjoint)

lemma decoded_changed_compared:
  "changed_loci (decode_finite_transaction T)\<subseteq>comparison_loci (decode_finite_transaction T) \<longleftrightarrow>
    fBall (finite_changed_loci T) (\<lambda>l. l |\<in>| finite_comparison_loci T)"
  by (simp add: decode_finite_changed_loci decode_finite_comparison_loci decoded_targets_subset)

theorem finite_transaction_formed_correct:
  "finite_transaction_formed T \<longleftrightarrow> transaction_formed (decode_finite_transaction T)"
  unfolding finite_transaction_formed_def transaction_formed_def
  by (simp only: decoded_changed_compared decode_finite_transaction_fields finite_snapshot_formed_correct
    decoded_targets_formed decoded_loci_absent)

section \<open>Comparison, update and the observed comparison\<close>

definition finite_comparison_passes :: "finite_snapshot \<Rightarrow> finite_transaction \<Rightarrow> bool" where
  "finite_comparison_passes S T \<longleftrightarrow> fBall (finite_comparison_loci T)
    (\<lambda>l. finite_snapshot_lookup S l=finite_snapshot_lookup (finite_expected_selected T) l)"

theorem finite_comparison_passes_correct:
  assumes formed: "finite_snapshot_formed S" "finite_snapshot_formed (finite_expected_selected T)"
  shows "finite_comparison_passes S T \<longleftrightarrow>
    comparison_passes (decode_finite_snapshot S) (decode_finite_transaction T)"
proof -
  have "comparison_passes (decode_finite_snapshot S) (decode_finite_transaction T) \<longleftrightarrow>
    (\<forall>l\<in>fset (finite_comparison_loci T).
      snapshot_lookup (decode_finite_snapshot S) (decode_finite_target l)=
      snapshot_lookup (decode_finite_snapshot (finite_expected_selected T)) (decode_finite_target l))"
    by (auto simp: comparison_passes_def decode_finite_comparison_loci)
  also have "\<dots>\<longleftrightarrow>finite_comparison_passes S T"
    by (simp add: finite_comparison_passes_def finite_snapshot_lookup_exact[OF formed(1)]
      finite_snapshot_lookup_exact[OF formed(2)] map_option_decode_finite_generation_eq)
  finally show ?thesis by simp
qed

definition finite_transaction_update :: "finite_snapshot \<Rightarrow> finite_transaction \<Rightarrow> finite_snapshot" where
  "finite_transaction_update S T=
    ffilter (\<lambda>G. generation_locus G |\<notin>| finite_changed_loci T) S |\<union>| finite_proposed_selected T"

theorem decode_finite_transaction_update:
  "decode_finite_snapshot (finite_transaction_update S T)=
    transaction_update (decode_finite_snapshot S) (decode_finite_transaction T)"
proof -
  have changed: "snapshot_loci (decode_finite_snapshot (finite_proposed_selected T))\<union>
      fset (fimage decode_finite_target (finite_proposed_absent T))=
    decode_finite_target ` fset (finite_changed_loci T)"
    by (simp add: finite_changed_loci_def decode_finite_snapshot_loci fimage.rep_eq image_Un)
  show ?thesis
  proof (rule fset_eqI)
    fix x
    show "x |\<in>| decode_finite_snapshot (finite_transaction_update S T) \<longleftrightarrow>
      x |\<in>| transaction_update (decode_finite_snapshot S) (decode_finite_transaction T)"
      unfolding transaction_update_def replace_snapshot_def decode_finite_transaction_fields changed
      by (auto simp: finite_transaction_update_def decode_finite_snapshot_def fimage.rep_eq
        decode_finite_generation_selectors inj_image_mem_iff[OF decode_finite_target_inj])
  qed
qed

type_synonym finite_comparison_observation = "(finite_exact_target\<times>finite_generation option) fset"

definition finite_observed_comparison :: "finite_snapshot \<Rightarrow> finite_transaction \<Rightarrow> finite_comparison_observation" where
  "finite_observed_comparison S T=fimage (\<lambda>l. (l,finite_snapshot_lookup S l)) (finite_comparison_loci T)"

definition decode_finite_observation :: "finite_comparison_observation \<Rightarrow> comparison_observation" where
  "decode_finite_observation C=(\<lambda>(l,G). (decode_finite_target l,map_option decode_finite_generation G)) ` fset C"

lemma graph_map_image: "graph_map A f=(\<lambda>x. (x,f x)) ` A"
  by (auto simp: graph_map_def)

theorem decode_finite_observed_comparison:
  assumes formed: "finite_snapshot_formed S"
  shows "decode_finite_observation (finite_observed_comparison S T)=
    observed_comparison (decode_finite_snapshot S) (decode_finite_transaction T)"
proof -
  have "decode_finite_observation (finite_observed_comparison S T)=
      (\<lambda>l. (decode_finite_target l,snapshot_lookup (decode_finite_snapshot S) (decode_finite_target l))) `
        fset (finite_comparison_loci T)"
    by (simp add: decode_finite_observation_def finite_observed_comparison_def fimage.rep_eq image_image
      finite_snapshot_lookup_exact[OF formed])
  also have "\<dots>=observed_comparison (decode_finite_snapshot S) (decode_finite_transaction T)"
    by (simp add: observed_comparison_def graph_map_image decode_finite_comparison_loci image_image)
  finally show ?thesis .
qed

section \<open>The executed transaction is the structural transaction\<close>

datatype finite_transaction_result =
    Finite_Applied finite_snapshot
  | Finite_Conflict finite_comparison_observation

fun decode_finite_transaction_result :: "finite_transaction_result \<Rightarrow> transaction_result" where
  "decode_finite_transaction_result (Finite_Applied S)=Applied (decode_finite_snapshot S)"
| "decode_finite_transaction_result (Finite_Conflict C)=Conflict (decode_finite_observation C)"

definition finite_transact :: "finite_snapshot \<Rightarrow> finite_transaction \<Rightarrow> finite_transaction_result option" where
  "finite_transact S T=(if finite_snapshot_formed S \<and> finite_transaction_formed T then
    Some (if finite_comparison_passes S T then Finite_Applied (finite_transaction_update S T)
      else Finite_Conflict (finite_observed_comparison S T)) else None)"

theorem finite_transact_exact:
  "transact (decode_finite_snapshot S) (decode_finite_transaction T) result \<longleftrightarrow>
    (\<exists>r. finite_transact S T=Some r \<and> result=decode_finite_transaction_result r)"
proof (cases "finite_snapshot_formed S \<and> finite_transaction_formed T")
  case True
  then have formed: "finite_snapshot_formed S" "finite_snapshot_formed (finite_expected_selected T)"
    and transaction: "finite_transaction_formed T"
    by (simp_all add: finite_transaction_formed_def)
  have decoded: "snapshot_formed (decode_finite_snapshot S)" "transaction_formed (decode_finite_transaction T)"
    using formed(1) transaction by (simp_all only: finite_snapshot_formed_correct finite_transaction_formed_correct)
  have passes: "comparison_passes (decode_finite_snapshot S) (decode_finite_transaction T) \<longleftrightarrow>
      finite_comparison_passes S T"
    by (simp only: finite_comparison_passes_correct[OF formed])
  show ?thesis
    by (simp add: transact_def finite_transact_def decoded formed(1) transaction passes
      decode_finite_transaction_update decode_finite_observed_comparison[OF formed(1)])
next
  case False
  then have refused: "finite_transact S T=None" by (auto simp: finite_transact_def)
  have "\<not>transact (decode_finite_snapshot S) (decode_finite_transaction T) result"
    using False by (auto simp: transact_def finite_snapshot_formed_correct finite_transaction_formed_correct)
  then show ?thesis using refused by simp
qed

corollary finite_transact_refused:
  "finite_transact S T=None \<longleftrightarrow>
    \<not>(snapshot_formed (decode_finite_snapshot S) \<and> transaction_formed (decode_finite_transaction T))"
  by (simp add: finite_transact_def finite_snapshot_formed_correct finite_transaction_formed_correct)

section \<open>Replacement and admission at one locus\<close>

definition finite_replacement_transaction :: "finite_generation \<Rightarrow> finite_generation \<Rightarrow> finite_transaction" where
  "finite_replacement_transaction G H=\<lparr>finite_expected_selected={|G|},finite_expected_absent={||},
    finite_proposed_selected={|H|},finite_proposed_absent={||}\<rparr>"

lemma decode_finite_replacement_transaction:
  "decode_finite_transaction (finite_replacement_transaction G H)=
    replacement_transaction (decode_finite_generation G) (decode_finite_generation H)"
  by (simp add: decode_finite_transaction_def finite_replacement_transaction_def
    replacement_transaction_def decode_finite_snapshot_def)

definition finite_admission_transaction :: "finite_snapshot \<Rightarrow> finite_transaction" where
  "finite_admission_transaction W=\<lparr>finite_expected_selected={||},finite_expected_absent=finite_snapshot_loci W,
    finite_proposed_selected=W,finite_proposed_absent={||}\<rparr>"

lemma decode_finite_admission_transaction:
  "decode_finite_transaction (finite_admission_transaction W)=admission_transaction (decode_finite_snapshot W)"
proof -
  have "fimage decode_finite_target (finite_snapshot_loci W)=fimage generation_locus (decode_finite_snapshot W)"
    by (simp add: finite_snapshot_loci_def decode_finite_snapshot_def fimage_fimage comp_def
      decode_finite_generation_selectors)
  then show ?thesis
    by (simp add: decode_finite_transaction_def finite_admission_transaction_def admission_transaction_def
      decode_finite_snapshot_def)
qed

text \<open>
  The transaction a publisher builds expects exactly what it read at the locus it writes: the
  generation selected there, or its absence. Applied to the snapshot current when it is
  executed, it replaces that generation or admits the new one; if the locus has changed since
  it was read, the transaction yields the complete observed comparison and no successor.
\<close>

definition finite_locus_transaction ::
    "finite_generation option \<Rightarrow> finite_generation \<Rightarrow> finite_transaction" where
  "finite_locus_transaction expected H=(case expected of
     None \<Rightarrow> finite_admission_transaction {|H|}
   | Some G \<Rightarrow> finite_replacement_transaction G H)"

lemma decode_finite_locus_transaction:
  "decode_finite_transaction (finite_locus_transaction expected H)=(case expected of
     None \<Rightarrow> admission_transaction {|decode_finite_generation H|}
   | Some G \<Rightarrow> replacement_transaction (decode_finite_generation G) (decode_finite_generation H))"
  by (cases expected) (simp_all add: finite_locus_transaction_def decode_finite_admission_transaction
    decode_finite_replacement_transaction decode_finite_snapshot_def)

text \<open>
  Formation, lookup, comparison, update and the observed comparison are each the original
  operation on the decoded values, so the executed transaction has exactly the structural
  transaction's outcome: a successor snapshot when every compared locus holds what was
  expected, and otherwise every observation of the comparison and no successor. The
  executable values add no field and select nothing; they neither create succession nor
  validate a cause or a publication.
\<close>

end
