theory Represented_Snapshot_Transactions
  imports RRA_Formed_Snapshot_Transactions Generation_Identity_Maps
begin

section \<open>Snapshots over any representation of their targets\<close>

text \<open>
  The transactions of @{text RRA_Finite_Transactions} and @{text RRA_Formed_Snapshot_Transactions}
  are stated over finite generations, whose targets are complete exact values. The same operations
  are stated here over generations whose targets are of any type, the formation of a target a
  parameter. Each is the existing operation under a decoding of the targets: the decoding mapped
  after it is the existing operation on the decoded arguments, the formation of a target read through
  the decoding, whenever the decoding is injective on the targets that occur in its arguments. A
  round may therefore hold its generations over references to targets it made once, and compare
  references where the existing operations compare whole targets. At exact targets with the identity
  each operation is the existing one.
\<close>

type_synonym 't represented_snapshot = "'t generation_structure fset"

primrec represented_generation_formed :: "('t \<Rightarrow> bool) \<Rightarrow> 't generation_structure \<Rightarrow> bool" where
  "represented_generation_formed tf (Generation l P p c)=(tf l \<and> tf p \<and> tf c \<and>
    fBall (fimage (represented_generation_formed tf) P) id)"

lemma represented_generation_formed_decoded:
  "represented_generation_formed (\<lambda>t. finite_target_formed (dec t)) G \<longleftrightarrow>
    finite_generation_formed (map_generation_structure dec G)"
proof (induction G)
  case (Generation l P p c)
  have "fBall (fimage (represented_generation_formed (\<lambda>t. finite_target_formed (dec t))) P) id \<longleftrightarrow>
      fBall (fimage finite_generation_formed (fimage (map_generation_structure dec) P)) id"
    using Generation.IH by (auto simp: fimage.rep_eq)
  then show ?case by simp
qed

lemma represented_generation_formed_exact:
  "represented_generation_formed finite_target_formed=finite_generation_formed"
proof
  fix G
  show "represented_generation_formed finite_target_formed G=finite_generation_formed G"
    using represented_generation_formed_decoded[of id G] by (simp add: generation_structure.map_id)
qed

definition represented_snapshot_targets :: "'t represented_snapshot \<Rightarrow> 't set" where
  "represented_snapshot_targets S=(\<Union>G\<in>fset S. set_generation_structure G)"

definition decode_represented_snapshot :: "('t \<Rightarrow> finite_exact_target) \<Rightarrow> 't represented_snapshot \<Rightarrow> finite_snapshot" where
  "decode_represented_snapshot dec S=fimage (map_generation_structure dec) S"

lemma decode_represented_snapshot_identity [simp]:
  "decode_represented_snapshot id S=S"
  by (rule fset_eqI) (simp add: decode_represented_snapshot_def fimage.rep_eq generation_structure.map_id)

lemma represented_locus_decoded [simp]:
  "generation_locus (map_generation_structure dec G)=dec (generation_locus G)"
  by (cases G) simp

lemma represented_locus_target: "generation_locus G\<in>set_generation_structure G"
  by (cases G) simp

lemma represented_decoded_member:
  assumes "inj_on dec K" "x\<in>K" "X\<subseteq>K"
  shows "dec x\<in>dec ` X \<longleftrightarrow> x\<in>X"
  using assms unfolding inj_on_def by blast

lemma represented_ball_image: "(\<forall>x\<in>f ` A. P x) \<longleftrightarrow> (\<forall>x\<in>A. P (f x))"
  by blast

lemma represented_fcard_image:
  assumes "inj_on f (fset A)"
  shows "fcard (fimage f A)=fcard A"
  using assms by (simp add: fcard.rep_eq fimage.rep_eq card_image)

lemma represented_snapshot_injective:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
  shows "inj_on (map_generation_structure dec) (fset S)"
  by (rule generation_identity_map_inj_on[OF inj]) (use S in \<open>auto simp: represented_snapshot_targets_def\<close>)

section \<open>Loci, formation and lookup\<close>

definition represented_snapshot_loci :: "'t represented_snapshot \<Rightarrow> 't fset" where
  "represented_snapshot_loci S=fimage generation_locus S"

lemma decode_represented_snapshot_loci:
  "finite_snapshot_loci (decode_represented_snapshot dec S)=fimage dec (represented_snapshot_loci S)"
  by (simp add: finite_snapshot_loci_def represented_snapshot_loci_def decode_represented_snapshot_def
    fimage_fimage comp_def)

lemma represented_snapshot_loci_exact: "represented_snapshot_loci S=finite_snapshot_loci S"
  by (simp add: represented_snapshot_loci_def finite_snapshot_loci_def)

lemma represented_snapshot_loci_targets:
  "fset (represented_snapshot_loci S)\<subseteq>represented_snapshot_targets S"
  unfolding represented_snapshot_loci_def represented_snapshot_targets_def fimage.rep_eq
  using represented_locus_target by blast

definition represented_snapshot_loci_formed :: "'t represented_snapshot \<Rightarrow> bool" where
  "represented_snapshot_loci_formed S \<longleftrightarrow> fcard (represented_snapshot_loci S)=fcard S"

lemma represented_snapshot_loci_formed_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
  shows "represented_snapshot_loci_formed S \<longleftrightarrow> finite_snapshot_loci_formed (decode_represented_snapshot dec S)"
proof -
  have loci: "inj_on dec (fset (represented_snapshot_loci S))"
    by (rule inj_on_subset[OF inj order_trans[OF represented_snapshot_loci_targets S]])
  have "fcard (finite_snapshot_loci (decode_represented_snapshot dec S))=fcard (represented_snapshot_loci S)"
    unfolding decode_represented_snapshot_loci by (rule represented_fcard_image[OF loci])
  moreover have "fcard (decode_represented_snapshot dec S)=fcard S"
    unfolding decode_represented_snapshot_def
    by (rule represented_fcard_image[OF represented_snapshot_injective[OF inj S]])
  ultimately show ?thesis
    by (simp only: represented_snapshot_loci_formed_def finite_snapshot_loci_formed_def)
qed

definition represented_snapshot_formed :: "('t \<Rightarrow> bool) \<Rightarrow> 't represented_snapshot \<Rightarrow> bool" where
  "represented_snapshot_formed tf S \<longleftrightarrow> fBall S (represented_generation_formed tf) \<and>
    represented_snapshot_loci_formed S"

theorem represented_snapshot_formed_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
  shows "represented_snapshot_formed (\<lambda>t. finite_target_formed (dec t)) S \<longleftrightarrow>
    finite_snapshot_formed (decode_represented_snapshot dec S)"
proof -
  have generations: "fBall S (represented_generation_formed (\<lambda>t. finite_target_formed (dec t))) \<longleftrightarrow>
      fBall (decode_represented_snapshot dec S) finite_generation_formed"
    by (auto simp: decode_represented_snapshot_def fimage.rep_eq represented_generation_formed_decoded)
  show ?thesis
    by (simp only: represented_snapshot_formed_def generations
      represented_snapshot_loci_formed_decoded[OF inj S] finite_snapshot_formed_def finite_snapshot_loci_formed_def)
qed

lemma represented_snapshot_formed_exact:
  "represented_snapshot_formed finite_target_formed S \<longleftrightarrow> finite_snapshot_formed S"
  using represented_snapshot_formed_decoded[of id UNIV S] by simp

definition represented_snapshot_lookup :: "'t represented_snapshot \<Rightarrow> 't \<Rightarrow> 't generation_structure option" where
  "represented_snapshot_lookup S l=finite_singleton_option (ffilter (\<lambda>G. generation_locus G=l) S)"

lemma represented_snapshot_lookup_exact: "represented_snapshot_lookup S l=finite_snapshot_lookup S l"
  by (simp add: represented_snapshot_lookup_def finite_snapshot_lookup_def)

lemma represented_snapshot_lookup_member:
  assumes found: "represented_snapshot_lookup S l=Some G"
  shows "G\<in>fset S \<and> generation_locus G=l"
proof -
  have "ffilter (\<lambda>G. generation_locus G=l) S={|G|}"
    using found by (simp only: represented_snapshot_lookup_def finite_singleton_option_some)
  then have "G |\<in>| ffilter (\<lambda>G. generation_locus G=l) S" by simp
  then show ?thesis by simp
qed

lemma finite_singleton_option_image:
  assumes inj: "inj_on f (fset A)"
  shows "finite_singleton_option (fimage f A)=map_option f (finite_singleton_option A)"
proof (cases "finite_singleton_option A")
  case (Some x)
  then have "A={|x|}" by (simp add: finite_singleton_option_some)
  then show ?thesis using Some by simp
next
  case None
  have "finite_singleton_option (fimage f A)=None"
  proof (rule ccontr)
    assume "finite_singleton_option (fimage f A)\<noteq>None"
    then obtain y where "finite_singleton_option (fimage f A)=Some y" by auto
    then have "fset (fimage f A)=fset {|y|}" by (simp add: finite_singleton_option_some)
    then have image: "f ` fset A={y}" by (simp add: fimage.rep_eq)
    then obtain a where a: "a\<in>fset A" by blast
    have "fset A={a}"
    proof
      show "fset A\<subseteq>{a}"
      proof
        fix b
        assume b: "b\<in>fset A"
        have "f b=y" "f a=y" using image b a by blast+
        then show "b\<in>{a}" using inj b a by (simp add: inj_on_def)
      qed
      show "{a}\<subseteq>fset A" using a by simp
    qed
    then have "A={|a|}" by (simp add: fset_eq_iff)
    then show False using None by simp
  qed
  then show ?thesis using None by simp
qed

theorem represented_snapshot_lookup_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K" and l: "l\<in>K"
  shows "map_option (map_generation_structure dec) (represented_snapshot_lookup S l)=
    finite_snapshot_lookup (decode_represented_snapshot dec S) (dec l)"
proof -
  have generations: "inj_on (map_generation_structure dec) (fset S)"
    by (rule represented_snapshot_injective[OF inj S])
  have locus: "dec (generation_locus G)=dec l \<longleftrightarrow> generation_locus G=l" if "G\<in>fset S" for G
  proof -
    have "generation_locus G\<in>K"
      using that S represented_locus_target unfolding represented_snapshot_targets_def by blast
    then show ?thesis using inj l by (auto dest: inj_onD)
  qed
  have filtered: "ffilter (\<lambda>G. generation_locus G=dec l) (decode_represented_snapshot dec S)=
      fimage (map_generation_structure dec) (ffilter (\<lambda>G. generation_locus G=l) S)"
    by (rule fset_eqI) (auto simp: decode_represented_snapshot_def fimage.rep_eq locus)
  have "inj_on (map_generation_structure dec) (fset (ffilter (\<lambda>G. generation_locus G=l) S))"
    using generations by (rule inj_on_subset) auto
  then show ?thesis
    by (simp add: represented_snapshot_lookup_def finite_snapshot_lookup_def filtered finite_singleton_option_image)
qed

section \<open>Transactions, their loci and their formation\<close>

record 't represented_transaction =
  represented_expected_selected :: "'t represented_snapshot"
  represented_expected_absent :: "'t fset"
  represented_proposed_selected :: "'t represented_snapshot"
  represented_proposed_absent :: "'t fset"

definition decode_represented_transaction ::
    "('t \<Rightarrow> finite_exact_target) \<Rightarrow> 't represented_transaction \<Rightarrow> finite_transaction" where
  "decode_represented_transaction dec T=\<lparr>
    finite_expected_selected=decode_represented_snapshot dec (represented_expected_selected T),
    finite_expected_absent=fimage dec (represented_expected_absent T),
    finite_proposed_selected=decode_represented_snapshot dec (represented_proposed_selected T),
    finite_proposed_absent=fimage dec (represented_proposed_absent T)\<rparr>"

lemma decode_represented_transaction_fields [simp]:
  "finite_expected_selected (decode_represented_transaction dec T)=
    decode_represented_snapshot dec (represented_expected_selected T)"
  "finite_expected_absent (decode_represented_transaction dec T)=fimage dec (represented_expected_absent T)"
  "finite_proposed_selected (decode_represented_transaction dec T)=
    decode_represented_snapshot dec (represented_proposed_selected T)"
  "finite_proposed_absent (decode_represented_transaction dec T)=fimage dec (represented_proposed_absent T)"
  by (simp_all add: decode_represented_transaction_def)

text \<open>At exact targets every finite transaction is the decoding of one with the same fields.\<close>

definition represented_of_finite_transaction :: "finite_transaction \<Rightarrow> finite_exact_target represented_transaction" where
  "represented_of_finite_transaction T=\<lparr>represented_expected_selected=finite_expected_selected T,
    represented_expected_absent=finite_expected_absent T,
    represented_proposed_selected=finite_proposed_selected T,
    represented_proposed_absent=finite_proposed_absent T\<rparr>"

lemma decode_represented_of_finite_transaction [simp]:
  "decode_represented_transaction id (represented_of_finite_transaction T)=T"
  by (cases T) (simp add: decode_represented_transaction_def represented_of_finite_transaction_def)

definition represented_transaction_targets :: "'t represented_transaction \<Rightarrow> 't set" where
  "represented_transaction_targets T=represented_snapshot_targets (represented_expected_selected T)\<union>
    fset (represented_expected_absent T)\<union>represented_snapshot_targets (represented_proposed_selected T)\<union>
    fset (represented_proposed_absent T)"

definition represented_comparison_loci :: "'t represented_transaction \<Rightarrow> 't fset" where
  "represented_comparison_loci T=
    represented_snapshot_loci (represented_expected_selected T) |\<union>| represented_expected_absent T"

definition represented_changed_loci :: "'t represented_transaction \<Rightarrow> 't fset" where
  "represented_changed_loci T=
    represented_snapshot_loci (represented_proposed_selected T) |\<union>| represented_proposed_absent T"

lemma decode_represented_comparison_loci:
  "finite_comparison_loci (decode_represented_transaction dec T)=fimage dec (represented_comparison_loci T)"
  by (simp add: finite_comparison_loci_def represented_comparison_loci_def decode_represented_snapshot_loci
    fimage_funion)

lemma decode_represented_changed_loci:
  "finite_changed_loci (decode_represented_transaction dec T)=fimage dec (represented_changed_loci T)"
  by (simp add: finite_changed_loci_def represented_changed_loci_def decode_represented_snapshot_loci
    fimage_funion)

lemma represented_comparison_loci_targets:
  "fset (represented_comparison_loci T)\<subseteq>represented_transaction_targets T"
  using represented_snapshot_loci_targets[of "represented_expected_selected T"]
  by (auto simp: represented_comparison_loci_def represented_transaction_targets_def)

lemma represented_changed_loci_targets:
  "fset (represented_changed_loci T)\<subseteq>represented_transaction_targets T"
  using represented_snapshot_loci_targets[of "represented_proposed_selected T"]
  by (auto simp: represented_changed_loci_def represented_transaction_targets_def)

text \<open>
  The conditions on a transaction's loci and absent targets: formed absent targets, no selected
  generation at an absent locus, and every changed locus compared.
\<close>

definition represented_transaction_loci_formed :: "('t \<Rightarrow> bool) \<Rightarrow> 't represented_transaction \<Rightarrow> bool" where
  "represented_transaction_loci_formed tf T \<longleftrightarrow>
    fBall (represented_expected_absent T) tf \<and> fBall (represented_proposed_absent T) tf \<and>
    fBall (represented_snapshot_loci (represented_expected_selected T)) (\<lambda>l. l |\<notin>| represented_expected_absent T) \<and>
    fBall (represented_snapshot_loci (represented_proposed_selected T)) (\<lambda>l. l |\<notin>| represented_proposed_absent T) \<and>
    fBall (represented_changed_loci T) (\<lambda>l. l |\<in>| represented_comparison_loci T)"

lemma represented_transaction_target_parts:
  assumes "represented_transaction_targets T\<subseteq>K"
  shows "represented_snapshot_targets (represented_expected_selected T)\<subseteq>K"
    "represented_snapshot_targets (represented_proposed_selected T)\<subseteq>K"
    "fset (represented_expected_absent T)\<subseteq>K" "fset (represented_proposed_absent T)\<subseteq>K"
    "fset (represented_snapshot_loci (represented_expected_selected T))\<subseteq>K"
    "fset (represented_snapshot_loci (represented_proposed_selected T))\<subseteq>K"
    "fset (represented_comparison_loci T)\<subseteq>K" "fset (represented_changed_loci T)\<subseteq>K"
  using assms represented_snapshot_loci_targets[of "represented_expected_selected T"]
    represented_snapshot_loci_targets[of "represented_proposed_selected T"]
    represented_comparison_loci_targets[of T] represented_changed_loci_targets[of T]
  by (auto simp: represented_transaction_targets_def)

lemma represented_transaction_loci_formed_decoded:
  assumes inj: "inj_on dec K" and T: "represented_transaction_targets T\<subseteq>K"
  shows "represented_transaction_loci_formed (\<lambda>t. finite_target_formed (dec t)) T \<longleftrightarrow>
    fBall (finite_expected_absent (decode_represented_transaction dec T)) finite_target_formed \<and>
    fBall (finite_proposed_absent (decode_represented_transaction dec T)) finite_target_formed \<and>
    fBall (finite_snapshot_loci (finite_expected_selected (decode_represented_transaction dec T)))
      (\<lambda>l. l |\<notin>| finite_expected_absent (decode_represented_transaction dec T)) \<and>
    fBall (finite_snapshot_loci (finite_proposed_selected (decode_represented_transaction dec T)))
      (\<lambda>l. l |\<notin>| finite_proposed_absent (decode_represented_transaction dec T)) \<and>
    fBall (finite_changed_loci (decode_represented_transaction dec T))
      (\<lambda>l. l |\<in>| finite_comparison_loci (decode_represented_transaction dec T))"
proof -
  note parts=represented_transaction_target_parts[OF T]
  have formed: "fBall (fimage dec X) finite_target_formed \<longleftrightarrow> fBall X (\<lambda>t. finite_target_formed (dec t))" for X
    by (auto simp: fimage.rep_eq)
  have member: "dec l\<in>dec ` fset X \<longleftrightarrow> l\<in>fset X" if "fset L\<subseteq>K" "fset X\<subseteq>K" "l\<in>fset L" for L X l
    by (rule represented_decoded_member[OF inj subsetD[OF that(1) that(3)] that(2)])
  have disjoint: "fBall (fimage dec L) (\<lambda>l. l |\<notin>| fimage dec X) \<longleftrightarrow> fBall L (\<lambda>l. l |\<notin>| X)"
    if "fset L\<subseteq>K" "fset X\<subseteq>K" for L X
    using member[OF that] by (auto simp: fimage.rep_eq)
  have within: "fBall (fimage dec L) (\<lambda>l. l |\<in>| fimage dec X) \<longleftrightarrow> fBall L (\<lambda>l. l |\<in>| X)"
    if "fset L\<subseteq>K" "fset X\<subseteq>K" for L X
    using member[OF that] by (auto simp: fimage.rep_eq)
  show ?thesis
    unfolding represented_transaction_loci_formed_def decode_represented_transaction_fields
      decode_represented_snapshot_loci decode_represented_changed_loci decode_represented_comparison_loci
    by (simp only: formed disjoint[OF parts(5,3)] disjoint[OF parts(6,4)] within[OF parts(8,7)])
qed

definition represented_transaction_formed :: "('t \<Rightarrow> bool) \<Rightarrow> 't represented_transaction \<Rightarrow> bool" where
  "represented_transaction_formed tf T \<longleftrightarrow>
    represented_snapshot_formed tf (represented_expected_selected T) \<and>
    represented_snapshot_formed tf (represented_proposed_selected T) \<and> represented_transaction_loci_formed tf T"

theorem represented_transaction_formed_decoded:
  assumes inj: "inj_on dec K" and T: "represented_transaction_targets T\<subseteq>K"
  shows "represented_transaction_formed (\<lambda>t. finite_target_formed (dec t)) T \<longleftrightarrow>
    finite_transaction_formed (decode_represented_transaction dec T)"
proof -
  note parts=represented_transaction_target_parts[OF T]
  show ?thesis
    unfolding represented_transaction_formed_def finite_transaction_formed_def
    by (simp only: represented_snapshot_formed_decoded[OF inj parts(1)]
      represented_snapshot_formed_decoded[OF inj parts(2)] represented_transaction_loci_formed_decoded[OF inj T]
      decode_represented_transaction_fields)
qed

definition represented_transaction_generations :: "'t represented_transaction \<Rightarrow> 't generation_structure fset" where
  "represented_transaction_generations T=represented_expected_selected T |\<union>| represented_proposed_selected T"

definition represented_transaction_body_formed :: "('t \<Rightarrow> bool) \<Rightarrow> 't represented_transaction \<Rightarrow> bool" where
  "represented_transaction_body_formed tf T \<longleftrightarrow>
    represented_snapshot_loci_formed (represented_expected_selected T) \<and>
    represented_snapshot_loci_formed (represented_proposed_selected T) \<and> represented_transaction_loci_formed tf T"

theorem represented_transaction_body_formed_decoded:
  assumes inj: "inj_on dec K" and T: "represented_transaction_targets T\<subseteq>K"
  shows "represented_transaction_body_formed (\<lambda>t. finite_target_formed (dec t)) T \<longleftrightarrow>
    finite_transaction_body_formed (decode_represented_transaction dec T)"
proof -
  note parts=represented_transaction_target_parts[OF T]
  show ?thesis
    unfolding represented_transaction_body_formed_def finite_transaction_body_formed_def
    by (simp only: represented_snapshot_loci_formed_decoded[OF inj parts(1)]
      represented_snapshot_loci_formed_decoded[OF inj parts(2)] represented_transaction_loci_formed_decoded[OF inj T]
      decode_represented_transaction_fields finite_snapshot_loci_formed_def)
qed

lemma represented_transaction_formed_generations:
  "represented_transaction_formed tf T \<longleftrightarrow>
    fBall (represented_transaction_generations T) (represented_generation_formed tf) \<and>
    represented_transaction_body_formed tf T"
  by (auto simp: represented_transaction_formed_def represented_transaction_body_formed_def
    represented_transaction_generations_def represented_snapshot_formed_def)

section \<open>Comparison, update and the observed comparison\<close>

definition represented_comparison_passes :: "'t represented_snapshot \<Rightarrow> 't represented_transaction \<Rightarrow> bool" where
  "represented_comparison_passes S T \<longleftrightarrow> fBall (represented_comparison_loci T)
    (\<lambda>l. represented_snapshot_lookup S l=represented_snapshot_lookup (represented_expected_selected T) l)"

theorem represented_comparison_passes_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
    and T: "represented_transaction_targets T\<subseteq>K"
  shows "represented_comparison_passes S T \<longleftrightarrow>
    finite_comparison_passes (decode_represented_snapshot dec S) (decode_represented_transaction dec T)"
proof -
  let ?E="represented_expected_selected T"
  note parts=represented_transaction_target_parts[OF T]
  have generations: "inj_on (map_generation_structure dec) (fset S\<union>fset ?E)"
    by (rule generation_identity_map_inj_on[OF inj])
      (use S parts(1) in \<open>auto simp: represented_snapshot_targets_def\<close>)
  have same: "map_option (map_generation_structure dec) x=map_option (map_generation_structure dec) y \<longleftrightarrow> x=y"
    if "set_option x\<subseteq>fset S\<union>fset ?E" "set_option y\<subseteq>fset S\<union>fset ?E" for x y
    using that by (cases x; cases y) (simp_all add: inj_on_eq_iff[OF generations])
  have found: "set_option (represented_snapshot_lookup S l)\<subseteq>fset S\<union>fset ?E"
    "set_option (represented_snapshot_lookup ?E l)\<subseteq>fset S\<union>fset ?E" for l
    by (cases "represented_snapshot_lookup S l"; cases "represented_snapshot_lookup ?E l";
      simp add: represented_snapshot_lookup_member)+
  have same_at: "map_option (map_generation_structure dec) (represented_snapshot_lookup S l)=
      map_option (map_generation_structure dec) (represented_snapshot_lookup ?E l) \<longleftrightarrow>
    represented_snapshot_lookup S l=represented_snapshot_lookup ?E l" for l
    by (rule same[OF found])
  have at: "finite_snapshot_lookup (decode_represented_snapshot dec S) (dec l)=
        map_option (map_generation_structure dec) (represented_snapshot_lookup S l)"
      "finite_snapshot_lookup (decode_represented_snapshot dec ?E) (dec l)=
        map_option (map_generation_structure dec) (represented_snapshot_lookup ?E l)"
    if "l\<in>fset (represented_comparison_loci T)" for l
    using represented_snapshot_lookup_decoded[OF inj S subsetD[OF parts(7) that]]
      represented_snapshot_lookup_decoded[OF inj parts(1) subsetD[OF parts(7) that]] by simp_all
  have "finite_comparison_passes (decode_represented_snapshot dec S) (decode_represented_transaction dec T) \<longleftrightarrow>
      (\<forall>l\<in>fset (represented_comparison_loci T).
        finite_snapshot_lookup (decode_represented_snapshot dec S) (dec l)=
        finite_snapshot_lookup (decode_represented_snapshot dec ?E) (dec l))"
    by (simp only: finite_comparison_passes_def decode_represented_comparison_loci fimage.rep_eq
      represented_ball_image decode_represented_transaction_fields)
  also have "\<dots>\<longleftrightarrow>represented_comparison_passes S T"
    unfolding represented_comparison_passes_def using at same_at by (simp cong: ball_cong)
  finally show ?thesis by simp
qed

definition represented_transaction_update ::
    "'t represented_snapshot \<Rightarrow> 't represented_transaction \<Rightarrow> 't represented_snapshot" where
  "represented_transaction_update S T=
    ffilter (\<lambda>G. generation_locus G |\<notin>| represented_changed_loci T) S |\<union>| represented_proposed_selected T"

theorem represented_transaction_update_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
    and T: "represented_transaction_targets T\<subseteq>K"
  shows "decode_represented_snapshot dec (represented_transaction_update S T)=
    finite_transaction_update (decode_represented_snapshot dec S) (decode_represented_transaction dec T)"
proof -
  note parts=represented_transaction_target_parts[OF T]
  have locus: "dec (generation_locus G)\<in>dec ` fset (represented_changed_loci T) \<longleftrightarrow>
      generation_locus G\<in>fset (represented_changed_loci T)" if "G\<in>fset S" for G
  proof -
    have "generation_locus G\<in>K"
      using that S represented_locus_target unfolding represented_snapshot_targets_def by blast
    then show ?thesis by (rule represented_decoded_member[OF inj _ parts(8)])
  qed
  have filtered: "ffilter (\<lambda>G. generation_locus G |\<notin>| fimage dec (represented_changed_loci T))
      (decode_represented_snapshot dec S)=
    fimage (map_generation_structure dec) (ffilter (\<lambda>G. generation_locus G |\<notin>| represented_changed_loci T) S)"
  proof (rule fset_eqI)
    fix x
    have "x |\<in>| ffilter (\<lambda>G. generation_locus G |\<notin>| fimage dec (represented_changed_loci T))
        (decode_represented_snapshot dec S) \<longleftrightarrow>
      (\<exists>G\<in>fset S. x=map_generation_structure dec G \<and>
        dec (generation_locus G)\<notin>dec ` fset (represented_changed_loci T))"
      by (auto simp: decode_represented_snapshot_def fimage.rep_eq)
    also have "\<dots>\<longleftrightarrow>(\<exists>G\<in>fset S. x=map_generation_structure dec G \<and>
        generation_locus G\<notin>fset (represented_changed_loci T))"
      using locus by blast
    also have "\<dots>\<longleftrightarrow>x |\<in>| fimage (map_generation_structure dec)
        (ffilter (\<lambda>G. generation_locus G |\<notin>| represented_changed_loci T) S)"
      by (auto simp: fimage.rep_eq)
    finally show "x |\<in>| ffilter (\<lambda>G. generation_locus G |\<notin>| fimage dec (represented_changed_loci T))
        (decode_represented_snapshot dec S) \<longleftrightarrow>
      x |\<in>| fimage (map_generation_structure dec)
        (ffilter (\<lambda>G. generation_locus G |\<notin>| represented_changed_loci T) S)" .
  qed
  show ?thesis
    unfolding represented_transaction_update_def finite_transaction_update_def
      decode_represented_changed_loci decode_represented_transaction_fields filtered
    by (simp add: decode_represented_snapshot_def fimage_funion)
qed

lemma represented_transaction_update_targets:
  "represented_snapshot_targets (represented_transaction_update S T)\<subseteq>
    represented_snapshot_targets S\<union>represented_transaction_targets T"
  by (auto simp: represented_transaction_update_def represented_snapshot_targets_def
    represented_transaction_targets_def)

type_synonym 't represented_observation = "('t\<times>'t generation_structure option) fset"

definition represented_observed_comparison ::
    "'t represented_snapshot \<Rightarrow> 't represented_transaction \<Rightarrow> 't represented_observation" where
  "represented_observed_comparison S T=
    fimage (\<lambda>l. (l,represented_snapshot_lookup S l)) (represented_comparison_loci T)"

definition decode_represented_observation ::
    "('t \<Rightarrow> finite_exact_target) \<Rightarrow> 't represented_observation \<Rightarrow> finite_comparison_observation" where
  "decode_represented_observation dec C=
    fimage (\<lambda>(l,G). (dec l,map_option (map_generation_structure dec) G)) C"

theorem represented_observed_comparison_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
    and T: "represented_transaction_targets T\<subseteq>K"
  shows "decode_represented_observation dec (represented_observed_comparison S T)=
    finite_observed_comparison (decode_represented_snapshot dec S) (decode_represented_transaction dec T)"
proof -
  note parts=represented_transaction_target_parts[OF T]
  have at: "finite_snapshot_lookup (decode_represented_snapshot dec S) (dec l)=
      map_option (map_generation_structure dec) (represented_snapshot_lookup S l)"
    if "l\<in>fset (represented_comparison_loci T)" for l
    using represented_snapshot_lookup_decoded[OF inj S subsetD[OF parts(7) that]] by simp
  have "decode_represented_observation dec (represented_observed_comparison S T)=
      fimage (\<lambda>l. (dec l,map_option (map_generation_structure dec) (represented_snapshot_lookup S l)))
        (represented_comparison_loci T)"
    by (simp add: decode_represented_observation_def represented_observed_comparison_def fimage_fimage comp_def)
  also have "\<dots>=fimage (\<lambda>l. (dec l,finite_snapshot_lookup (decode_represented_snapshot dec S) (dec l)))
      (represented_comparison_loci T)"
    by (rule fset_eqI) (auto simp: fimage.rep_eq at)
  also have "\<dots>=finite_observed_comparison (decode_represented_snapshot dec S) (decode_represented_transaction dec T)"
    by (simp add: finite_observed_comparison_def decode_represented_comparison_loci fimage_fimage comp_def)
  finally show ?thesis .
qed

section \<open>The executed transaction and its three checks\<close>

datatype 't represented_transaction_result =
    Represented_Applied "'t represented_snapshot"
  | Represented_Conflict "'t represented_observation"

fun decode_represented_result ::
    "('t \<Rightarrow> finite_exact_target) \<Rightarrow> 't represented_transaction_result \<Rightarrow> finite_transaction_result" where
  "decode_represented_result dec (Represented_Applied S)=Finite_Applied (decode_represented_snapshot dec S)"
| "decode_represented_result dec (Represented_Conflict C)=Finite_Conflict (decode_represented_observation dec C)"

definition represented_transaction_step ::
    "'t represented_snapshot \<Rightarrow> 't represented_transaction \<Rightarrow> 't represented_transaction_result" where
  "represented_transaction_step S T=(if represented_comparison_passes S T
    then Represented_Applied (represented_transaction_update S T)
    else Represented_Conflict (represented_observed_comparison S T))"

lemma represented_transaction_step_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
    and T: "represented_transaction_targets T\<subseteq>K"
  shows "decode_represented_result dec (represented_transaction_step S T)=
    (if finite_comparison_passes (decode_represented_snapshot dec S) (decode_represented_transaction dec T)
     then Finite_Applied (finite_transaction_update (decode_represented_snapshot dec S) (decode_represented_transaction dec T))
     else Finite_Conflict (finite_observed_comparison (decode_represented_snapshot dec S) (decode_represented_transaction dec T)))"
  by (cases "represented_comparison_passes S T")
    (simp_all add: represented_transaction_step_def represented_comparison_passes_decoded[OF inj S T, symmetric]
      represented_transaction_update_decoded[OF inj S T] represented_observed_comparison_decoded[OF inj S T])

lemma represented_transaction_step_applied:
  assumes "represented_transaction_step S T=Represented_Applied U"
  shows "represented_snapshot_targets U\<subseteq>represented_snapshot_targets S\<union>represented_transaction_targets T"
  using assms represented_transaction_update_targets[of S T]
  by (auto simp: represented_transaction_step_def split: if_split_asm)

definition represented_transact :: "('t \<Rightarrow> bool) \<Rightarrow> 't represented_snapshot \<Rightarrow> 't represented_transaction \<Rightarrow>
    't represented_transaction_result option" where
  "represented_transact tf S T=(if represented_snapshot_formed tf S \<and> represented_transaction_formed tf T
    then Some (represented_transaction_step S T) else None)"

definition represented_transact_formed :: "('t \<Rightarrow> bool) \<Rightarrow> 't represented_snapshot \<Rightarrow>
    't represented_transaction \<Rightarrow> 't represented_transaction_result option" where
  "represented_transact_formed tf S T=(if represented_transaction_formed tf T
    then Some (represented_transaction_step S T) else None)"

definition represented_transact_body :: "('t \<Rightarrow> bool) \<Rightarrow> 't represented_snapshot \<Rightarrow>
    't represented_transaction \<Rightarrow> 't represented_transaction_result option" where
  "represented_transact_body tf S T=(if represented_transaction_body_formed tf T
    then Some (represented_transaction_step S T) else None)"

theorem represented_transact_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
    and T: "represented_transaction_targets T\<subseteq>K"
  shows "map_option (decode_represented_result dec) (represented_transact (\<lambda>t. finite_target_formed (dec t)) S T)=
    finite_transact (decode_represented_snapshot dec S) (decode_represented_transaction dec T)"
  by (simp add: represented_transact_def finite_transact_def represented_snapshot_formed_decoded[OF inj S]
    represented_transaction_formed_decoded[OF inj T] represented_transaction_step_decoded[OF inj S T])

theorem represented_transact_formed_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
    and T: "represented_transaction_targets T\<subseteq>K"
  shows "map_option (decode_represented_result dec) (represented_transact_formed (\<lambda>t. finite_target_formed (dec t)) S T)=
    finite_transact_formed (decode_represented_snapshot dec S) (decode_represented_transaction dec T)"
  by (simp add: represented_transact_formed_def finite_transact_formed_def
    represented_transaction_formed_decoded[OF inj T] represented_transaction_step_decoded[OF inj S T])

theorem represented_transact_body_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
    and T: "represented_transaction_targets T\<subseteq>K"
  shows "map_option (decode_represented_result dec) (represented_transact_body (\<lambda>t. finite_target_formed (dec t)) S T)=
    finite_transact_body (decode_represented_snapshot dec S) (decode_represented_transaction dec T)"
  by (simp add: represented_transact_body_def finite_transact_body_def
    represented_transaction_body_formed_decoded[OF inj T] represented_transaction_step_decoded[OF inj S T])

lemma represented_transact_applied:
  "represented_transact tf S T=Some (Represented_Applied U) \<Longrightarrow>
    represented_snapshot_targets U\<subseteq>represented_snapshot_targets S\<union>represented_transaction_targets T"
  "represented_transact_formed tf S T=Some (Represented_Applied U) \<Longrightarrow>
    represented_snapshot_targets U\<subseteq>represented_snapshot_targets S\<union>represented_transaction_targets T"
  "represented_transact_body tf S T=Some (Represented_Applied U) \<Longrightarrow>
    represented_snapshot_targets U\<subseteq>represented_snapshot_targets S\<union>represented_transaction_targets T"
  using represented_transaction_step_applied[of S T U]
  by (auto simp: represented_transact_def represented_transact_formed_def represented_transact_body_def
    split: if_split_asm)

lemma represented_transact_body_established:
  "established_premise (represented_transact_formed tf S)
    (\<lambda>T. fBall (represented_transaction_generations T) (represented_generation_formed tf))
    (represented_transact_body tf S)"
  by unfold_locales
    (simp add: represented_transact_formed_def represented_transact_body_def
      represented_transaction_formed_generations)

section \<open>Replacement and admission at one locus\<close>

definition represented_replacement_transaction ::
    "'t generation_structure \<Rightarrow> 't generation_structure \<Rightarrow> 't represented_transaction" where
  "represented_replacement_transaction G H=\<lparr>represented_expected_selected={|G|},
    represented_expected_absent={||},represented_proposed_selected={|H|},represented_proposed_absent={||}\<rparr>"

definition represented_admission_transaction :: "'t represented_snapshot \<Rightarrow> 't represented_transaction" where
  "represented_admission_transaction W=\<lparr>represented_expected_selected={||},
    represented_expected_absent=represented_snapshot_loci W,represented_proposed_selected=W,
    represented_proposed_absent={||}\<rparr>"

definition represented_locus_transaction ::
    "'t generation_structure option \<Rightarrow> 't generation_structure \<Rightarrow> 't represented_transaction" where
  "represented_locus_transaction expected H=(case expected of
     None \<Rightarrow> represented_admission_transaction {|H|}
   | Some G \<Rightarrow> represented_replacement_transaction G H)"

lemma represented_locus_transaction_decoded:
  "decode_represented_transaction dec (represented_locus_transaction I G)=
    finite_locus_transaction (map_option (map_generation_structure dec) I) (map_generation_structure dec G)"
  by (cases I) (simp_all add: represented_locus_transaction_def finite_locus_transaction_def
    represented_admission_transaction_def finite_admission_transaction_def
    represented_replacement_transaction_def finite_replacement_transaction_def
    decode_represented_transaction_def decode_represented_snapshot_def
    represented_snapshot_loci_def finite_snapshot_loci_def)

lemma represented_locus_transaction_targets:
  "represented_transaction_targets (represented_locus_transaction I G)\<subseteq>
    (\<Union>H\<in>set_option I. set_generation_structure H)\<union>set_generation_structure G"
  by (cases I) (auto simp: represented_locus_transaction_def represented_admission_transaction_def
    represented_replacement_transaction_def represented_transaction_targets_def represented_snapshot_targets_def
    represented_snapshot_loci_def represented_locus_target)

lemma represented_locus_transaction_generations:
  "fBall (represented_transaction_generations (represented_locus_transaction I G)) (represented_generation_formed tf) \<longleftrightarrow>
    pred_option (represented_generation_formed tf) I \<and> represented_generation_formed tf G"
  by (cases I) (simp_all add: represented_locus_transaction_def represented_admission_transaction_def
    represented_replacement_transaction_def represented_transaction_generations_def conj_commute)

section \<open>Publishing several generations in turn\<close>

text \<open>
  The three publications of @{text RRA_Formed_Snapshot_Transactions} differ only in the transaction
  each step executes, so they are stated once over that transaction.
\<close>

fun represented_publications_with ::
    "('t represented_snapshot \<Rightarrow> 't represented_transaction \<Rightarrow> 't represented_transaction_result option) \<Rightarrow>
      't represented_snapshot \<Rightarrow> ('t generation_structure option\<times>'t generation_structure option) list \<Rightarrow>
      't represented_transaction_result option list" where
  "represented_publications_with tx S []=[]"
| "represented_publications_with tx S ((I,A)#ps)=(case A of
     None \<Rightarrow> None#represented_publications_with tx S ps
   | Some G \<Rightarrow> (let result=tx S (represented_locus_transaction I G) in
       result#(case result of Some (Represented_Applied U) \<Rightarrow> represented_publications_with tx U ps
         | _ \<Rightarrow> represented_publications_with tx S ps)))"

definition represented_locus_publications :: "('t \<Rightarrow> bool) \<Rightarrow> 't represented_snapshot \<Rightarrow>
    ('t generation_structure option\<times>'t generation_structure option) list \<Rightarrow> 't represented_transaction_result option list" where
  "represented_locus_publications tf=represented_publications_with (represented_transact tf)"

definition represented_locus_publications_formed :: "('t \<Rightarrow> bool) \<Rightarrow> 't represented_snapshot \<Rightarrow>
    ('t generation_structure option\<times>'t generation_structure option) list \<Rightarrow> 't represented_transaction_result option list" where
  "represented_locus_publications_formed tf=represented_publications_with (represented_transact_formed tf)"

definition represented_locus_publications_body :: "('t \<Rightarrow> bool) \<Rightarrow> 't represented_snapshot \<Rightarrow>
    ('t generation_structure option\<times>'t generation_structure option) list \<Rightarrow> 't represented_transaction_result option list" where
  "represented_locus_publications_body tf=represented_publications_with (represented_transact_body tf)"

definition represented_publications_targets ::
    "('t generation_structure option\<times>'t generation_structure option) list \<Rightarrow> 't set" where
  "represented_publications_targets ps=
    (\<Union>(I,A)\<in>set ps. \<Union>G\<in>set_option I\<union>set_option A. set_generation_structure G)"

definition decode_represented_publications :: "('t \<Rightarrow> finite_exact_target) \<Rightarrow>
    ('t generation_structure option\<times>'t generation_structure option) list \<Rightarrow>
    (finite_generation option\<times>finite_generation option) list" where
  "decode_represented_publications dec=
    map (map_prod (map_option (map_generation_structure dec)) (map_option (map_generation_structure dec)))"

lemma decode_represented_publications_identity [simp]: "decode_represented_publications id ps=ps"
  by (simp add: decode_represented_publications_def generation_structure.map_id0 option.map_id0 prod.map_id0)

lemma represented_publications_with_decoded:
  assumes inj: "inj_on dec K"
    and step: "\<And>S T. represented_snapshot_targets S\<subseteq>K \<Longrightarrow> represented_transaction_targets T\<subseteq>K \<Longrightarrow>
      map_option (decode_represented_result dec) (tx S T)=
        tx' (decode_represented_snapshot dec S) (decode_represented_transaction dec T)"
    and applied: "\<And>S T U. tx S T=Some (Represented_Applied U) \<Longrightarrow>
      represented_snapshot_targets U\<subseteq>represented_snapshot_targets S\<union>represented_transaction_targets T"
    and nil: "\<And>S. F S []=[]"
    and cons: "\<And>S I A ps. F S ((I,A)#ps)=(case A of None \<Rightarrow> None#F S ps
      | Some G \<Rightarrow> (let r=tx' S (finite_locus_transaction I G) in
          r#(case r of Some (Finite_Applied U) \<Rightarrow> F U ps | _ \<Rightarrow> F S ps)))"
  shows "represented_snapshot_targets S\<subseteq>K \<Longrightarrow> represented_publications_targets ps\<subseteq>K \<Longrightarrow>
    map (map_option (decode_represented_result dec)) (represented_publications_with tx S ps)=
      F (decode_represented_snapshot dec S) (decode_represented_publications dec ps)"
proof (induction ps arbitrary: S)
  case Nil
  then show ?case by (simp add: nil decode_represented_publications_def)
next
  case (Cons q ps)
  obtain I A where q: "q=(I,A)" by (cases q) auto
  have rest: "represented_publications_targets ps\<subseteq>K"
    using Cons.prems(2) by (auto simp: represented_publications_targets_def)
  have decoded: "decode_represented_publications dec ((I,A)#ps)=
      (map_option (map_generation_structure dec) I,map_option (map_generation_structure dec) A)#
        decode_represented_publications dec ps"
    by (simp add: decode_represented_publications_def)
  show ?case
  proof (cases A)
    case None
    then show ?thesis using Cons.IH[OF Cons.prems(1) rest] by (simp add: q decode_represented_publications_def cons)
  next
    case (Some G)
    let ?T="represented_locus_transaction I G"
    have T: "represented_transaction_targets ?T\<subseteq>K"
      using represented_locus_transaction_targets[of I G] Cons.prems(2) Some
      by (auto simp: represented_publications_targets_def q)
    have result: "map_option (decode_represented_result dec) (tx S ?T)=
        tx' (decode_represented_snapshot dec S)
          (finite_locus_transaction (map_option (map_generation_structure dec) I) (map_generation_structure dec G))"
      using step[OF Cons.prems(1) T] by (simp add: represented_locus_transaction_decoded)
    show ?thesis
    proof (cases "tx S ?T")
      case None
      then show ?thesis using result[symmetric] Cons.IH[OF Cons.prems(1) rest]
        by (simp add: q \<open>A=Some G\<close> decode_represented_publications_def cons Let_def)
    next
      case (Some r)
      note found=this
      show ?thesis
      proof (cases r)
        case (Represented_Applied U)
        have U: "represented_snapshot_targets U\<subseteq>K"
          using applied[of S ?T U] found Represented_Applied Cons.prems(1) T by blast
        show ?thesis using result[symmetric] Cons.IH[OF U rest] found Represented_Applied
          by (simp add: q \<open>A=Some G\<close> decode_represented_publications_def cons Let_def)
      next
        case (Represented_Conflict C)
        show ?thesis using result[symmetric] Cons.IH[OF Cons.prems(1) rest] found Represented_Conflict
          by (simp add: q \<open>A=Some G\<close> decode_represented_publications_def cons Let_def)
      qed
    qed
  qed
qed

theorem represented_locus_publications_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
    and ps: "represented_publications_targets ps\<subseteq>K"
  shows "map (map_option (decode_represented_result dec))
      (represented_locus_publications (\<lambda>t. finite_target_formed (dec t)) S ps)=
    finite_locus_publications (decode_represented_snapshot dec S) (decode_represented_publications dec ps)"
  unfolding represented_locus_publications_def
  by (rule represented_publications_with_decoded[OF inj _ represented_transact_applied(1) _ _ S ps])
    (simp_all add: represented_transact_decoded[OF inj])

theorem represented_locus_publications_formed_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
    and ps: "represented_publications_targets ps\<subseteq>K"
  shows "map (map_option (decode_represented_result dec))
      (represented_locus_publications_formed (\<lambda>t. finite_target_formed (dec t)) S ps)=
    finite_locus_publications_formed (decode_represented_snapshot dec S) (decode_represented_publications dec ps)"
  unfolding represented_locus_publications_formed_def
  by (rule represented_publications_with_decoded[OF inj _ represented_transact_applied(2) _ _ S ps])
    (simp_all add: represented_transact_formed_decoded[OF inj])

theorem represented_locus_publications_body_decoded:
  assumes inj: "inj_on dec K" and S: "represented_snapshot_targets S\<subseteq>K"
    and ps: "represented_publications_targets ps\<subseteq>K"
  shows "map (map_option (decode_represented_result dec))
      (represented_locus_publications_body (\<lambda>t. finite_target_formed (dec t)) S ps)=
    finite_locus_publications_body (decode_represented_snapshot dec S) (decode_represented_publications dec ps)"
  unfolding represented_locus_publications_body_def
  by (rule represented_publications_with_decoded[OF inj _ represented_transact_applied(3) _ _ S ps])
    (simp_all add: represented_transact_body_decoded[OF inj])

section \<open>At exact targets with the identity, the existing operations\<close>

lemma represented_transact_exact:
  "map_option (decode_represented_result id) (represented_transact finite_target_formed S T)=
    finite_transact S (decode_represented_transaction id T)"
  using represented_transact_decoded[of id UNIV S T] by simp

lemma represented_transact_formed_exact:
  "map_option (decode_represented_result id) (represented_transact_formed finite_target_formed S T)=
    finite_transact_formed S (decode_represented_transaction id T)"
  using represented_transact_formed_decoded[of id UNIV S T] by simp

lemma represented_transact_body_exact:
  "map_option (decode_represented_result id) (represented_transact_body finite_target_formed S T)=
    finite_transact_body S (decode_represented_transaction id T)"
  using represented_transact_body_decoded[of id UNIV S T] by simp

lemma represented_locus_transaction_exact:
  "decode_represented_transaction id (represented_locus_transaction I G)=finite_locus_transaction I G"
  using represented_locus_transaction_decoded[of id I G]
  by (simp add: generation_structure.map_id0 option.map_id0)

lemma represented_locus_publications_exact:
  "map (map_option (decode_represented_result id)) (represented_locus_publications finite_target_formed S ps)=
    finite_locus_publications S ps"
  using represented_locus_publications_decoded[of id UNIV S ps] by simp

lemma represented_locus_publications_formed_exact:
  "map (map_option (decode_represented_result id)) (represented_locus_publications_formed finite_target_formed S ps)=
    finite_locus_publications_formed S ps"
  using represented_locus_publications_formed_decoded[of id UNIV S ps] by simp

lemma represented_locus_publications_body_exact:
  "map (map_option (decode_represented_result id)) (represented_locus_publications_body finite_target_formed S ps)=
    finite_locus_publications_body S ps"
  using represented_locus_publications_body_decoded[of id UNIV S ps] by simp

section \<open>The body publications over formed generations, at every representation\<close>

text \<open>
  Where every generation a list publishes is formed, as where each was made by a constructor whose
  contract states it formed, the publications check only the rest of each transaction: the instance
  @{thm [source] finite_locus_publications_body_established} of @{text Established_Premises}, stated
  at every representation of the targets and every formation of a target.
\<close>

definition represented_publications_formed_generations :: "('t \<Rightarrow> bool) \<Rightarrow>
    ('t generation_structure option\<times>'t generation_structure option) list \<Rightarrow> bool" where
  "represented_publications_formed_generations tf ps \<longleftrightarrow>
    (\<forall>(I,A)\<in>set ps. pred_option (represented_generation_formed tf) I \<and> pred_option (represented_generation_formed tf) A)"

lemma represented_locus_publications_body_established:
  "established_premise (represented_locus_publications_formed tf S)
    (represented_publications_formed_generations tf) (represented_locus_publications_body tf S)"
proof unfold_locales
  fix ps
  assume "represented_publications_formed_generations tf ps"
  then show "represented_locus_publications_formed tf S ps=represented_locus_publications_body tf S ps"
    unfolding represented_locus_publications_formed_def represented_locus_publications_body_def
  proof (induction ps arbitrary: S)
    case Nil
    then show ?case by simp
  next
    case (Cons q ps)
    obtain I A where q: "q=(I,A)" by (cases q) auto
    have rest: "represented_publications_formed_generations tf ps"
      and here: "pred_option (represented_generation_formed tf) I" "pred_option (represented_generation_formed tf) A"
      using Cons.prems by (simp_all add: represented_publications_formed_generations_def q)
    show ?case
    proof (cases A)
      case None
      then show ?thesis using Cons.IH[OF rest] by (simp add: q)
    next
      case (Some G)
      have premise: "fBall (represented_transaction_generations (represented_locus_transaction I G))
          (represented_generation_formed tf)"
        using here Some by (simp add: represented_locus_transaction_generations)
      have same: "represented_transact_formed tf S (represented_locus_transaction I G)=
          represented_transact_body tf S (represented_locus_transaction I G)"
        by (rule established_premise.exact[OF represented_transact_body_established premise])
      show ?thesis using Cons.IH[OF rest] same
        by (simp add: q Some Let_def split: option.split represented_transaction_result.split)
    qed
  qed
qed

lemma represented_publications_formed_generations_decoded:
  "represented_publications_formed_generations (\<lambda>t. finite_target_formed (dec t)) ps \<longleftrightarrow>
    finite_publications_formed_generations (decode_represented_publications dec ps)"
proof -
  have each: "pred_option finite_generation_formed (map_option (map_generation_structure dec) I) \<longleftrightarrow>
      pred_option (represented_generation_formed (\<lambda>t. finite_target_formed (dec t))) I" for I
    by (cases I) (simp_all add: represented_generation_formed_decoded)
  show ?thesis
    by (simp add: represented_publications_formed_generations_def finite_publications_formed_generations_def
      decode_represented_publications_def split_def represented_ball_image each)
qed

export_code represented_snapshot_loci represented_snapshot_formed represented_snapshot_lookup
  represented_comparison_loci represented_changed_loci represented_transaction_formed
  represented_transaction_body_formed represented_comparison_passes represented_transaction_update
  represented_observed_comparison represented_transact represented_transact_formed represented_transact_body
  represented_locus_transaction represented_locus_publications represented_locus_publications_formed
  represented_locus_publications_body decode_represented_result
  checking SML

end
