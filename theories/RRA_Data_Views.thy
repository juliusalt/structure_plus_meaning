theory RRA_Data_Views
  imports RRA_Data
begin

datatype ('a,'v) legacy_data =
    Legacy_No_Data
  | Legacy_Functional_Data "('a \<times> 'v) set"
  | Legacy_Bag_Data "('a \<times> 'v \<times> nat) set"
  | Legacy_Node_Data "('a \<times> 'a \<times> 'v) set"

definition legacy_pair_functional :: "('a \<times> 'b) set \<Rightarrow> bool" where
  "legacy_pair_functional F \<longleftrightarrow> (\<forall>a x y. (a,x) \<in> F \<longrightarrow> (a,y) \<in> F \<longrightarrow> x = y)"

definition legacy_bag_functional :: "('a \<times> 'b \<times> nat) set \<Rightarrow> bool" where
  "legacy_bag_functional B \<longleftrightarrow>
     (\<forall>a v m n. (a,v,m) \<in> B \<longrightarrow> (a,v,n) \<in> B \<longrightarrow> m = n)"

definition legacy_node_functional :: "('a \<times> 'a \<times> 'b) set \<Rightarrow> bool" where
  "legacy_node_functional N \<longleftrightarrow>
     (\<forall>d a v b w. (d,a,v) \<in> N \<longrightarrow> (d,b,w) \<in> N \<longrightarrow> a = b \<and> v = w)"

fun legacy_data_formed :: "'a set \<Rightarrow> ('a,'v) legacy_data \<Rightarrow> bool" where
  "legacy_data_formed U Legacy_No_Data = True"
| "legacy_data_formed U (Legacy_Functional_Data F) =
     (finite F \<and> legacy_pair_functional F \<and> (\<forall>a v. (a,v) \<in> F \<longrightarrow> a \<in> U))"
| "legacy_data_formed U (Legacy_Bag_Data B) =
     (finite B \<and> legacy_bag_functional B \<and>
      (\<forall>a v n. (a,v,n) \<in> B \<longrightarrow> a \<in> U \<and> n > 0))"
| "legacy_data_formed U (Legacy_Node_Data N) =
     (finite N \<and> legacy_node_functional N \<and>
      (\<forall>d a v. (d,a,v) \<in> N \<longrightarrow> d \<in> U \<and> a \<in> U))"

fun legacy_restrict_data :: "'a set \<Rightarrow> ('a,'v) legacy_data \<Rightarrow> ('a,'v) legacy_data" where
  "legacy_restrict_data A Legacy_No_Data = Legacy_No_Data"
| "legacy_restrict_data A (Legacy_Functional_Data F) =
     Legacy_Functional_Data {t \<in> F. fst t \<in> A}"
| "legacy_restrict_data A (Legacy_Bag_Data B) =
     Legacy_Bag_Data {t \<in> B. fst t \<in> A}"
| "legacy_restrict_data A (Legacy_Node_Data N) =
     Legacy_Node_Data {t \<in> N. fst t \<in> A \<and> fst (snd t) \<in> A}"

fun legacy_push_data :: "('a \<Rightarrow> 'b) \<Rightarrow> ('a,'v) legacy_data \<Rightarrow> ('b,'v) legacy_data" where
  "legacy_push_data f Legacy_No_Data = Legacy_No_Data"
| "legacy_push_data f (Legacy_Functional_Data F) =
     Legacy_Functional_Data {(f a,v) |a v. (a,v) \<in> F}"
| "legacy_push_data f (Legacy_Bag_Data B) =
     Legacy_Bag_Data {(f a,v,n) |a v n. (a,v,n) \<in> B}"
| "legacy_push_data f (Legacy_Node_Data N) =
     Legacy_Node_Data {(f d,f a,v) |d a v. (d,a,v) \<in> N}"


section \<open>Legacy views and their migration boundary\<close>

text \<open>
  The old selected profiles are source-language views used to state migration
  theorems. They are not alternatives selected by the new data core. Recovery
  records which legacy view was supplied; the empty views intentionally overlap
  after the old profile discriminator is removed.
\<close>

definition legacy_count :: "('a \<times> 'v \<times> nat) set \<Rightarrow> 'a \<Rightarrow> 'v \<Rightarrow> nat" where
  "legacy_count B a v =
    (if \<exists>n. (a,v,n) \<in> B then (THE n. (a,v,n) \<in> B) else 0)"

lemma legacy_count_value:
  assumes functional: "legacy_bag_functional B" and present: "(a,v,n) \<in> B"
  shows "legacy_count B a v = n"
proof -
  have unique: "(THE m. (a,v,m) \<in> B) = n"
    by (rule the_equality) (use functional present in \<open>auto simp: legacy_bag_functional_def\<close>)
  show ?thesis using present unique by (auto simp: legacy_count_def split: if_splits)
qed

lemma legacy_count_positive:
  assumes functional: "legacy_bag_functional B"
    and positive: "\<forall>a v n. (a,v,n) \<in> B \<longrightarrow> 0 < n"
  shows "0 < legacy_count B a v \<longleftrightarrow> (\<exists>n. (a,v,n) \<in> B)"
proof
  assume "0 < legacy_count B a v"
  then show "\<exists>n. (a,v,n) \<in> B" by (auto simp: legacy_count_def split: if_splits)
next
  assume "\<exists>n. (a,v,n) \<in> B"
  then obtain n where p: "(a,v,n) \<in> B" by blast
  show "0 < legacy_count B a v"
    using legacy_count_value[OF functional p] positive p by auto
qed

fun legacy_payload_basis :: "('a,'v) legacy_data \<Rightarrow> ('a,'v) opaque_basis" where
  "legacy_payload_basis Legacy_No_Data = empty_basis"
| "legacy_payload_basis (Legacy_Functional_Data F) =
    \<lparr>bag_count = (\<lambda>_. 0), functional_bindings = F\<rparr>"
| "legacy_payload_basis (Legacy_Bag_Data B) =
    \<lparr>bag_count = (\<lambda>(a,v). legacy_count B a v), functional_bindings = {}\<rparr>"
| "legacy_payload_basis (Legacy_Node_Data N) =
    \<lparr>bag_count = (\<lambda>_. 0),
     functional_bindings = (\<lambda>(d,u,v). (d,v)) ` N\<rparr>"

lemma legacy_bag_support:
  assumes functional: "legacy_bag_functional B"
    and positive: "\<forall>a v n. (a,v,n) \<in> B \<longrightarrow> 0 < n"
  shows "bag_support (legacy_payload_basis (Legacy_Bag_Data B)) =
    (\<lambda>(a,v,n). (a,v)) ` B"
  by (auto simp: bag_support_def legacy_count_positive[OF functional positive] intro: rev_image_eqI)

lemma legacy_payload_basis_formed:
  assumes "legacy_data_formed U D"
  shows "basis_formed U (legacy_payload_basis D)"
proof (cases D)
  case Legacy_No_Data
  then show ?thesis by simp
next
  case (Legacy_Functional_Data F)
  then show ?thesis using assms
    by (auto simp: basis_formed_def bag_support_def legacy_pair_functional_def single_valued_def)
next
  case (Legacy_Bag_Data B)
  have bf: "legacy_bag_functional B" using assms Legacy_Bag_Data by simp
  have pos: "\<forall>a v n. (a,v,n) \<in> B \<longrightarrow> 0 < n" using assms Legacy_Bag_Data by auto
  have support: "bag_support (legacy_payload_basis D) = (\<lambda>(a,v,n). (a,v)) ` B"
    using legacy_bag_support[OF bf pos] Legacy_Bag_Data by simp
  show ?thesis using assms Legacy_Bag_Data support
    by (auto simp: basis_formed_def single_valued_def)
next
  case (Legacy_Node_Data N)
  then show ?thesis using assms
    by (auto simp: basis_formed_def bag_support_def single_valued_def legacy_node_functional_def; blast)
qed

definition recover_functional_view :: "('a,'v) opaque_basis \<Rightarrow> ('a,'v) legacy_data" where
  "recover_functional_view D = Legacy_Functional_Data (functional_bindings D)"

definition recover_bag_view :: "('a,'v) opaque_basis \<Rightarrow> ('a,'v) legacy_data" where
  "recover_bag_view D = Legacy_Bag_Data {(a,v,n). bag_count D (a,v) = n \<and> 0 < n}"

lemma functional_view_round_trip:
  "recover_functional_view (legacy_payload_basis (Legacy_Functional_Data F)) = Legacy_Functional_Data F"
  by (simp add: recover_functional_view_def)

lemma bag_view_round_trip:
  fixes B :: "('a \<times> 'v \<times> nat) set"
  assumes functional: "legacy_bag_functional B"
    and positive: "\<forall>a v n. (a,v,n) \<in> B \<longrightarrow> 0 < n"
  shows "recover_bag_view (legacy_payload_basis (Legacy_Bag_Data B)) = Legacy_Bag_Data B"
proof -
  have bf: "legacy_bag_functional B" using functional .
  have pos: "\<forall>a v n. (a,v,n) \<in> B \<longrightarrow> 0 < n" using positive .
  have eq: "{(a,v,n). legacy_count B a v = n \<and> 0 < n} = B"
  proof (rule set_eqI)
    fix avn :: "'a \<times> 'v \<times> nat"
    obtain a v n where avn: "avn = (a,v,n)" by (cases avn)
    show "avn \<in> {(a,v,n). legacy_count B a v = n \<and> 0 < n} \<longleftrightarrow> avn \<in> B"
    proof
      assume left: "avn \<in> {(a,v,n). legacy_count B a v = n \<and> 0 < n}"
      then have nonzero: "0 < legacy_count B a v" using avn by auto
      from legacy_count_positive[OF bf pos, where a=a and v=v] nonzero
      obtain m where am: "(a,v,m) \<in> B" by blast
      have "m = n" using legacy_count_value[OF bf am] left avn by simp
      with am avn show "avn \<in> B" by simp
    next
      assume right: "avn \<in> B"
      then have an: "(a,v,n) \<in> B" using avn by simp
      show "avn \<in> {(a,v,n). legacy_count B a v = n \<and> 0 < n}"
        using legacy_count_value[OF bf an] pos an avn by auto
    qed
  qed
  show ?thesis by (simp add: recover_bag_view_def eq)
qed

lemma empty_legacy_views_coincide:
  "legacy_payload_basis (Legacy_Functional_Data {}) = legacy_payload_basis Legacy_No_Data"
  by (simp add: empty_basis_def)

lemma profile_erasure_has_no_unqualified_inverse:
  "\<not> (\<exists>decode. \<forall>D :: ('a,'v) legacy_data. decode (legacy_payload_basis D) = D)"
proof
  assume "\<exists>decode. \<forall>D :: ('a,'v) legacy_data. decode (legacy_payload_basis D) = D"
  then obtain decode where dec: "\<And>D :: ('a,'v) legacy_data. decode (legacy_payload_basis D) = D"
    by blast
  have "Legacy_Functional_Data {} = (Legacy_No_Data :: ('a,'v) legacy_data)"
    using dec[of "Legacy_Functional_Data {}"] dec[of Legacy_No_Data] empty_legacy_views_coincide
    by (simp add: empty_basis_def)
  then show False by simp
qed

section \<open>Legacy gluing equations\<close>

definition positive_count_graph ::
  "(('a \<times> 'v) \<Rightarrow> nat) \<Rightarrow> ('a \<times> 'v \<times> nat) set" where
  "positive_count_graph b = {(a,v,n). b (a,v) = n \<and> 0 < n}"

lemma positive_count_graph_functional:
  "legacy_bag_functional (positive_count_graph b)"
  by (auto simp: positive_count_graph_def legacy_bag_functional_def)

lemma legacy_count_positive_graph:
  "legacy_count (positive_count_graph b) a v = b (a,v)"
proof (cases "b (a,v) = 0")
  case True
  then show ?thesis by (simp add: legacy_count_def positive_count_graph_def)
next
  case False
  have p: "(a,v,b (a,v)) \<in> positive_count_graph b"
    using False by (simp add: positive_count_graph_def)
  show ?thesis by (rule legacy_count_value[OF positive_count_graph_functional p])
qed

lemma legacy_payload_positive_graph:
  "legacy_payload_basis (Legacy_Bag_Data (positive_count_graph b)) =
    \<lparr>bag_count = b, functional_bindings = {}\<rparr>"
  by (auto simp: basis_identity fun_eq_iff legacy_count_positive_graph)

lemma recover_positive_graph:
  "recover_bag_view (legacy_payload_basis (Legacy_Bag_Data (positive_count_graph b))) =
    Legacy_Bag_Data (positive_count_graph b)"
  by (simp only: legacy_payload_positive_graph;
      simp add: recover_bag_view_def positive_count_graph_def)

lemma positive_count_graph_image:
  "positive_count_graph b = (\<lambda>(a,v). (a,v,b (a,v))) ` {av. b av \<noteq> 0}"
  by (auto simp: positive_count_graph_def intro: rev_image_eqI)

lemma recover_bag_view_formed:
  assumes formed: "basis_formed U D"
  shows "legacy_data_formed U (recover_bag_view D)"
proof -
  have fin: "finite (positive_count_graph (bag_count D))"
    using formed by (simp add: positive_count_graph_image basis_formed_def bag_support_def)
  show ?thesis using formed fin
    by (auto simp: recover_bag_view_def positive_count_graph_def basis_formed_def
      bag_support_def legacy_bag_functional_def)
qed

definition legacy_expected_bag ::
  "'a set \<Rightarrow> ('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'v \<times> nat) set \<Rightarrow>
   ('b \<times> 'v \<times> nat) set" where
  "legacy_expected_bag U f B = positive_count_graph
    (\<lambda>(y,v). \<Sum>a\<in>U. if f a = y then legacy_count B a v else 0)"

lemma legacy_bag_gluing_commutes:
  "legacy_payload_basis (Legacy_Bag_Data (legacy_expected_bag U f B)) =
    push_basis U f (legacy_payload_basis (Legacy_Bag_Data B))"
  by (auto simp: basis_identity legacy_expected_bag_def push_basis_def
    pushed_count_def fun_eq_iff legacy_count_positive_graph)

lemma legacy_bag_graph:
  "legacy_expected_bag U f B =
    positive_count_graph (pushed_count U f (\<lambda>(a,v). legacy_count B a v))"
proof -
  have counts: "(\<lambda>(y,v). \<Sum>a\<in>U. if f a = y then legacy_count B a v else 0) =
    pushed_count U f (\<lambda>(a,v). legacy_count B a v)"
    by (auto simp: pushed_count_def fun_eq_iff intro!: sum.cong)
  show ?thesis by (simp only: legacy_expected_bag_def counts)
qed

lemma legacy_bag_renaming:
  fixes B :: "('a \<times> 'v \<times> nat) set" and f :: "'a \<Rightarrow> 'b"
  assumes fin: "finite U" and formed: "legacy_data_formed U (Legacy_Bag_Data B)" and injective: "inj_on f U"
  shows "legacy_expected_bag U f B = (\<lambda>(a,v,n). (f a,v,n)) ` B"
proof (rule set_eqI)
  fix yvn :: "'b \<times> 'v \<times> nat"
  obtain y v n where yvn: "yvn = (y,v,n)" by (cases yvn)
  have bf: "legacy_bag_functional B" using formed by simp
  have pos: "\<forall>a v n. (a,v,n) \<in> B \<longrightarrow> 0 < n" using formed by auto
  let ?b = "\<lambda>(a,v). legacy_count B a v"
  show "yvn \<in> legacy_expected_bag U f B \<longleftrightarrow>
        yvn \<in> (\<lambda>(a,v,n). (f a,v,n)) ` B"
  proof
    assume in_output: "yvn \<in> legacy_expected_bag U f B"
    then have pn: "pushed_count U f ?b (y,v) = n" and nz: "0 < n"
      by (auto simp: yvn legacy_bag_graph positive_count_graph_def)
    have nonzero: "pushed_count U f ?b (y,v) \<noteq> 0" using pn nz by simp
    from pushed_count_origin[OF nonzero] obtain a where
      au: "a \<in> U" and ay: "f a = y" and av: "0 < legacy_count B a v" by auto
    from legacy_count_positive[OF bf pos, where a=a and v=v] av
    obtain m where am: "(a,v,m) \<in> B" by blast
    have cp: "pushed_count U f ?b (f a,v) = legacy_count B a v"
      using pushed_count_injective[where b="?b" and x=a and v=v, OF fin injective au] by simp
    have mn: "m = n" using pn cp ay legacy_count_value[OF bf am] by simp
    show "yvn \<in> (\<lambda>(a,v,n). (f a,v,n)) ` B"
      by (rule image_eqI[where x="(a,v,m)"]) (use yvn ay mn am in auto)
  next
    assume "yvn \<in> (\<lambda>(a,v,n). (f a,v,n)) ` B"
    then obtain a where an: "(a,v,n) \<in> B" and ay: "f a = y"
      by (auto simp: yvn)
    have au: "a \<in> U" using formed an by auto
    have cp: "pushed_count U f ?b (f a,v) = legacy_count B a v"
      using pushed_count_injective[where b="?b" and x=a and v=v, OF fin injective au] by simp
    show "yvn \<in> legacy_expected_bag U f B"
      using cp ay legacy_count_value[OF bf an] pos an
      by (auto simp: yvn legacy_bag_graph positive_count_graph_def)
  qed
qed

lemma legacy_bag_gluing_formed:
  assumes formed: "legacy_data_formed U (Legacy_Bag_Data B)"
  shows "legacy_data_formed (f ` U) (Legacy_Bag_Data (legacy_expected_bag U f B))"
proof -
  have source: "basis_formed U (legacy_payload_basis (Legacy_Bag_Data B))"
    by (rule legacy_payload_basis_formed[OF formed])
  have compatible: "basis_compatible f (legacy_payload_basis (Legacy_Bag_Data B))"
    by (simp add: basis_compatible_def)
  have target: "basis_formed (f ` U) (push_basis U f (legacy_payload_basis (Legacy_Bag_Data B)))"
    using push_basis_formed_iff[OF source, where f=f] compatible by simp
  show ?thesis
    using recover_bag_view_formed[OF target]
    by (simp only: legacy_bag_gluing_commutes[symmetric]
      legacy_expected_bag_def recover_positive_graph)
qed

lemma legacy_bag_gluing_boundary:
  assumes "(y,v,n) \<in> legacy_expected_bag U f B"
  shows "y \<in> f ` U \<and> (\<exists>a m. (a,v,m) \<in> B)"
proof -
  have nz: "pushed_count U f (\<lambda>(a,v). legacy_count B a v) (y,v) \<noteq> 0"
    using assms by (auto simp: legacy_expected_bag_def positive_count_graph_def pushed_count_def)
  from pushed_count_origin[OF nz] obtain a where
    au: "a \<in> U" and ay: "f a = y" and av: "legacy_count B a v \<noteq> 0"
    by auto
  show ?thesis using au ay av
    by (auto simp: legacy_count_def split: if_splits intro: rev_image_eqI)
qed

lemma legacy_functional_gluing_commutes:
  "legacy_payload_basis (Legacy_Functional_Data ((\<lambda>(a,v). (f a,v)) ` F)) =
    push_basis U f (legacy_payload_basis (Legacy_Functional_Data F))"
  by (simp add: basis_identity push_basis_def pushed_count_def fun_eq_iff)

lemma legacy_functional_formation_iff:
  "basis_formed U (legacy_payload_basis (Legacy_Functional_Data F)) \<longleftrightarrow>
    legacy_data_formed U (Legacy_Functional_Data F)"
  by (auto simp: basis_formed_def bag_support_def single_valued_def legacy_pair_functional_def)

lemma legacy_functional_gluing_formation:
  assumes formed: "legacy_data_formed U (Legacy_Functional_Data F)"
  shows "legacy_data_formed (f ` U) (Legacy_Functional_Data ((\<lambda>(a,v). (f a,v)) ` F)) \<longleftrightarrow>
    basis_compatible f (legacy_payload_basis (Legacy_Functional_Data F))"
proof -
  have source: "basis_formed U (legacy_payload_basis (Legacy_Functional_Data F))"
    by (rule legacy_payload_basis_formed[OF formed])
  show ?thesis
    using push_basis_formed_iff[OF source, where f=f]
    by (simp only: legacy_functional_gluing_commutes[symmetric] legacy_functional_formation_iff)
qed

section \<open>Addressable data ownership as incidence\<close>

definition node_owner_incidence ::
  "('a \<times> 'a \<times> 'v) set \<Rightarrow> (('a + 'a) \<times> ('a + 'a) \<times> ('a + 'a)) set" where
  "node_owner_incidence N = (\<lambda>(d,u,v). (Inr d,Inl d,Inl u)) ` N"

definition node_migration_structure ::
  "'a rra_structure \<Rightarrow> ('a \<times> 'a \<times> 'v) set \<Rightarrow> ('a + 'a) rra_structure" where
  "node_migration_structure S N =
    \<lparr>rra_carrier = Inl ` rra_carrier S \<union> Inr ` (fst ` N),
     rra_incidence = rra_incidence (push_structure Inl S) \<union> node_owner_incidence N\<rparr>"

definition node_migration_basis ::
  "('a \<times> 'a \<times> 'v) set \<Rightarrow> ('a + 'a,'v) opaque_basis" where
  "node_migration_basis N =
    \<lparr>bag_count = (\<lambda>_. 0),
     functional_bindings = (\<lambda>(d,u,v). (Inl d,v)) ` N\<rparr>"

definition recover_source_structure :: "('a + 'a) rra_structure \<Rightarrow> 'a rra_structure" where
  "recover_source_structure T =
    \<lparr>rra_carrier = {a. Inl a \<in> rra_carrier T},
     rra_incidence = {(r,p,x). (Inl r,Inl p,Inl x) \<in> rra_incidence T}\<rparr>"

definition recover_node_view ::
  "('a + 'a) rra_structure \<Rightarrow> ('a + 'a,'v) opaque_basis \<Rightarrow> ('a,'v) legacy_data" where
  "recover_node_view T D = Legacy_Node_Data
    {(d,u,v). (Inr d,Inl d,Inl u) \<in> rra_incidence T \<and>
              (Inl d,v) \<in> functional_bindings D}"

lemma node_source_round_trip:
  "recover_source_structure (node_migration_structure S N) = S"
  by (cases S)
     (auto simp: recover_source_structure_def node_migration_structure_def
       node_owner_incidence_def push_structure_def intro: rev_image_eqI)

lemma node_migration_structure_formed:
  assumes "rra_formed S" "legacy_data_formed (rra_carrier S) (Legacy_Node_Data N)"
  shows "rra_formed (node_migration_structure S N)"
proof -
  have fin: "finite N" using assms(2) by simp
  have loc: "\<And>d u v. (d,u,v) \<in> N \<Longrightarrow> d \<in> rra_carrier S \<and> u \<in> rra_carrier S"
    using assms(2) by auto
  show ?thesis using assms(1) fin
    by (auto simp: rra_formed_def node_migration_structure_def
      node_owner_incidence_def push_structure_def intro: rev_image_eqI dest: loc)
qed

lemma node_basis_is_payload_push:
  "push_basis U Inl (legacy_payload_basis (Legacy_Node_Data N)) = node_migration_basis N"
  by (auto simp: basis_identity node_migration_basis_def push_basis_def
    pushed_count_def fun_eq_iff image_image intro: rev_image_eqI)

lemma node_migration_basis_formed:
  assumes "legacy_data_formed (rra_carrier S) (Legacy_Node_Data N)"
  shows "basis_formed (rra_carrier (node_migration_structure S N)) (node_migration_basis N)"
proof -
  have source: "basis_formed (rra_carrier S) (legacy_payload_basis (Legacy_Node_Data N))"
    by (rule legacy_payload_basis_formed[OF assms])
  have target: "basis_formed (Inl ` rra_carrier S) (node_migration_basis N)"
    apply (subst node_basis_is_payload_push[symmetric, where U="rra_carrier S"])
    apply (subst push_basis_formed_iff[OF source])
    apply (rule injective_gluing_compatible[OF source])
    apply (simp add: inj_on_def)
    done
  show ?thesis
    by (rule basis_formed_mono[OF target]) (auto simp: node_migration_structure_def)
qed

definition lifted_node_selection :: "'a set \<Rightarrow> ('a + 'a) set" where
  "lifted_node_selection A = Inl ` A \<union> Inr ` A"

lemma legacy_node_crossing_is_incidence:
  assumes "(d,u,v) \<in> N"
  shows "(Inr d,Inl d,Inl u) \<in>
      crossing_incidence (node_migration_structure S N) (lifted_node_selection A)
    \<longleftrightarrow> ((d \<in> A) \<noteq> (u \<in> A))"
proof -
  have edge: "(Inr d,Inl d,Inl u) \<in> rra_incidence (node_migration_structure S N)"
    using assms by (auto simp: node_migration_structure_def node_owner_incidence_def
      intro: rev_image_eqI)
  show ?thesis
    using edge by (auto simp: crossing_incidence_def touching_incidence_def
      internal_incidence_def lifted_node_selection_def)
qed

lemma node_owner_payload_coherence:
  assumes "legacy_node_functional N"
  shows "((\<exists>w. (d,u,w) \<in> N) \<and> (\<exists>a. (d,a,v) \<in> N)) \<longleftrightarrow> (d,u,v) \<in> N"
  using assms unfolding legacy_node_functional_def by blast

lemma node_view_round_trip:
  fixes N :: "('a \<times> 'a \<times> 'v) set" and S :: "'a rra_structure"
  assumes functional: "legacy_node_functional N"
  shows "recover_node_view (node_migration_structure S N) (node_migration_basis N) = Legacy_Node_Data N"
proof -
  have recovered: "{(d,u,v).
       (Inr d,Inl d,Inl u) \<in> rra_incidence (node_migration_structure S N) \<and>
       (Inl d,v) \<in> functional_bindings (node_migration_basis N)} = N"
  proof (rule set_eqI)
    fix duv :: "'a \<times> 'a \<times> 'v"
    obtain d u v where duv: "duv = (d,u,v)" by (cases duv)
    have edge: "(Inr d,Inl d,Inl u) \<in> rra_incidence (node_migration_structure S N)
        \<longleftrightarrow> (\<exists>w. (d,u,w) \<in> N)"
      by (auto simp: node_migration_structure_def node_owner_incidence_def
        push_structure_def intro: rev_image_eqI)
    have payload: "(Inl d,v) \<in> functional_bindings (node_migration_basis N)
        \<longleftrightarrow> (\<exists>a. (d,a,v) \<in> N)"
      by (auto simp: node_migration_basis_def intro: rev_image_eqI)
    show "duv \<in> {(d,u,v).
       (Inr d,Inl d,Inl u) \<in> rra_incidence (node_migration_structure S N) \<and>
       (Inl d,v) \<in> functional_bindings (node_migration_basis N)} \<longleftrightarrow> duv \<in> N"
      using node_owner_payload_coherence[OF functional, where d=d and u=u and v=v]
      by (simp add: duv edge payload)
  qed
  show ?thesis by (simp add: recover_node_view_def recovered)
qed

lemma node_migration_round_trip:
  assumes "legacy_data_formed (rra_carrier S) (Legacy_Node_Data N)"
  shows "(recover_source_structure (node_migration_structure S N),
          recover_node_view (node_migration_structure S N) (node_migration_basis N)) =
         (S, Legacy_Node_Data N)"
  using assms node_view_round_trip[of N S]
  by (simp add: node_source_round_trip)

definition legacy_expected_node ::
  "('a \<Rightarrow> 'b) \<Rightarrow> ('a \<times> 'a \<times> 'v) set \<Rightarrow> ('b \<times> 'b \<times> 'v) set" where
  "legacy_expected_node f N = (\<lambda>(d,u,v). (f d,f u,v)) ` N"

lemma node_structure_gluing_commutes:
  "push_structure (map_sum f f) (node_migration_structure S N) =
    node_migration_structure (push_structure f S) (legacy_expected_node f N)"
  by (auto simp: push_structure_def node_migration_structure_def node_owner_incidence_def
    legacy_expected_node_def image_Un image_image intro: rev_image_eqI)

lemma node_basis_gluing_commutes:
  "push_basis U (map_sum f f) (node_migration_basis N) =
    node_migration_basis (legacy_expected_node f N)"
  by (auto simp: basis_identity push_basis_def node_migration_basis_def legacy_expected_node_def
    pushed_count_def fun_eq_iff image_image intro: rev_image_eqI)

definition legacy_node_owners :: "('a \<times> 'a \<times> 'v) set \<Rightarrow> ('a \<times> 'a) set" where
  "legacy_node_owners N = {(d,u). \<exists>v. (d,u,v) \<in> N}"

definition legacy_node_payloads :: "('a \<times> 'a \<times> 'v) set \<Rightarrow> ('a \<times> 'v) set" where
  "legacy_node_payloads N = {(d,v). \<exists>u. (d,u,v) \<in> N}"

lemma node_functionality_decomposes:
  "legacy_node_functional N \<longleftrightarrow>
    single_valued (legacy_node_owners N) \<and> single_valued (legacy_node_payloads N)"
  unfolding legacy_node_functional_def single_valued_def legacy_node_owners_def legacy_node_payloads_def
  by blast

lemma legacy_node_payloads_basis:
  "legacy_node_payloads N = functional_bindings (legacy_payload_basis (Legacy_Node_Data N))"
  by (auto simp: legacy_node_payloads_def intro: rev_image_eqI)

lemma legacy_node_payload_transport:
  "legacy_node_payloads (legacy_expected_node f N) =
    functional_bindings (push_basis U f (legacy_payload_basis (Legacy_Node_Data N)))"
  by (auto simp: legacy_node_payloads_def legacy_expected_node_def push_basis_def
    image_image intro: rev_image_eqI)

lemma legacy_node_gluing_formation:
  assumes formed: "legacy_data_formed U (Legacy_Node_Data N)"
  shows "legacy_data_formed (f ` U) (Legacy_Node_Data (legacy_expected_node f N)) \<longleftrightarrow>
    basis_compatible f (legacy_payload_basis (Legacy_Node_Data N)) \<and>
    single_valued (legacy_node_owners (legacy_expected_node f N))"
proof -
  have fin: "finite (legacy_expected_node f N)"
    using formed by (auto simp: legacy_expected_node_def)
  have oldloc: "\<And>d u v. (d,u,v) \<in> N \<Longrightarrow> d \<in> U \<and> u \<in> U"
    using formed by auto
  have loc: "\<forall>d u v. (d,u,v) \<in> legacy_expected_node f N \<longrightarrow>
    d \<in> f ` U \<and> u \<in> f ` U"
    by (auto simp: legacy_expected_node_def intro: rev_image_eqI dest: oldloc)
  have formation: "legacy_data_formed (f ` U) (Legacy_Node_Data (legacy_expected_node f N)) \<longleftrightarrow>
    legacy_node_functional (legacy_expected_node f N)"
    using fin loc by simp
  have payloads: "single_valued (legacy_node_payloads (legacy_expected_node f N)) \<longleftrightarrow>
    basis_compatible f (legacy_payload_basis (Legacy_Node_Data N))"
    by (simp only: legacy_node_payload_transport[where U=U] pushed_functional_single_valued)
  show ?thesis
    using formation payloads node_functionality_decomposes[where N="legacy_expected_node f N"]
    by blast
qed

lemma node_compatibility_lifts:
  "basis_compatible (map_sum f f) (node_migration_basis N) \<longleftrightarrow>
    basis_compatible f (legacy_payload_basis (Legacy_Node_Data N))"
  by (force simp: basis_compatible_def node_migration_basis_def)

lemma legacy_payload_renaming:
  assumes fin: "finite U" and formed: "legacy_data_formed U D" and injective: "inj_on f U"
  shows "legacy_payload_basis (legacy_push_data f D) = push_basis U f (legacy_payload_basis D)"
proof (cases D)
  case Legacy_No_Data
  then show ?thesis by simp
next
  case (Legacy_Functional_Data F)
  have old_push: "legacy_push_data f (Legacy_Functional_Data F) =
      Legacy_Functional_Data ((\<lambda>(a,v). (f a,v)) ` F)"
    by (auto intro: rev_image_eqI)
  show ?thesis using Legacy_Functional_Data
    by (simp only: old_push legacy_functional_gluing_commutes)
next
  case (Legacy_Bag_Data B)
  have bf: "legacy_data_formed U (Legacy_Bag_Data B)" using formed Legacy_Bag_Data by simp
  have old_push: "legacy_push_data f (Legacy_Bag_Data B) = Legacy_Bag_Data ((\<lambda>(a,v,n). (f a,v,n)) ` B)"
    by (auto intro: rev_image_eqI)
  show ?thesis using Legacy_Bag_Data
    by (simp only: old_push legacy_bag_renaming[OF fin bf injective, symmetric]
      legacy_bag_gluing_commutes)
next
  case (Legacy_Node_Data N)
  have old_push: "legacy_push_data f (Legacy_Node_Data N) = Legacy_Node_Data (legacy_expected_node f N)"
    by (auto simp: legacy_expected_node_def intro: rev_image_eqI)
  have counts: "bag_count (legacy_payload_basis (legacy_push_data f (Legacy_Node_Data N))) =
      bag_count (push_basis U f (legacy_payload_basis (Legacy_Node_Data N)))"
    by (simp add: push_basis_def pushed_count_def fun_eq_iff)
  have payloads: "functional_bindings (legacy_payload_basis (legacy_push_data f (Legacy_Node_Data N))) =
      functional_bindings (push_basis U f (legacy_payload_basis (Legacy_Node_Data N)))"
    by (simp only: old_push legacy_node_payloads_basis[symmetric]
      legacy_node_payload_transport[where U=U])
  show ?thesis using Legacy_Node_Data counts payloads by (simp only: basis_identity)
qed

text \<open>
  The two injections describe a migration correspondence: inherited occurrences
  and fresh ownership-link occurrences. No stored atom kind is introduced.
  A fresh link prevents an added ownership tuple from coinciding with an
  original incidence and thereby destroying source recovery.
  The payload remains attached to its one addressable atom. An omitted owner
  therefore crosses through incidence, not through a multi-atom data item.
\<close>

end
