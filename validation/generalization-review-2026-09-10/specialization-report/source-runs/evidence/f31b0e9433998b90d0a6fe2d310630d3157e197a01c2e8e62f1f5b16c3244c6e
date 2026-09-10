theory RRA_Syntax_Composition
  imports RRA_Scope_Construction
begin

section \<open>Attaching finite structural syntax to an existing artifact\<close>

definition attach_structure ::
  "exact_artifact \<Rightarrow> local_address rra_structure \<Rightarrow> exact_artifact" where
  "attach_structure R H =
    \<lparr>object_structure =
      \<lparr>rra_carrier = rra_carrier (object_structure R) \<union> rra_carrier H,
       rra_incidence = rra_incidence (object_structure R) \<union> rra_incidence H\<rparr>,
     object_data = object_data R\<rparr>"

lemma attach_structure_formed:
  assumes rf: "exact_formed R" and hf: "rra_formed H"
    and addresses: "\<forall>a\<in>rra_carrier H. octets_formed a"
  shows "exact_formed (attach_structure R H)"
proof -
  have sf: "rra_formed (object_structure R)"
    and df: "basis_formed (rra_carrier (object_structure R)) (object_data R)"
    using rf by (auto simp: exact_formed_def object_formed_def)
  have data: "basis_formed (rra_carrier (object_structure R) \<union> rra_carrier H) (object_data R)"
    by (rule basis_formed_mono[OF df]) blast
  show ?thesis using rf sf hf addresses data
    by (auto simp: exact_formed_def object_formed_def attach_structure_def rra_formed_def)
qed

lemma attach_structure_head:
  "headed_incidence (object_structure (attach_structure R H)) a =
    headed_incidence (object_structure R) a \<union> headed_incidence H a"
  by (auto simp: attach_structure_def headed_incidence_def)

lemma attach_structure_reads:
  assumes "\<forall>a\<in>rra_carrier (object_structure R). headed_incidence H a = {}"
  shows "object_reads_agree R (attach_structure R H) (rra_carrier (object_structure R))"
  using assms by (auto simp: object_reads_agree_def attach_structure_head attach_structure_def headed_incidence_def)

lemma attached_empty_syntax_reads:
  assumes inside: "I \<subseteq> rra_carrier (object_structure S)"
    and empty: "object_data S = empty_basis"
    and heads: "\<forall>a\<in>I. headed_incidence (object_structure R) a = {}"
    and data: "restrict_basis I (object_data R) = empty_basis"
  shows "object_reads_agree S (attach_structure R (object_structure S)) I"
  using assms by (auto simp: object_reads_agree_def attach_structure_head attach_structure_def headed_incidence_def)

lemma attached_fresh_syntax_reads:
  assumes rf: "exact_formed R" and inside: "I \<subseteq> rra_carrier (object_structure S)"
    and empty: "object_data S = empty_basis"
    and fresh: "I \<inter> rra_carrier (object_structure R) = {}"
  shows "object_reads_agree S (attach_structure R (object_structure S)) I"
proof -
  have oformed: "object_formed R" and df: "basis_formed (rra_carrier (object_structure R)) (object_data R)"
    using rf by (auto simp: exact_formed_def object_formed_def)
  have heads: "\<forall>a\<in>I. headed_incidence (object_structure R) a = {}"
    using fresh formed_head_outside[OF oformed] by blast
  have data: "restrict_basis I (object_data R) = empty_basis"
    by (rule empty_restriction_outside[OF df fresh])
  show ?thesis by (rule attached_empty_syntax_reads[OF inside empty heads data])
qed

definition family_ports :: "nat \<Rightarrow> local_address list" where
  "family_ports n = map (\<lambda>i. [1,2] @ unary_address i) [0..<n]"

lemma family_ports_length [simp]: "length (family_ports n) = n"
  by (simp add: family_ports_def)

lemma family_ports_distinct [simp]: "distinct (family_ports n)"
  by (simp add: family_ports_def distinct_map inj_on_def)

lemma family_ports_shape:
  assumes "a \<in> set (family_ports n)"
  shows "\<exists>i<n. a=[1,2] @ unary_address i"
  using assms by (auto simp: family_ports_def)

lemma family_ports_formed:
  "\<forall>a\<in>set (family_ports n). octets_formed a"
  using unary_address_formed by (auto simp: family_ports_def octets_formed_def)

section \<open>Records of arbitrary finite length\<close>

definition record_wrapper ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address list \<Rightarrow>
    local_address list \<Rightarrow> exact_artifact" where
  "record_wrapper R r ps xs = attach_structure R (record_structure r ps xs)"

lemma record_wrapper_formed:
  assumes rf: "exact_formed R" and roots: "set xs \<subseteq> rra_carrier (object_structure R)"
    and addresses: "\<forall>a\<in>insert r (set ps). octets_formed a"
  shows "exact_formed (record_wrapper R r ps xs)"
proof -
  have hf: "rra_formed (record_structure r ps xs)"
    using record_object_formed[of r ps xs]
    by (simp add: object_formed_def record_object_def)
  have formed_addresses: "\<forall>a\<in>rra_carrier (record_structure r ps xs). octets_formed a"
    using rf roots addresses by (auto simp: record_structure_def exact_formed_def)
  show ?thesis unfolding record_wrapper_def
    by (rule attach_structure_formed[OF rf hf formed_addresses])
qed

lemma record_wrapper_reads:
  assumes fresh: "insert r (set ps) \<inter> rra_carrier (object_structure R) = {}"
  shows "object_reads_agree R (record_wrapper R r ps xs) (rra_carrier (object_structure R))"
proof -
  have heads: "\<forall>a\<in>rra_carrier (object_structure R).
    headed_incidence (record_structure r ps xs) a = {}"
    using fresh by (auto simp: record_structure_def headed_incidence_def dest: set_zip_leftD)
  show ?thesis unfolding record_wrapper_def by (rule attach_structure_reads[OF heads])
qed

lemma record_wrapper_recovers:
  assumes rf: "exact_formed R" and tf: "exact_formed (record_wrapper R r ps xs)"
    and len: "length ps = length xs" and separate: "distinct (r#ps)"
    and fresh: "insert r (set ps) \<inter> rra_carrier (object_structure R) = {}"
  shows "record_at (record_wrapper R r ps xs) r ps xs"
proof -
  let ?S = "record_object r ps xs :: exact_artifact"
  have raw: "record_at ?S r ps xs"
    by (rule record_object_recovers[OF len]) (use separate in auto)
  have reads: "object_reads_agree ?S (attach_structure R (object_structure ?S)) (insert r (set ps))"
    by (rule attached_fresh_syntax_reads[OF rf _ _ fresh])
       (auto simp: record_object_def record_structure_def)
  have target: "object_formed (record_wrapper R r ps xs)" using tf by (simp add: exact_formed_def)
  have agreement: "object_reads_agree ?S (record_wrapper R r ps xs) (insert r (set ps))"
    using reads by (simp add: record_wrapper_def record_object_def)
  show ?thesis by (rule record_at_read_transport[OF raw target agreement]) simp
qed

theorem record_wrapper_total:
  assumes rf: "exact_formed R" and roots: "set xs \<subseteq> rra_carrier (object_structure R)"
  shows "\<exists>r ps. exact_formed (record_wrapper R r ps xs) \<and>
    record_at (record_wrapper R r ps xs) r ps xs \<and>
    distinct (r#ps) \<and> insert r (set ps) \<inter> rra_carrier (object_structure R) = {} \<and>
    object_reads_agree R (record_wrapper R r ps xs) (rra_carrier (object_structure R)) \<and>
    rra_carrier (object_structure (record_wrapper R r ps xs)) =
      rra_carrier (object_structure R) \<union> insert r (set ps)"
proof -
  let ?U = "rra_carrier (object_structure R)"
  let ?r = "fresh_address ?U"
  let ?ps = "fresh_addresses (insert ?r ?U) (length xs)"
  have fin: "finite ?U" using rf by (simp add: exact_formed_def object_formed_def rra_formed_def)
  have r_fresh: "?r \<notin> ?U" by (rule fresh_address_not_in[OF fin])
  have ps_fresh: "distinct ?ps \<and> set ?ps \<inter> insert ?r ?U = {}"
    by (rule fresh_addresses_disjoint) (use fin in simp)
  have separate: "distinct (?r#?ps)" and fresh: "insert ?r (set ?ps) \<inter> ?U = {}"
    using r_fresh ps_fresh by auto
  have addresses: "\<forall>a\<in>insert ?r (set ?ps). octets_formed a"
    using fresh_addresses_formed by auto
  have formed: "exact_formed (record_wrapper R ?r ?ps xs)"
    by (rule record_wrapper_formed[OF rf roots addresses])
  have rec: "record_at (record_wrapper R ?r ?ps xs) ?r ?ps xs"
    by (rule record_wrapper_recovers[OF rf formed _ separate fresh]) simp
  have reads: "object_reads_agree R (record_wrapper R ?r ?ps xs) ?U"
    by (rule record_wrapper_reads[OF fresh])
  have carrier: "rra_carrier (object_structure (record_wrapper R ?r ?ps xs)) = ?U \<union> insert ?r (set ?ps)"
    using roots by (auto simp: record_wrapper_def attach_structure_def record_structure_def)
  show ?thesis by (rule exI[of _ ?r], rule exI[of _ ?ps])
    (use formed rec separate fresh reads carrier in blast)
qed

section \<open>Families can share silent sockets with an explicit boundary\<close>

definition family_wrapper ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> (local_address \<times> local_address) set \<Rightarrow> exact_artifact" where
  "family_wrapper R r M = attach_structure R (object_structure (family_object r M :: exact_artifact))"

lemma family_wrapper_formed:
  assumes rf: "exact_formed R" and fin: "finite M"
    and addresses: "\<forall>a\<in>insert r (rel_dom M \<union> rel_ran M). octets_formed a"
  shows "exact_formed (family_wrapper R r M)"
proof -
  have hf: "rra_formed (object_structure (family_object r M))"
    using family_object_formed[OF fin, of r] by (simp add: object_formed_def family_object_def)
  show ?thesis unfolding family_wrapper_def
    by (rule attach_structure_formed[OF rf hf]) (use addresses in \<open>simp add: family_object_def\<close>)
qed

lemma family_wrapper_reads:
  assumes fresh: "r \<notin> rra_carrier (object_structure R)"
  shows "object_reads_agree R (family_wrapper R r M) (rra_carrier (object_structure R))"
  unfolding family_wrapper_def
  by (rule attach_structure_reads)
     (use fresh in \<open>auto simp: family_object_def headed_incidence_def\<close>)

lemma family_wrapper_recovers:
  assumes tf: "exact_formed (family_wrapper R r M)"
    and fin: "finite M" and sv: "single_valued M" and separate: "r \<notin> rel_dom M"
    and heads: "\<forall>a\<in>insert r (rel_dom M). headed_incidence (object_structure R) a = {}"
    and data: "restrict_basis (insert r (rel_dom M)) (object_data R) = empty_basis"
  shows "family_at (family_wrapper R r M) r M"
proof -
  have root: "headed_incidence (object_structure (family_wrapper R r M)) r = M"
    using heads family_object_head[of r M]
    by (simp add: family_wrapper_def attach_structure_head)
  have ports: "\<forall>p\<in>rel_dom M. headed_incidence (object_structure (family_wrapper R r M)) p = {}"
    using heads separate
    by (auto simp: family_wrapper_def attach_structure_def family_object_def headed_incidence_def)
  show ?thesis using tf root sv separate ports data
    by (simp add: family_at_def exact_formed_def family_wrapper_def attach_structure_def family_object_def)
qed

lemma family_wrapper_fresh_recovers:
  assumes rf: "exact_formed R" and tf: "exact_formed (family_wrapper R r M)"
    and fin: "finite M" and sv: "single_valued M" and separate: "r \<notin> rel_dom M"
    and fresh: "insert r (rel_dom M) \<inter> rra_carrier (object_structure R) = {}"
  shows "family_at (family_wrapper R r M) r M"
proof -
  have oformed: "object_formed R" and df: "basis_formed (rra_carrier (object_structure R)) (object_data R)"
    using rf by (auto simp: exact_formed_def object_formed_def)
  have heads: "\<forall>a\<in>insert r (rel_dom M). headed_incidence (object_structure R) a = {}"
    using fresh formed_head_outside[OF oformed] by blast
  have data: "restrict_basis (insert r (rel_dom M)) (object_data R) = empty_basis"
    by (rule empty_restriction_outside[OF df fresh])
  show ?thesis by (rule family_wrapper_recovers[OF tf fin sv separate heads data])
qed

text \<open>
  Attaching a record adds only its root, actual ports, and structural incidences.
  Its length is unrestricted and endpoints may repeat. Every old headed read
  and all old data are preserved when the record headers are fresh. Families
  need only a fresh root to preserve old reads; their sockets may be existing
  silent occurrences, as in a binder declaration. These are construction
  functions, while the existing structural readers determine their roles.
\<close>

end
