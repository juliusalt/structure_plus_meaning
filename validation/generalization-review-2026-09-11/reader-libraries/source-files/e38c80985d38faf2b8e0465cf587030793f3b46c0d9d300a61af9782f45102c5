theory RRA_Bound_Syntax_Construction
  imports RRA_Syntax_Construction
begin

section \<open>Copying syntax while fixing an explicit construction boundary\<close>

definition binder_addresses :: "local_address set" where
  "binder_addresses = range (Cons 6)"

definition syntax_prefix :: "nat \<Rightarrow> local_address \<Rightarrow> local_address" where
  "syntax_prefix n a = (if a \<in> binder_addresses then a else n#a)"

lemma binder_addresses_iff [simp]:
  "a \<in> binder_addresses \<longleftrightarrow> (\<exists>xs. a = 6#xs)"
  by (auto simp: binder_addresses_def)

lemma syntax_prefix_root [simp]: "syntax_prefix n [] = [n]"
  by (simp add: syntax_prefix_def)

lemma syntax_prefix_binder [simp]: "syntax_prefix n (6#a) = 6#a"
  by (simp add: syntax_prefix_def)

lemma syntax_prefix_injective:
  assumes "n \<noteq> 6"
  shows "inj (syntax_prefix n)"
  using assms by (auto simp: syntax_prefix_def inj_def split: if_splits)

lemma syntax_prefix_overlap:
  assumes "m \<noteq> 6" "n \<noteq> 6" "m \<noteq> n"
  shows "syntax_prefix m a = syntax_prefix n b \<longleftrightarrow> a = b \<and> a \<in> binder_addresses"
  using assms by (auto simp: syntax_prefix_def split: if_splits)

lemma syntax_prefix_boundary:
  assumes "n \<noteq> 6"
  shows "syntax_prefix n a \<in> binder_addresses \<longleftrightarrow> a \<in> binder_addresses"
  using assms by (auto simp: syntax_prefix_def split: if_splits)

lemma syntax_prefix_addressing:
  assumes "exact_formed R" "n < 256" "n \<noteq> 6"
  shows "finite_addressing (rra_carrier (object_structure R)) (syntax_prefix n)"
proof -
  have injective: "inj_on (syntax_prefix n) (rra_carrier (object_structure R))"
    using syntax_prefix_injective[OF assms(3)] by (auto simp: inj_on_def)
  have source: "\<forall>a\<in>rra_carrier (object_structure R). octets_formed a"
    using assms(1) by (simp add: exact_formed_def)
  have target: "\<forall>a\<in>rra_carrier (object_structure R). octets_formed (syntax_prefix n a)"
    using source assms(2) by (auto simp: syntax_prefix_def octets_formed_def)
  show ?thesis using injective target by (simp add: finite_addressing_def)
qed

lemma syntax_prefix_ne_empty [simp]:
  "syntax_prefix n a \<noteq> []"
  by (auto simp: syntax_prefix_def)

lemma syntax_prefix_singleton:
  assumes "m \<noteq> 6"
  shows "syntax_prefix n a = [m] \<longleftrightarrow> n = m \<and> a = []"
  using assms by (auto simp: syntax_prefix_def split: if_splits)

lemma syntax_prefix_singleton_reverse:
  assumes "m \<noteq> 6"
  shows "[m] = syntax_prefix n a \<longleftrightarrow> n = m \<and> a = []"
  using syntax_prefix_singleton[OF assms, of n a] by auto

lemma syntax_prefix_empty_reverse [simp]:
  "[] \<noteq> syntax_prefix n a"
  by (rule not_sym[OF syntax_prefix_ne_empty])

lemma syntax_prefix_eq_iff:
  assumes "n \<noteq> 6"
  shows "syntax_prefix n a = syntax_prefix n b \<longleftrightarrow> a = b"
  using syntax_prefix_injective[OF assms] by (auto simp: inj_def)

lemma syntax_prefix_image_outside:
  assumes "A \<inter> binder_addresses = {}"
  shows "syntax_prefix n ` A = Cons n ` A"
  by (rule image_cong[OF refl]) (use assms in \<open>auto simp: syntax_prefix_def\<close>)

lemma syntax_prefix_image_binders:
  assumes "A \<subseteq> binder_addresses"
  shows "syntax_prefix n ` A = A"
proof -
  have "syntax_prefix n ` A = id ` A"
    by (rule image_cong[OF refl]) (use assms in \<open>auto simp: syntax_prefix_def\<close>)
  then show ?thesis by simp
qed

definition binder_silent :: "exact_artifact \<Rightarrow> bool" where
  "binder_silent R \<longleftrightarrow>
    (\<forall>a\<in>binder_addresses. headed_incidence (object_structure R) a = {}) \<and>
    restrict_basis binder_addresses (object_data R) = empty_basis"

lemma binder_silent_incidence:
  assumes "binder_silent R" "(a,p,x) \<in> rra_incidence (object_structure R)"
  shows "a \<notin> binder_addresses"
  using assms by (auto simp: binder_silent_def headed_incidence_def)

lemma binder_silent_data:
  assumes "binder_silent R" "(a,v) \<in> functional_bindings (object_data R)"
  shows "a \<notin> binder_addresses"
proof
  assume member: "a \<in> binder_addresses"
  have "(a,v) \<in> functional_bindings (restrict_basis binder_addresses (object_data R))"
    using assms(2) member by simp
  moreover have "restrict_basis binder_addresses (object_data R) = empty_basis"
    using assms(1) by (simp add: binder_silent_def)
  ultimately show False by (simp add: empty_basis_def)
qed

definition bound_pair_syntax :: "exact_artifact \<Rightarrow> exact_artifact \<Rightarrow> exact_artifact" where
  "bound_pair_syntax R S =
    \<lparr>object_structure =
      \<lparr>rra_carrier = {[],[0],[1]} \<union>
          syntax_prefix 2 ` rra_carrier (object_structure R) \<union>
          syntax_prefix 3 ` rra_carrier (object_structure S),
       rra_incidence = {([],[0],[2]),([],[1],[3]),([0],[0],[1])} \<union>
          rra_incidence (push_structure (syntax_prefix 2) (object_structure R)) \<union>
          rra_incidence (push_structure (syntax_prefix 3) (object_structure S))\<rparr>,
     object_data = \<lparr>bag_count = (\<lambda>_. 0),
       functional_bindings =
         (\<lambda>(a,v). (syntax_prefix 2 a,v)) ` functional_bindings (object_data R) \<union>
         (\<lambda>(a,v). (syntax_prefix 3 a,v)) ` functional_bindings (object_data S)\<rparr>\<rparr>"

lemma bound_pair_root [simp]:
  "[] \<in> rra_carrier (object_structure (bound_pair_syntax R S))"
  by (simp add: bound_pair_syntax_def)

lemma bound_pair_no_counts [simp]:
  "bag_count (object_data (bound_pair_syntax R S)) = (\<lambda>_. 0)"
  by (simp add: bound_pair_syntax_def)

lemma bound_pair_bindings_functional:
  assumes rf: "object_formed R" and sf: "object_formed S"
    and silent: "binder_silent R" "binder_silent S"
  shows "single_valued (functional_bindings (object_data (bound_pair_syntax R S)))"
proof -
  let ?A = "(\<lambda>(a,v). (syntax_prefix 2 a,v)) ` functional_bindings (object_data R)"
  let ?B = "(\<lambda>(a,v). (syntax_prefix 3 a,v)) ` functional_bindings (object_data S)"
  have rsv: "single_valued (functional_bindings (object_data R))"
    and ssv: "single_valued (functional_bindings (object_data S))"
    using rf sf by (auto simp: object_formed_def basis_formed_def)
  have first: "single_valued ?A"
    using single_valued_pair_image[OF rsv, where f="syntax_prefix 2" and g=id]
      syntax_prefix_injective[of 2] by (auto simp: inj_on_def)
  have second: "single_valued ?B"
    using single_valued_pair_image[OF ssv, where f="syntax_prefix 3" and g=id]
      syntax_prefix_injective[of 3] by (auto simp: inj_on_def)
  have apart: "\<And>a v w. (a,v) \<in> ?A \<Longrightarrow> (a,w) \<in> ?B \<Longrightarrow> False"
  proof -
    fix a v w assume first: "(a,v) \<in> ?A" and second: "(a,w) \<in> ?B"
    obtain x where source: "(x,v) \<in> functional_bindings (object_data R)" "a = syntax_prefix 2 x"
      using first by auto
    obtain y where target: "(y,w) \<in> functional_bindings (object_data S)" "a = syntax_prefix 3 y"
      using second by auto
    have inside: "x \<in> binder_addresses" using source(2) target(2) syntax_prefix_overlap[of 2 3 x y] by auto
    show False using inside binder_silent_data[OF silent(1) source(1)] by blast
  qed
  have compatible: "\<forall>x y z. (x,y) \<in> ?A \<longrightarrow> (x,z) \<in> ?B \<longrightarrow> y = z"
    using apart by blast
  have union: "single_valued (?A \<union> ?B)"
    using single_valued_union_iff[OF first second] compatible by blast
  show ?thesis using union by (simp add: bound_pair_syntax_def)
qed

lemma bound_pair_syntax_formed:
  assumes rf: "exact_formed R" and sf: "exact_formed S"
    and roots: "[] \<in> rra_carrier (object_structure R)" "[] \<in> rra_carrier (object_structure S)"
    and silent: "binder_silent R" "binder_silent S"
  shows "exact_formed (bound_pair_syntax R S)"
proof -
  have objects: "object_formed R" "object_formed S" using rf sf by (auto simp: exact_formed_def)
  have functional: "single_valued (functional_bindings (object_data (bound_pair_syntax R S)))"
    by (rule bound_pair_bindings_functional[OF objects silent])
  have endpoints: "[2] \<in> syntax_prefix 2 ` rra_carrier (object_structure R)"
    "[3] \<in> syntax_prefix 3 ` rra_carrier (object_structure S)"
    using roots by (auto intro: rev_image_eqI)
  have formed: "object_formed (bound_pair_syntax R S)"
    using objects endpoints functional
    by (auto simp: object_formed_def rra_formed_def basis_formed_def bound_pair_syntax_def
        push_structure_def bag_support_def)
  have left_addressing: "finite_addressing (rra_carrier (object_structure R)) (syntax_prefix 2)"
    by (rule syntax_prefix_addressing[OF rf]) simp_all
  have right_addressing: "finite_addressing (rra_carrier (object_structure S)) (syntax_prefix 3)"
    by (rule syntax_prefix_addressing[OF sf]) simp_all
  have payloads: "\<And>a v. (a,v) \<in> functional_bindings (object_data R) \<union>
    functional_bindings (object_data S) \<Longrightarrow> octets_formed v"
  proof -
    fix a v assume member: "(a,v) \<in> functional_bindings (object_data R) \<union>
      functional_bindings (object_data S)"
    have "v \<in> basis_values (object_data R) \<union> basis_values (object_data S)"
      using member by (force simp: basis_values_def)
    then show "octets_formed v" using rf sf by (auto simp: exact_formed_def)
  qed
  show ?thesis using formed left_addressing right_addressing payloads
    by (auto simp: exact_formed_def bound_pair_syntax_def basis_values_def
        bag_support_def finite_addressing_def octets_formed_def; blast)
qed

lemma other_prefix_head_empty:
  assumes silent: "binder_silent R" and separate: "m \<noteq> 6" "n \<noteq> 6" "m \<noteq> n"
  shows "headed_incidence (push_structure (syntax_prefix n) (object_structure R)) (syntax_prefix m a) = {}"
proof (rule equals0I)
  fix entry assume member:
    "entry \<in> headed_incidence (push_structure (syntax_prefix n) (object_structure R)) (syntax_prefix m a)"
  obtain b p x where source: "(b,p,x) \<in> rra_incidence (object_structure R)"
    and eq: "syntax_prefix m a = syntax_prefix n b"
    using member by (auto simp: headed_incidence_def push_structure_def)
  have inside: "b \<in> binder_addresses" using syntax_prefix_overlap[OF separate, of a b] eq by auto
  show False using inside binder_silent_incidence[OF silent source] by blast
qed

lemma other_prefix_data_empty:
  assumes silent: "binder_silent R" and separate: "m \<noteq> 6" "n \<noteq> 6" "m \<noteq> n"
  shows "(syntax_prefix m a,v) \<notin>
    (\<lambda>(b,w). (syntax_prefix n b,w)) ` functional_bindings (object_data R)"
proof
  assume member: "(syntax_prefix m a,v) \<in>
    (\<lambda>(b,w). (syntax_prefix n b,w)) ` functional_bindings (object_data R)"
  obtain b where source: "(b,v) \<in> functional_bindings (object_data R)"
    and eq: "syntax_prefix m a = syntax_prefix n b" using member by auto
  have inside: "b \<in> binder_addresses" using syntax_prefix_overlap[OF separate, of a b] eq by auto
  show False using inside binder_silent_data[OF silent source] by blast
qed

lemma data_prefix_separate:
  assumes silent: "binder_silent R" and member: "(b,v) \<in> functional_bindings (object_data R)"
    and separate: "n \<noteq> 6" "m \<noteq> 6" "n \<noteq> m"
  shows "syntax_prefix n b \<noteq> syntax_prefix m a"
  using binder_silent_data[OF silent member] syntax_prefix_overlap[OF separate, of b a] by auto

lemma bound_pair_head:
  "headed_incidence (object_structure (bound_pair_syntax R S)) a =
    {(p,x). (a,p,x) \<in> {([],[0],[2]),([],[1],[3]),([0],[0],[1])}} \<union>
    headed_incidence (push_structure (syntax_prefix 2) (object_structure R)) a \<union>
    headed_incidence (push_structure (syntax_prefix 3) (object_structure S)) a"
  by (auto simp: bound_pair_syntax_def headed_incidence_def)

lemma bound_pair_head_left:
  assumes "binder_silent S"
  shows "headed_incidence (object_structure (bound_pair_syntax R S)) (syntax_prefix 2 a) =
    headed_incidence (push_structure (syntax_prefix 2) (object_structure R)) (syntax_prefix 2 a)"
proof -
  have other: "headed_incidence (push_structure (syntax_prefix 3) (object_structure S)) (syntax_prefix 2 a) = {}"
    by (rule other_prefix_head_empty[OF assms]) simp_all
  show ?thesis by (simp add: bound_pair_head other syntax_prefix_singleton)
qed

lemma bound_pair_head_right:
  assumes "binder_silent R"
  shows "headed_incidence (object_structure (bound_pair_syntax R S)) (syntax_prefix 3 a) =
    headed_incidence (push_structure (syntax_prefix 3) (object_structure S)) (syntax_prefix 3 a)"
proof -
  have other: "headed_incidence (push_structure (syntax_prefix 2) (object_structure R)) (syntax_prefix 3 a) = {}"
    by (rule other_prefix_head_empty[OF assms]) simp_all
  show ?thesis by (simp add: bound_pair_head other syntax_prefix_singleton)
qed

lemma bound_pair_reads_left:
  assumes counts: "bag_count (object_data R) = (\<lambda>_. 0)" and silent: "binder_silent S"
  shows "object_reads_agree (push_object (syntax_prefix 2) R) (bound_pair_syntax R S)
    (syntax_prefix 2 ` rra_carrier (object_structure R))"
proof -
  let ?I = "syntax_prefix 2 ` rra_carrier (object_structure R)"
  have heads: "\<forall>a\<in>?I. headed_incidence (object_structure (push_object (syntax_prefix 2) R)) a =
    headed_incidence (object_structure (bound_pair_syntax R S)) a"
    using bound_pair_head_left[OF silent] by (auto simp: push_object_def)
  have absent: "\<And>a v. (syntax_prefix 2 a,v) \<notin>
    (\<lambda>(b,w). (syntax_prefix 3 b,w)) ` functional_bindings (object_data S)"
    by (rule other_prefix_data_empty[OF silent]) simp_all
  have different: "\<And>a b v. (b,v) \<in> functional_bindings (object_data S) \<Longrightarrow>
    syntax_prefix 3 b \<noteq> syntax_prefix 2 a"
    by (rule data_prefix_separate[OF silent]) simp_all
  have data: "restrict_basis ?I (object_data (push_object (syntax_prefix 2) R)) =
    restrict_basis ?I (object_data (bound_pair_syntax R S))"
    using absent
    by (auto simp: restrict_basis_def basis_identity push_object_def push_basis_def
        pushed_count_def bound_pair_syntax_def counts fun_eq_iff; meson different)
  show ?thesis using heads data by (auto simp: object_reads_agree_def push_object_def bound_pair_syntax_def)
qed

lemma bound_pair_reads_right:
  assumes counts: "bag_count (object_data S) = (\<lambda>_. 0)" and silent: "binder_silent R"
  shows "object_reads_agree (push_object (syntax_prefix 3) S) (bound_pair_syntax R S)
    (syntax_prefix 3 ` rra_carrier (object_structure S))"
proof -
  let ?I = "syntax_prefix 3 ` rra_carrier (object_structure S)"
  have heads: "\<forall>a\<in>?I. headed_incidence (object_structure (push_object (syntax_prefix 3) S)) a =
    headed_incidence (object_structure (bound_pair_syntax R S)) a"
    using bound_pair_head_right[OF silent] by (auto simp: push_object_def)
  have absent: "\<And>a v. (syntax_prefix 3 a,v) \<notin>
    (\<lambda>(b,w). (syntax_prefix 2 b,w)) ` functional_bindings (object_data R)"
    by (rule other_prefix_data_empty[OF silent]) simp_all
  have different: "\<And>a b v. (b,v) \<in> functional_bindings (object_data R) \<Longrightarrow>
    syntax_prefix 2 b \<noteq> syntax_prefix 3 a"
    by (rule data_prefix_separate[OF silent]) simp_all
  have data: "restrict_basis ?I (object_data (push_object (syntax_prefix 3) S)) =
    restrict_basis ?I (object_data (bound_pair_syntax R S))"
    using absent
    by (auto simp: restrict_basis_def basis_identity push_object_def push_basis_def
        pushed_count_def bound_pair_syntax_def counts fun_eq_iff; meson different)
  show ?thesis using heads data by (auto simp: object_reads_agree_def push_object_def bound_pair_syntax_def)
qed

lemma bound_pair_silent:
  assumes silent: "binder_silent R" "binder_silent S"
  shows "binder_silent (bound_pair_syntax R S)"
proof -
  have headR: "\<And>a. a \<in> binder_addresses \<Longrightarrow>
    headed_incidence (push_structure (syntax_prefix 2) (object_structure R)) a = {}"
  proof -
    fix a assume member: "a \<in> binder_addresses"
    have "headed_incidence (push_structure (syntax_prefix 2) (object_structure R)) (syntax_prefix 3 a) = {}"
      by (rule other_prefix_head_empty[OF silent(1)]) simp_all
    then show "headed_incidence (push_structure (syntax_prefix 2) (object_structure R)) a = {}"
      using member by (simp add: syntax_prefix_def)
  qed
  have headS: "\<And>a. a \<in> binder_addresses \<Longrightarrow>
    headed_incidence (push_structure (syntax_prefix 3) (object_structure S)) a = {}"
  proof -
    fix a assume member: "a \<in> binder_addresses"
    have "headed_incidence (push_structure (syntax_prefix 3) (object_structure S)) (syntax_prefix 2 a) = {}"
      by (rule other_prefix_head_empty[OF silent(2)]) simp_all
    then show "headed_incidence (push_structure (syntax_prefix 3) (object_structure S)) a = {}"
      using member by (simp add: syntax_prefix_def)
  qed
  have dataR: "\<And>a v. a \<in> binder_addresses \<Longrightarrow>
    (a,v) \<notin> (\<lambda>(b,w). (syntax_prefix 2 b,w)) ` functional_bindings (object_data R)"
  proof -
    fix a v assume member: "a \<in> binder_addresses"
    have "(syntax_prefix 3 a,v) \<notin>
      (\<lambda>(b,w). (syntax_prefix 2 b,w)) ` functional_bindings (object_data R)"
      by (rule other_prefix_data_empty[OF silent(1)]) simp_all
    then show "(a,v) \<notin> (\<lambda>(b,w). (syntax_prefix 2 b,w)) ` functional_bindings (object_data R)"
      using member by (simp add: syntax_prefix_def)
  qed
  have dataS: "\<And>a v. a \<in> binder_addresses \<Longrightarrow>
    (a,v) \<notin> (\<lambda>(b,w). (syntax_prefix 3 b,w)) ` functional_bindings (object_data S)"
  proof -
    fix a v assume member: "a \<in> binder_addresses"
    have "(syntax_prefix 2 a,v) \<notin>
      (\<lambda>(b,w). (syntax_prefix 3 b,w)) ` functional_bindings (object_data S)"
      by (rule other_prefix_data_empty[OF silent(2)]) simp_all
    then show "(a,v) \<notin> (\<lambda>(b,w). (syntax_prefix 3 b,w)) ` functional_bindings (object_data S)"
      using member by (simp add: syntax_prefix_def)
  qed
  have heads: "\<forall>a\<in>binder_addresses. headed_incidence (object_structure (bound_pair_syntax R S)) a = {}"
    using headR headS by (auto simp: bound_pair_head)
  have data: "restrict_basis binder_addresses (object_data (bound_pair_syntax R S)) = empty_basis"
    by (auto simp: restrict_basis_def bound_pair_syntax_def empty_basis_def basis_identity fun_eq_iff
        syntax_prefix_def dest: binder_silent_data[OF silent(1)] binder_silent_data[OF silent(2)])
  show ?thesis using heads data by (simp add: binder_silent_def)
qed

lemma bound_pair_record:
  assumes formed: "exact_formed (bound_pair_syntax R S)"
  shows "record_at (bound_pair_syntax R S) [] [[0],[1]] [[2],[3]]"
proof -
  let ?T = "object_structure (bound_pair_syntax R S)"
  have last: "record_path ?T [] [1] [[1]] [[3]]"
    by (rule record_path.path_last)
       (auto simp: bound_pair_syntax_def push_structure_def headed_incidence_def field_endpoint_def
         syntax_prefix_singleton syntax_prefix_singleton_reverse)
  have path: "record_path ?T [] [0] [[0],[1]] [[2],[3]]"
    by (rule record_path.path_slot[OF _ _ _ last])
       (auto simp: bound_pair_syntax_def push_structure_def headed_incidence_def field_endpoint_def
         syntax_prefix_singleton syntax_prefix_singleton_reverse)
  show ?thesis using formed path
    by (auto simp: record_at_def raw_record_at_def exact_formed_def bound_pair_syntax_def
        push_structure_def headed_incidence_def restrict_basis_def empty_basis_def
        basis_identity fun_eq_iff syntax_prefix_singleton syntax_prefix_singleton_reverse)
qed

text \<open>
  These byte prefixes are concrete choices for construction witnesses. Readers
  do not test them. Positions in the chosen binder boundary are fixed while
  other positions are copied. Shared binders carry no headed incidence or data,
  so combining their occurrences cannot add a field or attachment at that
  boundary. Incoming variable references remain explicit incidence.
\<close>

end
