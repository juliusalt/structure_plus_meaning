theory Factor_Presentation
  imports Factor_Interfaces
begin

type_synonym 'u definition_site = "'u \<times> local_address"
type_synonym 'u native_schema = "(local_address,local_address,'u definition_site) factor_schema"
type_synonym 'u native_system = "(local_address,local_address,'u definition_site,local_address) schema_system"

section \<open>A pattern with its complete declared scope\<close>

definition scoped_pattern_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address term_pattern \<Rightarrow>
    local_address set \<Rightarrow> local_address set \<Rightarrow> bool" where
  "scoped_pattern_at E u r p I K \<longleftrightarrow> environment_formed E \<and>
    (\<exists>R ps b q V J. artifact_at E u R \<and> record_at R r ps [b,q] \<and>
      binder_scope_at R b V \<and> pattern_quoted_at E u V q p J K \<and>
      V = pattern_variables p \<and>
      insert r (set ps) \<inter> (insert b V \<union> J) = {} \<and> insert b V \<inter> J = {} \<and>
      I = insert r (set ps \<union> insert b V \<union> J) \<and> I \<inter> K = {})"

theorem scoped_pattern_unique:
  assumes first: "scoped_pattern_at E u r p I K" and second: "scoped_pattern_at E u r q J W"
  shows "p = q \<and> I = J \<and> K = W"
proof -
  have ef: "environment_formed E" using first by (simp add: scoped_pattern_at_def)
  obtain R ps b a V A where left:
    "artifact_at E u R" "record_at R r ps [b,a]" "binder_scope_at R b V"
    "pattern_quoted_at E u V a p A K" "I = insert r (set ps \<union> insert b V \<union> A)"
    using first by (auto simp: scoped_pattern_at_def)
  obtain S qs c z B C where right:
    "artifact_at E u S" "record_at S r qs [c,z]" "binder_scope_at S c B"
    "pattern_quoted_at E u B z q C W" "J = insert r (set qs \<union> insert c B \<union> C)"
    using second by (auto simp: scoped_pattern_at_def)
  have art: "S = R" by (rule environment_artifact_unique[OF ef right(1) left(1)])
  have rec: "record_at R r qs [c,z]" using right(2) art by simp
  have fields: "qs = ps \<and> c = b \<and> z = a" using record_at_unique[OF rec left(2)] by auto
  have other_scope: "binder_scope_at R b B" using right(3) art fields by simp
  have scope: "B = V" by (rule binder_scope_unique[OF other_scope left(3)])
  have other_pattern: "pattern_quoted_at E u V a q C W" using right(4) fields scope by simp
  have same: "p = q \<and> A = C \<and> K = W"
    by (rule pattern_quoted_unique[OF left(4) other_pattern])
  show ?thesis using same scope fields left(5) right(5) by simp
qed

lemma scoped_pattern_formed:
  assumes "scoped_pattern_at E u r p I K"
  shows "pattern_formed p \<and> r \<in> I \<and> finite I \<and> finite K \<and> I \<inter> K = {}"
proof -
  obtain R ps b q V J where parts: "binder_scope_at R b V" "pattern_quoted_at E u V q p J K"
    "I = insert r (set ps \<union> insert b V \<union> J)" "I \<inter> K = {}"
    using assms by (auto simp: scoped_pattern_at_def)
  show ?thesis using pattern_quoted_formed[OF parts(2)] pattern_quoted_boundary[OF parts(2)]
    binder_scope_properties(1)[OF parts(1)] parts(3,4) by auto
qed

lemma scoped_pattern_declares_every_variable:
  assumes "scoped_pattern_at E u r p I K"
  shows "\<exists>R ps b q V J. artifact_at E u R \<and> record_at R r ps [b,q] \<and>
    binder_scope_at R b V \<and> pattern_quoted_at E u V q p J K \<and> V = pattern_variables p"
  using assms by (auto simp: scoped_pattern_at_def)

section \<open>Prospective calls recover their dependency locations\<close>

definition prospective_call_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow> local_address \<Rightarrow>
    'u definition_site \<Rightarrow> local_address term_pattern \<Rightarrow> local_address set \<Rightarrow>
    local_address set \<Rightarrow> bool" where
  "prospective_call_at E u V r d p I K \<longleftrightarrow> environment_formed E \<and>
    (\<exists>R ps c a cite C J A. artifact_at E u R \<and> record_at R r ps [c,a] \<and>
      citation_at R c cite C \<and> citation_location E u cite (fst d) (snd d) \<and>
      pattern_quoted_at E u V a p J A \<and>
      insert r (set ps) \<inter> (C \<union> J) = {} \<and> C \<inter> J = {} \<and>
      I = insert r (set ps \<union> C \<union> J) \<and> K = citation_slots cite \<union> A \<and>
      I \<inter> (K \<union> V) = {})"

theorem prospective_call_unique:
  assumes first: "prospective_call_at E u V r d p I K"
    and second: "prospective_call_at E u V r e q J W"
  shows "d = e \<and> p = q \<and> I = J \<and> K = W"
proof -
  have ef: "environment_formed E" using first by (simp add: prospective_call_at_def)
  obtain R ps c a cite C A L where left:
    "artifact_at E u R" "record_at R r ps [c,a]" "citation_at R c cite C"
    "citation_location E u cite (fst d) (snd d)" "pattern_quoted_at E u V a p A L"
    "I = insert r (set ps \<union> C \<union> A)" "K = citation_slots cite \<union> L"
    using first by (auto simp: prospective_call_at_def)
  obtain S qs b z code D B N where right:
    "artifact_at E u S" "record_at S r qs [b,z]" "citation_at S b code D"
    "citation_location E u code (fst e) (snd e)" "pattern_quoted_at E u V z q B N"
    "J = insert r (set qs \<union> D \<union> B)" "W = citation_slots code \<union> N"
    using second by (auto simp: prospective_call_at_def)
  have art: "S = R" by (rule environment_artifact_unique[OF ef right(1) left(1)])
  have rec: "record_at R r qs [b,z]" using right(2) art by simp
  have fields: "qs = ps \<and> b = c \<and> z = a" using record_at_unique[OF rec left(2)] by auto
  have other_cite: "citation_at R c code D" using right(3) art fields by simp
  have citation: "code = cite \<and> D = C" using citation_at_unique[OF other_cite left(3)] by blast
  have other_location: "citation_location E u cite (fst e) (snd e)" using right(4) citation by simp
  have location: "fst d = fst e \<and> snd d = snd e"
    by (rule citation_location_unique[OF ef left(4) other_location])
  have sites: "d = e" using location by (cases d; cases e) simp
  have other_pattern: "pattern_quoted_at E u V a q B N" using right(5) fields by simp
  have pattern: "p = q \<and> A = B \<and> L = N" by (rule pattern_quoted_unique[OF left(5) other_pattern])
  show ?thesis using sites pattern citation fields left(6,7) right(6,7) by simp
qed

lemma prospective_call_formed:
  assumes "prospective_call_at E u V r d p I K"
  shows "pattern_formed p \<and> pattern_variables p \<subseteq> V \<and>
    r \<in> I \<and> finite I \<and> finite K \<and> I \<inter> (K \<union> V) = {}"
proof -
  obtain R ps c a cite C J A where parts:
    "citation_at R c cite C" "pattern_quoted_at E u V a p J A"
    "I = insert r (set ps \<union> C \<union> J)" "K = citation_slots cite \<union> A"
    "I \<inter> (K \<union> V) = {}"
    using assms by (auto simp: prospective_call_at_def)
  have raw: "raw_citation_at R c cite C" using parts(1) by (simp add: citation_at_def)
  have finite_slots: "finite (citation_slots cite)" by (cases cite) simp_all
  show ?thesis using raw_citation_interior(1)[OF raw] pattern_quoted_formed[OF parts(2)]
    pattern_quoted_boundary[OF parts(2)] finite_slots parts(3-5) by auto
qed

lemma prospective_call_has_target:
  assumes "prospective_call_at E u V r d p I K"
  shows "\<exists>R. artifact_at E (fst d) R \<and> anchor_formed (R,snd d)"
proof -
  obtain cite where loc: "citation_location E u cite (fst d) (snd d)"
    using assms by (auto simp: prospective_call_at_def)
  show ?thesis by (rule citation_location_has_artifact[OF loc])
qed

section \<open>Complete families of prospective calls\<close>

definition prospective_family_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow> local_address \<Rightarrow>
    (local_address \<times> ('u definition_site \<times> local_address term_pattern)) set \<Rightarrow> bool" where
  "prospective_family_at E u V r Q \<longleftrightarrow> environment_formed E \<and>
    (\<exists>R M. artifact_at E u R \<and> family_at R r M \<and>
      finite Q \<and> single_valued Q \<and> rel_dom Q = rel_dom M \<and>
      (\<forall>s a. (s,a) \<in> M \<longrightarrow>
        (\<exists>d p I K. (s,d,p) \<in> Q \<and> prospective_call_at E u V a d p I K)))"

lemma prospective_family_origin:
  assumes family: "prospective_family_at E u V r Q" and member: "(s,d,p) \<in> Q"
  shows "\<exists>R M a I K. artifact_at E u R \<and> family_at R r M \<and>
    (s,a) \<in> M \<and> prospective_call_at E u V a d p I K"
proof -
  obtain R M where source: "artifact_at E u R" "family_at R r M" "single_valued Q"
    "rel_dom Q = rel_dom M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>d p I K. (s,d,p) \<in> Q \<and> prospective_call_at E u V a d p I K)"
    using family by (auto simp: prospective_family_at_def)
  have key: "s \<in> rel_dom Q" by (rule rel_domI[OF member])
  have domain: "s \<in> rel_dom M" using source(4) key by simp
  obtain a where field: "(s,a) \<in> M" using domain by (auto simp: rel_dom_def)
  obtain e q I K where recovered: "(s,e,q) \<in> Q" "prospective_call_at E u V a e q I K"
    using source(5) field by blast
  have outputs: "(e,q) = (d,p)" by (rule single_valued_outputs[OF source(3) recovered(1) member])
  have same: "e = d \<and> q = p" using outputs by simp
  show ?thesis using source(1,2) field recovered(2) same by blast
qed

theorem prospective_family_unique:
  assumes first: "prospective_family_at E u V r Q" and second: "prospective_family_at E u V r W"
  shows "Q = W"
proof -
  have compare: "\<And>A B. prospective_family_at E u V r A \<Longrightarrow>
    prospective_family_at E u V r B \<Longrightarrow> A \<subseteq> B"
  proof -
    fix A B assume left: "prospective_family_at E u V r A" and right: "prospective_family_at E u V r B"
    have ef: "environment_formed E" using left by (simp add: prospective_family_at_def)
    obtain S M where target: "artifact_at E u S" "family_at S r M"
      "\<forall>s a. (s,a) \<in> M \<longrightarrow>
        (\<exists>d p I K. (s,d,p) \<in> B \<and> prospective_call_at E u V a d p I K)"
      using right by (auto simp: prospective_family_at_def)
    show "A \<subseteq> B"
    proof
      fix entry assume member: "entry \<in> A"
      obtain s d p where shape: "entry = (s,d,p)" by (cases entry) auto
      obtain R N a I K where source: "artifact_at E u R" "family_at R r N" "(s,a) \<in> N"
        "prospective_call_at E u V a d p I K"
        using prospective_family_origin[OF left] member shape by blast
      have art: "R = S" by (rule environment_artifact_unique[OF ef source(1) target(1)])
      have local: "family_at S r N" using source(2) art by simp
      have graph: "N = M" by (rule family_at_unique[OF local target(2)])
      obtain e q J W where recovered: "(s,e,q) \<in> B" "prospective_call_at E u V a e q J W"
        using target(3) source(3) graph by blast
      have same: "d = e \<and> p = q"
        using prospective_call_unique[OF source(4) recovered(2)] by blast
      show "entry \<in> B" using shape same recovered(1) by simp
    qed
  qed
  show ?thesis using compare[OF first second] compare[OF second first] by blast
qed

lemma prospective_family_formed:
  assumes family: "prospective_family_at E u V r Q"
  shows "finite Q \<and> single_valued Q \<and>
    (\<forall>s d p. (s,d,p) \<in> Q \<longrightarrow> pattern_formed p \<and> pattern_variables p \<subseteq> V)"
proof -
  have base: "finite Q \<and> single_valued Q" using family by (auto simp: prospective_family_at_def)
  have entries: "\<forall>s d p. (s,d,p) \<in> Q \<longrightarrow> pattern_formed p \<and> pattern_variables p \<subseteq> V"
  proof (intro allI impI)
    fix s d p assume member: "(s,d,p) \<in> Q"
    obtain a I K where call: "prospective_call_at E u V a d p I K"
      using prospective_family_origin[OF family member] by blast
    show "pattern_formed p \<and> pattern_variables p \<subseteq> V"
      using prospective_call_formed[OF call] by blast
  qed
  show ?thesis using base entries by blast
qed

section \<open>One family contains calls and complete material checks\<close>

type_synonym 'u native_premise =
  "('u definition_site \<times> local_address term_pattern) + local_address material_pattern"

lemma native_call_material_disjoint:
  assumes call: "prospective_call_at E u V r d p I K" and material: "native_material_at E u V r M J W"
  shows False
proof -
  have ef: "environment_formed E" using call by (simp add: prospective_call_at_def)
  obtain R ports c a where first: "artifact_at E u R" "record_at R r ports [c,a]"
    using call by (auto simp: prospective_call_at_def)
  obtain S sockets roots where second: "artifact_at E u S" "record_at S r sockets roots" "length roots=5"
    using native_material_five_fields[OF material] by blast
  have same: "S=R" by (rule environment_artifact_unique[OF ef second(1) first(1)])
  have rec: "record_at R r sockets roots" using second(2) same by simp
  have fields: "roots=[c,a]" using record_at_unique[OF rec first(2)] by blast
  show False using fields second(3) by simp
qed

inductive native_premise_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow> local_address \<Rightarrow>
    'u native_premise \<Rightarrow> local_address set \<Rightarrow> local_address set \<Rightarrow> bool"
  for E u V r where
  call: "prospective_call_at E u V r d p I K \<Longrightarrow> native_premise_at E u V r (Inl (d,p)) I K"
| material: "native_material_at E u V r M I K \<Longrightarrow> native_premise_at E u V r (Inr M) I K"

lemma native_premise_read_cases [simp]:
  "native_premise_at E u V r (Inl (d,p)) I K \<longleftrightarrow> prospective_call_at E u V r d p I K"
  "native_premise_at E u V r (Inr M) I K \<longleftrightarrow> native_material_at E u V r M I K"
  by (auto elim: native_premise_at.cases intro: native_premise_at.intros)

theorem native_premise_unique:
  assumes first: "native_premise_at E u V r p I K" and second: "native_premise_at E u V r q J W"
  shows "p=q \<and> I=J \<and> K=W"
  using first second
  by (cases rule: native_premise_at.cases[OF first];
      cases rule: native_premise_at.cases[OF second];
      auto dest: prospective_call_unique native_material_unique;
      blast dest: native_call_material_disjoint)

definition native_premise_family_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address set \<Rightarrow> local_address \<Rightarrow>
    (local_address \<times> ('u definition_site \<times> local_address term_pattern)) set \<Rightarrow>
    (local_address \<times> local_address material_pattern) set \<Rightarrow> bool" where
  "native_premise_family_at E u V r Q C \<longleftrightarrow> environment_formed E \<and>
    (\<exists>R M. artifact_at E u R \<and> family_at R r M \<and>
      finite (socket_sum Q C) \<and> single_valued (socket_sum Q C) \<and> rel_dom (socket_sum Q C)=rel_dom M \<and>
      (\<forall>s a. (s,a) \<in> M \<longrightarrow>
        (\<exists>p I K. (s,p) \<in> socket_sum Q C \<and> native_premise_at E u V a p I K)))"

lemma native_premise_family_origin:
  assumes family: "native_premise_family_at E u V r Q C" and member: "(s,p) \<in> socket_sum Q C"
  shows "\<exists>R M a I K. artifact_at E u R \<and> family_at R r M \<and> (s,a) \<in> M \<and>
    native_premise_at E u V a p I K"
proof -
  obtain R M where source: "artifact_at E u R" "family_at R r M"
    "single_valued (socket_sum Q C)" "rel_dom (socket_sum Q C)=rel_dom M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow>
      (\<exists>p. (s,p) \<in> socket_sum Q C \<and> (\<exists>I K. native_premise_at E u V a p I K))"
    using family by (auto simp: native_premise_family_at_def)
  obtain a I K where found: "(s,a) \<in> M" "native_premise_at E u V a p I K"
    using complete_socket_reading_origin[OF source(3-5) member] by blast
  show ?thesis using source(1,2) found by blast
qed

lemma native_premise_family_call_origin:
  assumes family: "native_premise_family_at E u V r Q C" and member: "(s,d,p) \<in> Q"
  shows "\<exists>R M a I K. artifact_at E u R \<and> family_at R r M \<and> (s,a) \<in> M \<and>
    prospective_call_at E u V a d p I K"
proof -
  have present: "(s,Inl (d,p)) \<in> socket_sum Q C" using member by simp
  show ?thesis using native_premise_family_origin[OF family present] by auto
qed

lemma native_premise_family_material_origin:
  assumes family: "native_premise_family_at E u V r Q C" and member: "(s,M) \<in> C"
  shows "\<exists>R F a I K. artifact_at E u R \<and> family_at R r F \<and> (s,a) \<in> F \<and>
    native_material_at E u V a M I K"
proof -
  have present: "(s,Inr M) \<in> socket_sum Q C" using member by simp
  show ?thesis using native_premise_family_origin[OF family present] by auto
qed

theorem native_premise_family_unique:
  assumes first: "native_premise_family_at E u V r Q C" and second: "native_premise_family_at E u V r W D"
  shows "Q=W \<and> C=D"
proof -
  have ef: "environment_formed E" using first by (simp add: native_premise_family_at_def)
  obtain R M where left: "artifact_at E u R" "family_at R r M" "single_valued (socket_sum Q C)"
    "rel_dom (socket_sum Q C)=rel_dom M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow>
      (\<exists>p. (s,p) \<in> socket_sum Q C \<and> (\<exists>I K. native_premise_at E u V a p I K))"
    using first by (auto simp: native_premise_family_at_def)
  obtain S N where right: "artifact_at E u S" "family_at S r N" "single_valued (socket_sum W D)"
    "rel_dom (socket_sum W D)=rel_dom N"
    "\<forall>s a. (s,a) \<in> N \<longrightarrow>
      (\<exists>p. (s,p) \<in> socket_sum W D \<and> (\<exists>I K. native_premise_at E u V a p I K))"
    using second by (auto simp: native_premise_family_at_def)
  have same: "S=R" by (rule environment_artifact_unique[OF ef right(1) left(1)])
  have family: "family_at R r N" using right(2) same by simp
  have graph: "N=M" by (rule family_at_unique[OF family left(2)])
  have domain: "rel_dom (socket_sum W D)=rel_dom M" using right(4) graph by simp
  have reads: "\<forall>s a. (s,a) \<in> M \<longrightarrow>
    (\<exists>p. (s,p) \<in> socket_sum W D \<and> (\<exists>I K. native_premise_at E u V a p I K))"
    using right(5) graph by simp
  have unique: "\<And>a p q. (\<exists>I K. native_premise_at E u V a p I K) \<Longrightarrow>
    (\<exists>J W. native_premise_at E u V a q J W) \<Longrightarrow> p=q"
  proof -
    fix a p q
    assume one: "\<exists>I K. native_premise_at E u V a p I K"
      and two: "\<exists>J W. native_premise_at E u V a q J W"
    obtain I K where first_read: "native_premise_at E u V a p I K" using one by blast
    obtain J L where second_read: "native_premise_at E u V a q J L" using two by blast
    show "p=q" using native_premise_unique[OF first_read second_read] by blast
  qed
  have recovered: "socket_sum Q C = socket_sum W D"
    by (rule complete_socket_reading_unique[OF left(3-5) right(3) domain reads unique])
  show ?thesis using recovered by (simp only: socket_sum_unique)
qed

lemma native_premise_family_formed:
  assumes family: "native_premise_family_at E u V r Q C"
  shows "finite Q \<and> single_valued Q \<and> finite C \<and> single_valued C \<and>
    rel_dom Q \<inter> rel_dom C = {} \<and>
    (\<forall>s d p. (s,d,p) \<in> Q \<longrightarrow> pattern_formed p \<and> pattern_variables p \<subseteq> V) \<and>
    (\<forall>s M. (s,M) \<in> C \<longrightarrow> material_pattern_formed M \<and> material_variables M \<subseteq> V)"
proof -
  have base: "finite Q \<and> single_valued Q \<and> finite C \<and> single_valued C \<and> rel_dom Q \<inter> rel_dom C = {}"
    using family by (auto simp: native_premise_family_at_def socket_sum_single_valued)
  have calls: "\<forall>s d p. (s,d,p) \<in> Q \<longrightarrow> pattern_formed p \<and> pattern_variables p \<subseteq> V"
  proof (intro allI impI)
    fix s d p assume member: "(s,d,p) \<in> Q"
    obtain a I K where call: "prospective_call_at E u V a d p I K"
      using native_premise_family_call_origin[OF family member] by blast
    show "pattern_formed p \<and> pattern_variables p \<subseteq> V" using prospective_call_formed[OF call] by blast
  qed
  have materials: "\<forall>s M. (s,M) \<in> C \<longrightarrow> material_pattern_formed M \<and> material_variables M \<subseteq> V"
  proof (intro allI impI)
    fix s M assume member: "(s,M) \<in> C"
    obtain a I K where material: "native_material_at E u V a M I K"
      using native_premise_family_material_origin[OF family member] by blast
    show "material_pattern_formed M \<and> material_variables M \<subseteq> V" using native_material_formed[OF material] by blast
  qed
  show ?thesis using base calls materials by blast
qed

lemma native_premise_family_calls_only:
  fixes E :: "'u artifact_environment"
    and Q :: "(local_address \<times> ('u definition_site \<times> local_address term_pattern)) set"
  shows "native_premise_family_at E u V r Q {} \<longleftrightarrow> prospective_family_at E u V r Q"
proof -
  have entry: "\<And>s a. (\<exists>p I K. (s,p) \<in> socket_sum Q {} \<and> native_premise_at E u V a p I K)
    \<longleftrightarrow> (\<exists>d p I K. (s,d,p) \<in> Q \<and> prospective_call_at E u V a d p I K)"
  proof -
    fix s a :: local_address
    show "(\<exists>p I K. (s,p) \<in> socket_sum Q {} \<and> native_premise_at E u V a p I K)
      \<longleftrightarrow> (\<exists>d p I K. (s,d,p) \<in> Q \<and> prospective_call_at E u V a d p I K)"
    proof
      assume "\<exists>p I K. (s,p) \<in> socket_sum Q {} \<and> native_premise_at E u V a p I K"
      then obtain entry_value I K where member: "(s,entry_value) \<in> socket_sum Q {}"
        and read: "native_premise_at E u V a entry_value I K" by blast
      obtain q where qmember: "(s,q) \<in> Q" and shape: "entry_value=Inl q"
        using member by (auto simp: socket_sum_def)
      obtain d p where pair: "q=(d,p)" by (cases q)
      have call: "prospective_call_at E u V a d p I K" using read shape pair by simp
      show "\<exists>d p I K. (s,d,p) \<in> Q \<and> prospective_call_at E u V a d p I K"
        using qmember pair call by blast
    next
      assume "\<exists>d p I K. (s,d,p) \<in> Q \<and> prospective_call_at E u V a d p I K"
      then obtain d p I K where member: "(s,d,p) \<in> Q"
        and call: "prospective_call_at E u V a d p I K" by blast
      have present: "(s,Inl (d,p)) \<in> socket_sum Q ({} :: (local_address \<times> local_address material_pattern) set)"
        using member by simp
      have read: "native_premise_at E u V a (Inl (d,p)) I K" by (rule native_premise_at.call[OF call])
      show "\<exists>p I K. (s,p) \<in> socket_sum Q {} \<and> native_premise_at E u V a p I K"
        using present read by blast
    qed
  qed
  show ?thesis
    by (simp only: native_premise_family_at_def prospective_family_at_def socket_sum_finite
        socket_sum_single_valued socket_sum_domain entry;
        simp add: single_valued_def rel_dom_def)
qed

section \<open>Schemas recover their scope, conclusion, and premise family\<close>

definition native_schema_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u native_schema \<Rightarrow> bool" where
  "native_schema_at E u r S \<longleftrightarrow> environment_formed E \<and>
    (\<exists>R ps b c m V I K. artifact_at E u R \<and> record_at R r ps [b,c,m] \<and>
      binder_scope_at R b V \<and> pattern_quoted_at E u V c (schema_conclusion S) I K \<and>
      native_premise_family_at E u V m (schema_premises S) (schema_material_premises S) \<and>
      V = schema_variables S \<and>
      insert r (set ps) \<inter> (insert b V \<union> I \<union> {m}) = {} \<and>
      insert b V \<inter> I = {} \<and> b \<noteq> m \<and> m \<notin> I)"

theorem native_schema_unique:
  assumes first: "native_schema_at E u r S" and second: "native_schema_at E u r T"
  shows "S = T"
proof -
  have ef: "environment_formed E" using first by (simp add: native_schema_at_def)
  obtain R ps b c m V I K where left:
    "artifact_at E u R" "record_at R r ps [b,c,m]" "binder_scope_at R b V"
    "pattern_quoted_at E u V c (schema_conclusion S) I K"
    "native_premise_family_at E u V m (schema_premises S) (schema_material_premises S)"
    using first by (auto simp: native_schema_at_def)
  obtain A qs x y z W J L where right:
    "artifact_at E u A" "record_at A r qs [x,y,z]" "binder_scope_at A x W"
    "pattern_quoted_at E u W y (schema_conclusion T) J L"
    "native_premise_family_at E u W z (schema_premises T) (schema_material_premises T)"
    using second by (auto simp: native_schema_at_def)
  have art: "A = R" by (rule environment_artifact_unique[OF ef right(1) left(1)])
  have rec: "record_at R r qs [x,y,z]" using right(2) art by simp
  have fields: "x = b \<and> y = c \<and> z = m" using record_at_unique[OF rec left(2)] by auto
  have scope_read: "binder_scope_at R b W" using right(3) art fields by simp
  have scope: "W = V" by (rule binder_scope_unique[OF scope_read left(3)])
  have head_read: "pattern_quoted_at E u V c (schema_conclusion T) J L" using right(4) scope fields by simp
  have heads: "schema_conclusion S = schema_conclusion T"
    using pattern_quoted_unique[OF left(4) head_read] by blast
  have body_read: "native_premise_family_at E u V m (schema_premises T) (schema_material_premises T)"
    using right(5) scope fields by simp
  have bodies: "schema_premises S = schema_premises T \<and> schema_material_premises S = schema_material_premises T"
    by (rule native_premise_family_unique[OF left(5) body_read])
  show ?thesis using heads bodies by (cases S; cases T) simp
qed

lemma native_schema_formed:
  assumes "native_schema_at E u r S"
  shows "schema_formed S"
proof -
  obtain c m V I K where head: "pattern_quoted_at E u V c (schema_conclusion S) I K"
    and body: "native_premise_family_at E u V m (schema_premises S) (schema_material_premises S)"
    using assms by (auto simp: native_schema_at_def)
  show ?thesis using pattern_quoted_formed[OF head] native_premise_family_formed[OF body]
    by (auto simp: schema_formed_def)
qed

section \<open>Definition interfaces and identified clause families\<close>

definition native_schema_family_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    (local_address \<times> 'u native_schema) set \<Rightarrow> bool" where
  "native_schema_family_at E u r C \<longleftrightarrow> environment_formed E \<and>
    (\<exists>R M. artifact_at E u R \<and> family_at R r M \<and> finite C \<and> single_valued C \<and>
      rel_dom C = rel_dom M \<and>
      (\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>S. (s,S) \<in> C \<and> native_schema_at E u a S)))"

theorem native_schema_family_unique:
  assumes first: "native_schema_family_at E u r C" and second: "native_schema_family_at E u r D"
  shows "C = D"
proof -
  have ef: "environment_formed E" using first by (simp add: native_schema_family_at_def)
  obtain R M where left: "artifact_at E u R" "family_at R r M" "single_valued C"
    "rel_dom C = rel_dom M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>S. (s,S) \<in> C \<and> native_schema_at E u a S)"
    using first by (auto simp: native_schema_family_at_def)
  obtain S N where right: "artifact_at E u S" "family_at S r N" "single_valued D"
    "rel_dom D = rel_dom N"
    "\<forall>s a. (s,a) \<in> N \<longrightarrow> (\<exists>S. (s,S) \<in> D \<and> native_schema_at E u a S)"
    using second by (auto simp: native_schema_family_at_def)
  have art: "S = R" by (rule environment_artifact_unique[OF ef right(1) left(1)])
  have family: "family_at R r N" using right(2) art by simp
  have graph: "N = M" by (rule family_at_unique[OF family left(2)])
  have domain: "rel_dom D = rel_dom M" using right(4) graph by simp
  have reads: "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>S. (s,S) \<in> D \<and> native_schema_at E u a S)"
    using right(5) graph by simp
  show ?thesis
    by (rule complete_socket_reading_unique[OF left(3-5) right(3) domain reads])
       (rule native_schema_unique)
qed

lemma native_schema_family_origin:
  assumes family: "native_schema_family_at E u r C" and member: "(s,S) \<in> C"
  shows "\<exists>R M a. artifact_at E u R \<and> family_at R r M \<and> (s,a) \<in> M \<and> native_schema_at E u a S"
proof -
  obtain R M where source: "artifact_at E u R" "family_at R r M" "single_valued C"
    "rel_dom C = rel_dom M"
    "\<forall>s a. (s,a) \<in> M \<longrightarrow> (\<exists>S. (s,S) \<in> C \<and> native_schema_at E u a S)"
    using family by (auto simp: native_schema_family_at_def)
  have key: "s \<in> rel_dom M" using rel_domI[OF member] source(4) by simp
  obtain a where field: "(s,a) \<in> M" using key by (auto simp: rel_dom_def)
  obtain T where recovered: "(s,T) \<in> C" "native_schema_at E u a T"
    using source(5) field by blast
  have same: "T = S" by (rule single_valued_outputs[OF source(3) recovered(1) member])
  show ?thesis using source(1,2) field recovered(2) same by blast
qed

lemma native_schema_family_formed:
  assumes family: "native_schema_family_at E u r C"
  shows "finite C \<and> single_valued C \<and> (\<forall>s S. (s,S) \<in> C \<longrightarrow> schema_formed S)"
proof -
  have base: "finite C \<and> single_valued C" using family by (auto simp: native_schema_family_at_def)
  have entries: "\<forall>s S. (s,S) \<in> C \<longrightarrow> schema_formed S"
  proof (intro allI impI)
    fix s S assume member: "(s,S) \<in> C"
    obtain a where read: "native_schema_at E u a S"
      using native_schema_family_origin[OF family member] by blast
    show "schema_formed S" by (rule native_schema_formed[OF read])
  qed
  show ?thesis using base entries by blast
qed

definition native_definition_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> local_address term_pattern \<Rightarrow>
    (local_address \<times> 'u native_schema) set \<Rightarrow> bool" where
  "native_definition_at E u r p C \<longleftrightarrow> environment_formed E \<and>
    (\<exists>R ps i m I K. artifact_at E u R \<and> record_at R r ps [i,m] \<and>
      scoped_pattern_at E u i p I K \<and> native_schema_family_at E u m C \<and>
      insert r (set ps) \<inter> (I \<union> {m}) = {} \<and> m \<notin> I)"

theorem native_definition_unique:
  assumes first: "native_definition_at E u r p C" and second: "native_definition_at E u r q D"
  shows "p = q \<and> C = D"
proof -
  have ef: "environment_formed E" using first by (simp add: native_definition_at_def)
  obtain R ps i m I K where left: "artifact_at E u R" "record_at R r ps [i,m]"
    "scoped_pattern_at E u i p I K" "native_schema_family_at E u m C"
    using first by (auto simp: native_definition_at_def)
  obtain S qs j n J W where right: "artifact_at E u S" "record_at S r qs [j,n]"
    "scoped_pattern_at E u j q J W" "native_schema_family_at E u n D"
    using second by (auto simp: native_definition_at_def)
  have art: "S = R" by (rule environment_artifact_unique[OF ef right(1) left(1)])
  have rec: "record_at R r qs [j,n]" using right(2) art by simp
  have fields: "j = i \<and> n = m" using record_at_unique[OF rec left(2)] by auto
  have interface: "scoped_pattern_at E u i q J W" using right(3) fields by simp
  have interfaces: "p = q" using scoped_pattern_unique[OF left(3) interface] by blast
  have family: "native_schema_family_at E u m D" using right(4) fields by simp
  have clauses: "C = D" by (rule native_schema_family_unique[OF left(4) family])
  show ?thesis using interfaces clauses by blast
qed

lemma native_definition_formed:
  assumes "native_definition_at E u r p C"
  shows "pattern_formed p \<and> finite C \<and> single_valued C \<and> (\<forall>s S. (s,S) \<in> C \<longrightarrow> schema_formed S)"
proof -
  obtain i m I K where interface: "scoped_pattern_at E u i p I K"
    and clauses: "native_schema_family_at E u m C"
    using assms by (auto simp: native_definition_at_def)
  show ?thesis using scoped_pattern_formed[OF interface] native_schema_family_formed[OF clauses] by blast
qed

text \<open>
  A prospective call's dependency is the location recovered from its citation,
  including the supplied artifact use. Its argument is a scoped pattern.
  Formation of this syntax invokes no truth predicate. A schema recovers its
  complete scope, conclusion, and family of calls and material premises. Their
  two-field and five-field records recover different operand roles. Family
  sockets remain distinct even when endpoints or recovered patterns agree.
  A definition recovers its scoped interface and complete identified clause
  family. A definition package must collect all dependency locations before
  meaning is applied.
\<close>

end
