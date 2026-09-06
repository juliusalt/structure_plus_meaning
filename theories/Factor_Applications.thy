theory Factor_Applications
  imports Factor_Packages
begin

section \<open>A ground call exposes a definition citation and a term argument\<close>

definition native_application_at ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow> 'u definition_site \<Rightarrow>
    factor_term \<Rightarrow> local_address set \<Rightarrow> local_address set \<Rightarrow> bool" where
  "native_application_at E u r d t I K \<longleftrightarrow> environment_formed E \<and>
    (\<exists>R ps c a cite C J A. artifact_at E u R \<and> record_at R r ps [c,a] \<and>
      citation_at R c cite C \<and> citation_location E u cite (fst d) (snd d) \<and>
      term_quoted_at E u a t J A \<and>
      insert r (set ps) \<inter> (C \<union> J) = {} \<and> C \<inter> J = {} \<and>
      I = insert r (set ps \<union> C \<union> J) \<and> K = citation_slots cite \<union> A \<and>
      I \<inter> K = {})"

theorem native_application_unique:
  assumes first: "native_application_at E u r d t I K"
    and second: "native_application_at E u r e x J W"
  shows "d = e \<and> t = x \<and> I = J \<and> K = W"
proof -
  have ef: "environment_formed E" using first by (simp add: native_application_at_def)
  obtain R ps c a cite C A L where left:
    "artifact_at E u R" "record_at R r ps [c,a]" "citation_at R c cite C"
    "citation_location E u cite (fst d) (snd d)" "term_quoted_at E u a t A L"
    "I = insert r (set ps \<union> C \<union> A)" "K = citation_slots cite \<union> L"
    using first by (auto simp: native_application_at_def)
  obtain S qs b z code D B N where right:
    "artifact_at E u S" "record_at S r qs [b,z]" "citation_at S b code D"
    "citation_location E u code (fst e) (snd e)" "term_quoted_at E u z x B N"
    "J = insert r (set qs \<union> D \<union> B)" "W = citation_slots code \<union> N"
    using second by (auto simp: native_application_at_def)
  have art: "S = R" by (rule environment_artifact_unique[OF ef right(1) left(1)])
  have rec: "record_at R r qs [b,z]" using right(2) art by simp
  have fields: "qs = ps \<and> b = c \<and> z = a" using record_at_unique[OF rec left(2)] by auto
  have other_cite: "citation_at R c code D" using right(3) art fields by simp
  have citation: "code = cite \<and> D = C" using citation_at_unique[OF other_cite left(3)] by blast
  have other_location: "citation_location E u cite (fst e) (snd e)" using right(4) citation by simp
  have location: "fst d = fst e \<and> snd d = snd e"
    by (rule citation_location_unique[OF ef left(4) other_location])
  have sites: "d = e" using location by (cases d; cases e) simp
  have other_argument: "term_quoted_at E u a x B N" using right(5) fields by simp
  have argument: "t = x \<and> A = B \<and> L = N" by (rule term_quoted_unique[OF left(5) other_argument])
  show ?thesis using sites argument citation fields left(6,7) right(6,7) by simp
qed

lemma native_application_properties:
  assumes "native_application_at E u r d t I K"
  shows "term_formed t \<and> r \<in> I \<and> finite I \<and> finite K \<and> I \<inter> K = {}"
proof -
  obtain R ps c a cite C J A where parts:
    "citation_at R c cite C" "term_quoted_at E u a t J A"
    "I = insert r (set ps \<union> C \<union> J)" "K = citation_slots cite \<union> A" "I \<inter> K = {}"
    using assms by (auto simp: native_application_at_def)
  have raw: "raw_citation_at R c cite C" using parts(1) by (simp add: citation_at_def)
  have slots: "finite (citation_slots cite)" by (cases cite) simp_all
  show ?thesis using raw_citation_interior(1)[OF raw] term_quoted_formed[OF parts(2)]
    term_quoted_root_interior[OF parts(2)] term_quoted_finite[OF parts(2)] slots parts(3-5) by auto
qed

lemma native_application_target:
  assumes "native_application_at E u r d t I K"
  shows "d \<in> environment_positions E"
proof -
  obtain cite where loc: "citation_location E u cite (fst d) (snd d)"
    using assms by (auto simp: native_application_at_def)
  obtain R where target: "artifact_at E (fst d) R" "anchor_formed (R,snd d)"
    using citation_location_has_artifact[OF loc] by blast
  show ?thesis using target by (cases d) (auto simp: anchor_formed_def)
qed

definition native_application_formed ::
  "'u artifact_environment \<Rightarrow> 'u \<Rightarrow> local_address \<Rightarrow>
    'u \<Rightarrow> local_address \<Rightarrow> bool" where
  "native_application_formed E pu pr au ar \<longleftrightarrow>
    (\<exists>P d t I K. native_package_at E pu pr P \<and> native_application_at E au ar d t I K \<and>
      schema_call_formed P d t)"

lemma native_application_formed_with_reads:
  assumes package: "native_package_at E pu pr P" and app: "native_application_at E au ar d t I K"
  shows "native_application_formed E pu pr au ar \<longleftrightarrow> schema_call_formed P d t"
proof
  assume "native_application_formed E pu pr au ar"
  then obtain Q e x J W where other: "native_package_at E pu pr Q" "native_application_at E au ar e x J W"
    "schema_call_formed Q e x" unfolding native_application_formed_def by blast
  have program: "Q=P" by (rule native_package_unique[OF other(1) package])
  have argument: "e=d \<and> x=t" using native_application_unique[OF other(2) app] by blast
  show "schema_call_formed P d t" using other(3) program argument by simp
next
  assume "schema_call_formed P d t"
  then show "native_application_formed E pu pr au ar" using package app unfolding native_application_formed_def by blast
qed

lemma native_application_has_definition:
  assumes formed: "native_application_formed E pu pr au ar"
    and app: "native_application_at E au ar d t I K"
  shows "\<exists>p C. native_definition_at E (fst d) (snd d) p C \<and> pattern_accepts p t"
proof -
  obtain P e x J W where package: "native_package_at E pu pr P"
    and other: "native_application_at E au ar e x J W" and call: "schema_call_formed P e x"
    using formed by (auto simp: native_application_formed_def)
  have same: "e = d \<and> x = t" using native_application_unique[OF other app] by blast
  obtain U where proj: "P = native_program E U"
    using package unfolding native_package_at_def by blast
  obtain p where interface: "(d,p) \<in> system_interfaces P" and accepts: "pattern_accepts p t"
    using call same by (auto simp: schema_call_formed_def)
  obtain C where read: "native_definition_at E (fst d) (snd d) p C"
    using interface proj by (auto simp: native_definition_graph_def)
  show ?thesis using read accepts by blast
qed

text \<open>
  The two-field call reader recovers syntax and a dependency location without
  testing truth. Formation joins that call to an explicitly selected native
  package and checks its recovered interface. The supplied environment is
  finite for this application; no fixed foundation environment bounds the
  set of future argument terms.
\<close>

end
