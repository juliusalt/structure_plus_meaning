theory Factor_Correspondence_Reports
  imports Bootstrap_Relations
begin

section \<open>Every endpoint is paired or explicitly left without a counterpart\<close>

definition correspondence_completion ::
  "'a set \<Rightarrow> 'b set \<Rightarrow> ('a\<times>'b) set \<Rightarrow> ('a option\<times>'b option) set" where
  "correspondence_completion A B M =
    map_prod Some Some ` M \<union>
    {(Some a,None) |a. a\<in>A-rel_dom M} \<union>
    {(None,Some b) |b. b\<in>B-rel_ran M}"

definition correspondence_pairs :: "('a option\<times>'b option) set \<Rightarrow> ('a\<times>'b) set" where
  "correspondence_pairs R = {(a,b). (Some a,Some b)\<in>R}"

definition correspondence_complete ::
  "'a set \<Rightarrow> 'b set \<Rightarrow> ('a option\<times>'b option) set \<Rightarrow> bool" where
  "correspondence_complete A B R \<longleftrightarrow>
    (\<exists>M. M\<subseteq>A\<times>B \<and> R=correspondence_completion A B M)"

lemma correspondence_completion_members [simp]:
  "(Some a,Some b)\<in>correspondence_completion A B M \<longleftrightarrow> (a,b)\<in>M"
  "(Some a,None)\<in>correspondence_completion A B M \<longleftrightarrow> a\<in>A-rel_dom M"
  "(None,Some b)\<in>correspondence_completion A B M \<longleftrightarrow> b\<in>B-rel_ran M"
  "(None,None)\<notin>correspondence_completion A B M"
  by (auto simp: correspondence_completion_def)

lemma correspondence_completion_pairs [simp]:
  "correspondence_pairs (correspondence_completion A B M)=M"
  by (auto simp: correspondence_pairs_def)

lemma correspondence_complete_iff:
  "correspondence_complete A B R \<longleftrightarrow>
    correspondence_pairs R\<subseteq>A\<times>B \<and>
    R=correspondence_completion A B (correspondence_pairs R)"
  unfolding correspondence_complete_def by auto

lemma correspondence_completion_complete:
  assumes "M\<subseteq>A\<times>B"
  shows "correspondence_complete A B (correspondence_completion A B M)"
  using assms unfolding correspondence_complete_def by blast

theorem correspondence_complete_endpoints:
  assumes complete: "correspondence_complete A B R"
  shows "{a. \<exists>y. (Some a,y)\<in>R}=A"
    and "{b. \<exists>x. (x,Some b)\<in>R}=B"
proof -
  obtain M where inside: "M\<subseteq>A\<times>B" and rows: "R=correspondence_completion A B M"
    using complete unfolding correspondence_complete_def by blast
  show "{a. \<exists>y. (Some a,y)\<in>R}=A"
  proof
    show "{a. \<exists>y. (Some a,y)\<in>R}\<subseteq>A"
      using inside by (auto simp: rows correspondence_completion_def)
    show "A\<subseteq>{a. \<exists>y. (Some a,y)\<in>R}"
    proof
      fix a assume member: "a\<in>A"
      show "a\<in>{a. \<exists>y. (Some a,y)\<in>R}"
      proof (cases "a\<in>rel_dom M")
        case True
        then obtain b where pair: "(a,b)\<in>M" by (auto simp: rel_dom_def)
        have "(Some a,Some b)\<in>R" using pair by (simp add: rows)
        then show ?thesis by blast
      next
        case False
        have "(Some a,None)\<in>R" using member False by (simp add: rows)
        then show ?thesis by blast
      qed
    qed
  qed
  show "{b. \<exists>x. (x,Some b)\<in>R}=B"
  proof
    show "{b. \<exists>x. (x,Some b)\<in>R}\<subseteq>B"
      using inside by (auto simp: rows correspondence_completion_def)
    show "B\<subseteq>{b. \<exists>x. (x,Some b)\<in>R}"
    proof
      fix b assume member: "b\<in>B"
      show "b\<in>{b. \<exists>x. (x,Some b)\<in>R}"
      proof (cases "b\<in>rel_ran M")
        case True
        then obtain a where pair: "(a,b)\<in>M" by (auto simp: rel_ran_def)
        have "(Some a,Some b)\<in>R" using pair by (simp add: rows)
        then show ?thesis by blast
      next
        case False
        have "(None,Some b)\<in>R" using member False by (simp add: rows)
        then show ?thesis by blast
      qed
    qed
  qed
qed

theorem correspondence_complete_missing:
  assumes complete: "correspondence_complete A B R"
  shows "(Some a,None)\<in>R \<longleftrightarrow> a\<in>A \<and> \<not>(\<exists>b. (Some a,Some b)\<in>R)"
    and "(None,Some b)\<in>R \<longleftrightarrow> b\<in>B \<and> \<not>(\<exists>a. (Some a,Some b)\<in>R)"
    and "(None,None)\<notin>R"
  using complete unfolding correspondence_complete_def
  by (auto simp: rel_dom_def rel_ran_def)

lemma correspondence_complete_boundary:
  assumes "correspondence_complete A B R"
  shows "R\<subseteq>insert None (Some ` A)\<times>insert None (Some ` B)"
  using assms unfolding correspondence_complete_def
  by (auto simp: correspondence_completion_def)

lemma correspondence_complete_finite:
  assumes "correspondence_complete A B R" "finite A" "finite B"
  shows "finite R"
  by (rule finite_subset[OF correspondence_complete_boundary[OF assms(1)]])
     (simp add: assms(2,3))

lemma correspondence_complete_domains_unique:
  assumes "correspondence_complete A B R" "correspondence_complete C D R"
  shows "A=C \<and> B=D"
  using correspondence_complete_endpoints[OF assms(1)] correspondence_complete_endpoints[OF assms(2)] by blast

lemma correspondence_complete_empty:
  assumes complete: "correspondence_complete A B R"
  shows "R={} \<longleftrightarrow> A={} \<and> B={}"
  using correspondence_complete_endpoints[OF complete]
    correspondence_complete_boundary[OF complete] correspondence_complete_missing(3)[OF complete]
  by auto

lemma diagonal_correspondence_complete:
  "correspondence_complete A A ((\<lambda>a. (Some a,Some a)) ` A)"
proof -
  let ?M="(\<lambda>a. (a,a)) ` A"
  have "correspondence_completion A A ?M=(\<lambda>a. (Some a,Some a)) ` A"
    by (auto simp: correspondence_completion_def rel_dom_def rel_ran_def)
  then show ?thesis using correspondence_completion_complete[of ?M A A] by auto
qed

section \<open>Separate declarations on each complete judgment correspondence\<close>

type_synonym ('a,'b) correspondence_reports =
  "(('a option\<times>'b option)\<times>(bool\<times>bool)) set"

definition report_coverage :: "'a set \<Rightarrow> 'b set \<Rightarrow> ('a,'b) correspondence_reports \<Rightarrow> bool" where
  "report_coverage A B R \<longleftrightarrow> correspondence_complete A B (rel_dom R) \<and> single_valued R"

definition reported_interpretation :: "('a,'b) correspondence_reports \<Rightarrow> ('a\<times>'b) set" where
  "reported_interpretation R=correspondence_pairs (rel_dom R)"

definition reported_preservation :: "('a,'b) correspondence_reports \<Rightarrow> ('a option\<times>'b option) set" where
  "reported_preservation R={q. \<exists>i. (q,(True,i))\<in>R}"

definition reported_incompatibility :: "('a,'b) correspondence_reports \<Rightarrow> ('a option\<times>'b option) set" where
  "reported_incompatibility R={q. \<exists>p. (q,(p,True))\<in>R}"

definition constant_correspondence_reports ::
  "('a option\<times>'b option) set \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> ('a,'b) correspondence_reports" where
  "constant_correspondence_reports M p i=(\<lambda>q. (q,(p,i))) ` M"

lemma constant_reports_domain [simp]:
  "rel_dom (constant_correspondence_reports M p i)=M"
  by (auto simp: constant_correspondence_reports_def rel_dom_def)

lemma constant_reports_coverage:
  assumes "correspondence_complete A B M"
  shows "report_coverage A B (constant_correspondence_reports M p i)"
proof -
  have "single_valued (constant_correspondence_reports M p i)"
    by (auto simp: constant_correspondence_reports_def single_valued_def)
  then show ?thesis using assms by (simp add: report_coverage_def)
qed

lemma report_coverage_endpoints:
  assumes "report_coverage A B R"
  shows "{a. \<exists>y p i. ((Some a,y),(p,i))\<in>R}=A"
    and "{b. \<exists>x p i. ((x,Some b),(p,i))\<in>R}=B"
  using correspondence_complete_endpoints[of A B "rel_dom R"] assms
  by (auto simp: report_coverage_def rel_dom_def)

theorem report_coverage_declarations:
  assumes complete: "report_coverage A B R" and member: "q\<in>rel_dom R"
  shows "\<exists>!z. (q,z)\<in>R"
    and "\<exists>p i. (q,(p,i))\<in>R \<and>
      (q\<in>reported_preservation R\<longleftrightarrow>p) \<and> (q\<in>reported_incompatibility R\<longleftrightarrow>i)"
proof -
  have functional: "single_valued R" using complete by (simp add: report_coverage_def)
  obtain p i where row: "(q,(p,i))\<in>R" using member by (auto simp: rel_dom_def)
  have exact: "\<And>z. (q,z)\<in>R \<Longrightarrow> z=(p,i)"
    by (rule single_valued_outputs[OF functional _ row])
  show "\<exists>!z. (q,z)\<in>R" using row exact by blast
  have claims: "q\<in>reported_preservation R\<longleftrightarrow>p"
    "q\<in>reported_incompatibility R\<longleftrightarrow>i"
    using row exact by (auto simp: reported_preservation_def reported_incompatibility_def)
  show "\<exists>p i. (q,(p,i))\<in>R \<and>
      (q\<in>reported_preservation R\<longleftrightarrow>p) \<and> (q\<in>reported_incompatibility R\<longleftrightarrow>i)"
    using row claims by blast
qed

lemma report_coverage_empty:
  assumes "report_coverage A B R"
  shows "R={} \<longleftrightarrow> A={} \<and> B={}"
  using correspondence_complete_empty[of A B "rel_dom R"] assms
  by (simp add: report_coverage_def)

text \<open>
  A missing counterpart is an explicit row, present exactly when the declared
  correspondence gives that endpoint no partner. It does not claim that a
  different correspondence is impossible. Both endpoint domains are supplied
  independently of the rows, and complete rows determine those domains again.

  Judgment reports carry separate preservation and intentional-incompatibility
  declarations. Each flag is present even when false; false means no such
  declaration, not a proof of a negative semantic fact. Their complete reporting
  boundary includes every required endpoint. The positive subsets need not cover
  or partition that boundary. Interpretation, preservation, and incompatibility
  are derived projections, with no repeated storage of their judgment pairs.
  Their semantic and authority conditions are checked separately.
\<close>

end
