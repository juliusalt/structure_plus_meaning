theory Factor_Amendment_Comparisons
  imports Factor_Amendment_Reports Factor_Comparison_Support
begin

section \<open>The complete report profile has finite self-contained supporting data\<close>

lemma amendment_report_rows_formed:
  assumes reports: "amendment_reports_at C q H W F fu fr b"
  shows "finite W \<and> W\<noteq>{} \<and> (\<forall>z\<in>W. term_formed (correspondence_row_data z))"
proof -
  obtain A l G p E pu pr P d N qu qr Q T where fields:
    "current_entry_scope_quoted_at C q A l G p E pu pr P d" "generation_program_scope H N qu qr Q"
    "closed_native_package_at F fu fr T" "native_package_environment F fu fr=F"
    "system_report_coverage P Q
      (system_comparison_definitions P Q (native_package_roots E pu pr))
      (system_comparison_definitions Q P (native_package_roots N qu qr)) W (program_judgment_reports T b)"
    using reports unfolding amendment_reports_at_def by blast
  have packages: "native_package_at E pu pr P" "native_package_at N qu qr Q"
    using current_entry_scope_closed[OF fields(1)] generation_program_scope_closed[OF fields(2)]
    by (auto simp: closed_native_package_at_def)
  have environments: "environment_formed E" "environment_formed N"
    using native_package_projection(1)[OF packages(1)] native_package_projection(1)[OF packages(2)]
    by (auto simp: native_package_formed_def)
  have old: "\<And>d. d\<in>system_definitions P \<Longrightarrow> octets_formed (snd d)"
    by (rule environment_position_address[OF environments(1)], rule native_package_entry_position[OF packages(1)], assumption)
  have new: "\<And>d. d\<in>system_definitions Q \<Longrightarrow> octets_formed (snd d)"
    by (rule environment_position_address[OF environments(2)], rule native_package_entry_position[OF packages(2)], assumption)
  let ?U="system_comparison_definitions P Q (native_package_roots E pu pr)"
  let ?V="system_comparison_definitions Q P (native_package_roots N qu qr)"
  have coverage: "correspondence_complete ?U ?V W"
    and inside: "?U\<subseteq>system_definitions P" "?V\<subseteq>system_definitions Q"
    using fields(5) by (auto simp: system_report_coverage_def)
  have boundary: "W\<subseteq>insert None (Some ` ?U)\<times>insert None (Some ` ?V)"
    by (rule correspondence_complete_boundary[OF coverage])
  have left_bound: "insert None (Some ` ?U)\<subseteq>insert None (Some ` system_definitions P)"
    using image_mono[OF inside(1), where f=Some] by auto
  have right_bound: "insert None (Some ` ?V)\<subseteq>insert None (Some ` system_definitions Q)"
    using image_mono[OF inside(2), where f=Some] by auto
  have bound: "W\<subseteq>insert None (Some ` system_definitions P)\<times>insert None (Some ` system_definitions Q)"
    by (rule subset_trans[OF boundary], rule Sigma_mono[OF left_bound]) (rule right_bound)
  have rows: "\<forall>z\<in>W. term_formed (correspondence_row_data z)"
  proof (intro ballI)
    fix z assume member: "z\<in>W"
    have left: "fst z=None \<or> (\<exists>d\<in>system_definitions P. fst z=Some d)"
      and right: "snd z=None \<or> (\<exists>d\<in>system_definitions Q. snd z=Some d)"
      using bound member by auto
    show "term_formed (correspondence_row_data z)"
      using left right old new by (auto simp: correspondence_row_data_def)
  qed
  show ?thesis using amendment_reports_nonempty[OF fields(1-4) reports] rows by blast
qed

definition amendment_comparison_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> generation_core \<Rightarrow>
    local_address option artifact_environment \<Rightarrow> local_address option \<Rightarrow> local_address \<Rightarrow> bool" where
  "amendment_comparison_at C q H M mu mr \<longleftrightarrow>
    (\<exists>W F fu fr b N nu nr.
      comparison_support_at M mu mr W F fu fr b N nu nr \<and> amendment_reports_at C q H W F fu fr b)"

theorem amendment_comparison_with_support:
  assumes support: "comparison_support_at M mu mr W F fu fr b N nu nr"
  shows "amendment_comparison_at C q H M mu mr \<longleftrightarrow> amendment_reports_at C q H W F fu fr b"
proof
  assume accepted: "amendment_comparison_at C q H M mu mr"
  obtain V E eu er d L lu lr where other: "comparison_support_at M mu mr V E eu er d L lu lr"
    and reports: "amendment_reports_at C q H V E eu er d"
    using accepted unfolding amendment_comparison_at_def by blast
  have same: "W=V \<and> F=E \<and> fu=eu \<and> fr=er \<and> b=d"
    using comparison_support_at_unique[OF support other] by blast
  show "amendment_reports_at C q H W F fu fr b" using reports same by simp
next
  assume "amendment_reports_at C q H W F fu fr b"
  then show "amendment_comparison_at C q H M mu mr"
    using support unfolding amendment_comparison_at_def by blast
qed

theorem amendment_comparison_total:
  assumes reports: "amendment_reports_at C q H W F fu fr b"
    and remainder: "environment_formed N" "(nu,nr)\<in>environment_positions N"
  shows "\<exists>M. comparison_support_at M None [] W F fu fr b N nu nr \<and>
    amendment_comparison_at C q H M None []"
proof -
  obtain T where reporter: "closed_native_package_at F fu fr T" "b\<in>system_definitions T"
    using reports unfolding amendment_reports_at_def by blast
  have package: "native_package_at F fu fr T" using reporter(1) by (simp add: closed_native_package_at_def)
  have formed: "environment_formed F"
    using native_package_projection(1)[OF package] by (simp add: native_package_formed_def)
  have root: "(fu,fr)\<in>environment_positions F" by (rule native_package_root_position[OF package])
  have entry: "b\<in>environment_positions F" by (rule native_package_entry_position[OF package reporter(2)])
  have finite: "finite W" and rows: "\<And>z. z\<in>W \<Longrightarrow> term_formed (correspondence_row_data z)"
    using amendment_report_rows_formed[OF reports] by blast+
  obtain M where support: "comparison_support_at M None [] W F fu fr b N nu nr"
    using comparison_support_total[OF finite rows formed root entry remainder] by blast
  have accepted: "amendment_comparison_at C q H M None []"
    using reports by (simp only: amendment_comparison_with_support[OF support])
  show ?thesis using support accepted by blast
qed

theorem amendment_comparison_complete_calls:
  assumes current: "current_entry_scope_quoted_at C q A l G p E pu pr P d"
    and candidate: "generation_program_scope H N qu qr Q"
    and reporter: "closed_native_package_at F fu fr T"
    and support: "comparison_support_at M mu mr W F fu fr b L lu lr"
    and accepted: "amendment_comparison_at C q H M mu mr"
  shows "{x. \<exists>y p i. ((Some x,y),(p,i))\<in>program_judgment_reports T b} =
      system_comparison_calls P Q (native_package_roots E pu pr)"
    and "{y. \<exists>x p i. ((x,Some y),(p,i))\<in>program_judgment_reports T b} =
      system_comparison_calls Q P (native_package_roots N qu qr)"
proof -
  have minimal: "native_package_environment F fu fr=F" by (rule native_package_closed_environment_fixed[OF reporter])
  have reports: "amendment_reports_at C q H W F fu fr b"
    using accepted by (simp only: amendment_comparison_with_support[OF support])
  show "{x. \<exists>y p i. ((Some x,y),(p,i))\<in>program_judgment_reports T b} =
      system_comparison_calls P Q (native_package_roots E pu pr)"
    "{y. \<exists>x p i. ((x,Some y),(p,i))\<in>program_judgment_reports T b} =
      system_comparison_calls Q P (native_package_roots N qu qr)"
    by (rule amendment_reports_complete_calls[OF current candidate reporter minimal reports])+
qed

theorem amendment_comparison_empty_rejected:
  assumes support: "comparison_support_at M mu mr {} F fu fr b N nu nr"
  shows "\<not>amendment_comparison_at C q H M mu mr"
proof
  assume accepted: "amendment_comparison_at C q H M mu mr"
  have reports: "amendment_reports_at C q H {} F fu fr b"
    using accepted by (simp only: amendment_comparison_with_support[OF support])
  show False using amendment_report_rows_formed[OF reports] by blast
qed

text \<open>
  Every complete report profile has an actual finite native data quotation.
  Its row boundary follows from the old and candidate packages; it is not
  chosen by the supporting value. The quoted reporter scope is closed and its
  selected entry belongs to the recovered program. That program describes
  every required call, including unbounded argument domains.

  The value retains exactly the submitted correspondence and reporter.
  No alternative collection, scope, or selected definition can be read from
  the same complete value. Empty structural material is formed data but fails
  this actual amendment profile. Soundness of preservation and complete report
  coverage remain the existing separate mathematical obligations. A native
  checker for those obligations is still required.
\<close>

end
