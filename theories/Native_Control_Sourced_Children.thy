theory Native_Control_Sourced_Children
  imports Native_Control_Guard_Source Certificate_Construction_Review
    Finite_Presented_Native_Programs
begin

definition guard_source_record where
  "guard_source_record E xs=map_option (\<lambda>(d,K,v,P).
    (E,fimage (\<lambda>e. (e,guard_installation_coordinates E xs e))
       (finite_system_definitions (finite_guard_constructor xs)),d,K,v,P))
      (finite_install_quoted_guard_source E xs)"

lemma guard_source_record_fields:
  "guard_source_record E xs=Some (E',coordinates,d,K,v,P) \<longleftrightarrow>
    E'=E \<and> coordinates=fimage (\<lambda>e. (e,guard_installation_coordinates E xs e))
      (finite_system_definitions (finite_guard_constructor xs)) \<and>
    finite_install_quoted_guard E xs=Some (d,K,v) \<and> finite_native_source K v []=Some P"
  by (auto simp: guard_source_record_def finite_install_quoted_guard_source_fields
    split: option.splits prod.splits; cases d; auto)

lemma guard_source_record_projection:
  "map_option (\<lambda>(E,coordinates,d,K,v,P). (d,K,v)) (guard_source_record E xs)=
    finite_install_quoted_guard E xs"
proof (cases "finite_install_quoted_guard E xs")
  case None
  then show ?thesis by (simp add: guard_source_record_def finite_install_quoted_guard_source_def)
next
  case (Some z)
  obtain d K v where z: "z=(d,K,v)" by (cases z) auto
  obtain P where source: "finite_install_quoted_guard_source E xs=Some (d,K,v,P)"
    using finite_install_quoted_guard_source_total[OF Some[unfolded z]] by blast
  show ?thesis by (simp only: guard_source_record_def source option.simps prod.case Some z)
qed

definition admitted_guard_source_records where
  "admitted_guard_source_records body adapter target=map_option (map (\<lambda>(i,source). (i,
    case source of None \<Rightarrow> None | Some (d,E,u) \<Rightarrow> guard_source_record E checked_judgment_rows)))
      (admitted_guard_requests body adapter target)"

theorem admitted_guard_source_records_projection:
  "map_option (map (\<lambda>(i,source). (i,map_option (\<lambda>(E,coordinates,d,K,v,P). (d,K,v)) source)))
      (admitted_guard_source_records body adapter target)=admitted_guard_install body adapter target"
proof (cases "admitted_guard_requests body adapter target")
  case None
  then show ?thesis by (simp add: admitted_guard_source_records_def admitted_guard_install_def)
next
  case (Some rows)
  show ?thesis
    unfolding admitted_guard_source_records_def admitted_guard_install_def Some
    apply (simp only: option.simps map_map)
    apply (rule map_cong[OF refl])
    apply (rename_tac row)
    apply (case_tac row)
    apply (rename_tac i source)
    apply (case_tac source)
     apply (simp add: comp_def)
    apply (rename_tac entry)
    apply (case_tac entry)
    apply (simp add: comp_def guard_source_record_projection split: prod.splits)
    done
qed

theorem admitted_guard_source_records_original:
  assumes result: "admitted_guard_source_records body adapter target=Some records"
    and member: "(i,Some (E,coordinates,d,K,v,P))\<in>set records"
  shows "finite_native_source K v []=Some P"
    "\<exists>installed. admitted_guard_install body adapter target=Some installed \<and> (i,Some (d,K,v))\<in>set installed"
proof -
  have read: "finite_native_source K v []=Some P"
    if equation: "Some (E,coordinates,d,K,v,P)=guard_source_record X checked_judgment_rows" for X
    using equation[symmetric] by (simp only: guard_source_record_fields; blast)
  obtain X where actual_record:
    "Some (E,coordinates,d,K,v,P)=guard_source_record X checked_judgment_rows"
    using result member by (auto simp: admitted_guard_source_records_def split: option.splits)
  show "finite_native_source K v []=Some P" by (rule read[OF actual_record])
  let ?project="\<lambda>(i,source). (i,map_option (\<lambda>(E,coordinates,d,K,v,P). (d,K,v)) source)"
  have installed: "admitted_guard_install body adapter target=Some (map ?project records)"
    using admitted_guard_source_records_projection[of body adapter target] result by simp
  have included: "(i,Some (d,K,v))\<in>set (map ?project records)"
    using imageI[OF member, of ?project] by (simp only: set_map prod.case option.simps)
  show "\<exists>installed. admitted_guard_install body adapter target=Some installed \<and> (i,Some (d,K,v))\<in>set installed"
    using installed included by blast
qed

definition guard_mapped_child_demands where
  "guard_mapped_child_demands E xs H =
    fimage (\<lambda>(s,e,t). (guard_installation_coordinates E xs e,t)) H"

definition guard_source_certificate_candidates where
  "guard_source_certificate_candidates methods record H=(case record of (E,coordinates,d,K,v,P) \<Rightarrow>
    let D=guard_mapped_child_demands E checked_judgment_rows H in
      (D,certificate_constructor_family methods P D))"

text \<open>The complete original installed source and the complete definition
  coordinate map accompany every successful occurrence. Projection gives the
  original installation exactly, including every absent report and failed row.
  Child calls are mapped to that source before its constructors run. This does
  not convert natural clause, variable or socket coordinates into native proof
  coordinates: every resulting proof must satisfy the original native-source
  checker through its own certificate question. A successful leaf still cannot
  establish its siblings, the guard root, replay, or a policy cause.\<close>

end
