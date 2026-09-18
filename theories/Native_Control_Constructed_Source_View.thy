theory Native_Control_Constructed_Source_View
  imports Native_Control_Guard_Execution Optional_Result_Views
begin

section \<open>The original complete source view is reused at an actual constructor result\<close>

definition installed_guard_source_checks where
  "installed_guard_source_checks rows=map_option (map (\<lambda>(i,r). (i,
    case r of None \<Rightarrow> False | Some (d,K,v) \<Rightarrow> installed_guard_source_available K v))) rows"

lemma admitted_guard_source_available:
  assumes installed: "admitted_guard_install body adapter target=Some rows"
    and member: "(i,Some (d,K,v))\<in>set rows"
  shows "installed_guard_source_available K v"
  by (rule admitted_guard_installed_truth[OF installed member])
    (simp only: installed_guard_source_available_exact; blast)

lemma admitted_guard_source_checks_exact:
  "installed_guard_source_checks (admitted_guard_install body adapter target)=
    admitted_guard_install_summary (admitted_guard_install body adapter target)"
proof -
  let ?result="admitted_guard_install body adapter target"
  let ?read="map (\<lambda>(i,r). (i,case r of None \<Rightarrow> False
    | Some (d,K,v) \<Rightarrow> installed_guard_source_available K v))"
  let ?view="map (\<lambda>(i,r). (i,r\<noteq>None))"
  have each: "?read rows=?view rows" if installed: "?result=Some rows" for rows
  proof (rule map_cong[OF refl])
    fix row assume inside: "row\<in>set rows"
    obtain i r where row: "row=(i,r)" by (cases row) auto
    show "(case row of (i,r) \<Rightarrow> (i,case r of None \<Rightarrow> False
      | Some (d,K,v) \<Rightarrow> installed_guard_source_available K v))=
      (case row of (i,r) \<Rightarrow> (i,r\<noteq>None))"
    proof (cases r)
      case None
      then show ?thesis by (simp add: row)
    next
      case (Some q)
      obtain d K v where q: "q=(d,K,v)" by (cases q) auto
      have member: "(i,Some (d,K,v))\<in>set rows" using inside by (simp only: row Some q)
      have available: "installed_guard_source_available K v"
        by (rule admitted_guard_source_available[OF installed member])
      show ?thesis by (simp only: row Some q prod.case option.case available; simp)
    qed
  qed
  have projection: "map_option id ?result=?result"
    by (cases ?result) (simp_all add: id_def)
  show ?thesis unfolding installed_guard_source_checks_def admitted_guard_install_summary_def
    by (rule optional_result_view_projection[OF projection]) (simp_all add: each id_def)

qed

definition admitted_guard_received where
  "admitted_guard_received body adapter target=(let rows=admitted_guard_install body adapter target in
    (rows,installed_guard_source_checks rows))"

lemma admitted_guard_received_reuses_original_view:
  "admitted_guard_received body adapter target=(let rows=admitted_guard_install body adapter target in
    (rows,admitted_guard_install_summary rows))"
  by (simp only: admitted_guard_received_def Let_def admitted_guard_source_checks_exact)

text \<open>The all-input equation retains the actual installation, all three
  original reports and every failure. Source availability is obtained from the
  constructor's proved original native package, using the exact source reader
  contract. It is not a constant checker for arbitrary supplied environments.
  This theorem alone neither adopts a computation change nor constructs a
  certified policy cause.\<close>

end
