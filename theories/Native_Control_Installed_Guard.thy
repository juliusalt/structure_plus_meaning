theory Native_Control_Installed_Guard
  imports Native_Control_Guard_Construction Native_Control_Admitted_Selection
begin

section \<open>The installed guard consumes all original native decisions\<close>

definition admitted_guard_install where
  "admitted_guard_install body adapter target=map_option (map (\<lambda>(i,source). (i,
    case source of None \<Rightarrow> None | Some (d,E,u) \<Rightarrow>
      finite_install_quoted_guard E checked_judgment_rows))) (admitted_guard_requests body adapter target)"

lemma admitted_guard_install_fields:
  assumes installed: "admitted_guard_install body adapter target=Some results"
    and member: "(i,Some (d,K,v))\<in>set results"
  obtains rows e E u where "admitted_guard_requests body adapter target=Some rows"
    "(i,Some (e,E,u))\<in>set rows"
    "judgment_bridge_install body=Some rows"
    "judgment_artifact_choice adapter=Some Complete_Artifact_Body"
    "guard_representation_choice target=Some Complete_Guard_Target"
    "finite_install_quoted_guard E checked_judgment_rows=Some (d,K,v)"
proof -
  obtain rows e E u where requested: "admitted_guard_requests body adapter target=Some rows"
    and original: "(i,Some (e,E,u))\<in>set rows"
    and built: "finite_install_quoted_guard E checked_judgment_rows=Some (d,K,v)"
    using installed member by (auto simp: admitted_guard_install_def split: option.splits)
  have bridge: "judgment_bridge_install body=Some rows"
    by (rule admitted_guard_requests_fields(1)[OF requested original])
  have adapter: "judgment_artifact_choice adapter=Some Complete_Artifact_Body"
    by (rule admitted_guard_requests_fields(2)[OF requested original])
  have target: "guard_representation_choice target=Some Complete_Guard_Target"
    by (rule admitted_guard_requests_fields(3)[OF requested original])
  show thesis by (rule that[OF requested original bridge adapter target built])
qed

lemma checked_judgment_rows_exact:
  "t\<in>decode_finite_term ` set checked_judgment_rows \<longleftrightarrow>
    (\<exists>s. t=decode_finite_term (syntax_judgment_data s) \<and> syntax_judgment_truth s)"
proof
  assume "t\<in>decode_finite_term ` set checked_judgment_rows"
  then obtain s where within: "s\<in>set syntax_judgment_cases"
    and truth: "syntax_judgment_check s" and data_eq: "t=decode_finite_term (syntax_judgment_data s)"
    by (auto simp: checked_judgment_rows_def filtered_judgment_rows_def)
  show "\<exists>s. t=decode_finite_term (syntax_judgment_data s) \<and> syntax_judgment_truth s"
    by (rule exI[of _ s]) (simp only: data_eq syntax_judgment_check_exact[symmetric] truth)
next
  assume "\<exists>s. t=decode_finite_term (syntax_judgment_data s) \<and> syntax_judgment_truth s"
  then obtain s where data_eq: "t=decode_finite_term (syntax_judgment_data s)"
    and truth: "syntax_judgment_truth s" by blast
  have within: "s\<in>set syntax_judgment_cases" by (rule syntax_truth_has_case[OF truth])
  have checked: "syntax_judgment_check s" by (simp only: syntax_judgment_check_exact truth)
  have row: "syntax_judgment_data s\<in>set checked_judgment_rows"
    unfolding checked_judgment_rows_def filtered_judgment_rows_def
    by (simp only: set_map; rule imageI) (use within checked in simp)
  show "t\<in>decode_finite_term ` set checked_judgment_rows"
    by (simp only: data_eq; rule imageI[OF row])
qed

theorem admitted_guard_installed_truth:
  assumes installed: "admitted_guard_install body adapter target=Some results"
    and member: "(i,Some (d,K,v))\<in>set results"
  obtains E T where
    "finite_environment_formed K"
    "environment_included (decode_finite_environment E) (decode_finite_environment K)"
    "native_package_at (decode_finite_environment K) v [] T"
    "\<And>R. (d,Target_Term (Whole_Artifact R))\<in>positive_meaning T \<longleftrightarrow>
      (\<exists>r s. complete_data_quoted_at R r (decode_finite_term (syntax_judgment_data s)) \<and>
        syntax_judgment_truth s)"
proof -
  obtain E where built: "finite_install_quoted_guard E checked_judgment_rows=Some (d,K,v)"
    by (rule admitted_guard_install_fields[OF installed member]) blast
  obtain T where formed: "finite_environment_formed K"
    and preserve: "environment_included (decode_finite_environment E) (decode_finite_environment K)"
    and native: "native_package_at (decode_finite_environment K) v [] T"
    and meaning: "\<And>z. (d,z)\<in>positive_meaning T \<longleftrightarrow>
      (\<exists>R r t. z=Target_Term (Whole_Artifact R) \<and> complete_data_quoted_at R r t \<and>
        t\<in>decode_finite_term ` set checked_judgment_rows)"
    by (rule finite_install_quoted_guard_correct[OF built]) blast
  show thesis by (rule that[OF formed preserve native])
    (simp only: meaning checked_judgment_rows_exact factor_term.inject exact_target.inject; blast)
qed

corollary admitted_guard_original_policy_cause:
  assumes installed: "admitted_guard_install body adapter target=Some results"
    and member: "(i,Some (d,K,v))\<in>set results"
    and cause: "certified_policy_cause_at (decode_finite_environment K) v [] d E gu gr G H root R"
  shows "\<exists>r s. complete_data_quoted_at R r (decode_finite_term (syntax_judgment_data s)) \<and>
    syntax_judgment_truth s"
  by (rule admitted_guard_installed_truth[OF installed member])
    (use certified_policy_cause_sound[OF _ cause] in blast)

definition admitted_guard_install_summary where
  "admitted_guard_install_summary rows=map_option (map (\<lambda>(i,r). (i,r\<noteq>None))) rows"

text \<open>This constructor gates installation on the native original body,
  complete-artifact and exact-target decisions. The returned entry and actual
  package acquire the original complete-body judgment by the proved installation
  and transport. A certified cause remains a separate mandatory witness. This
  local guard does not encode the owner's full workflow policy.\<close>

end
