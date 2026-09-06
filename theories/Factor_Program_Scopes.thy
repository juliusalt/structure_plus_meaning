theory Factor_Program_Scopes
  imports Factor_Site_Values Factor_Native_Meaning
begin

section \<open>An exact program scope includes its complete dependency environment\<close>

lemma native_package_closed_environment_fixed:
  assumes closed: "closed_native_package_at E u r P"
  shows "native_package_environment E u r=E"
proof -
  have package: "native_package_at E u r P" and boundary: "environment_closed E {u} (native_package_demands E u r)"
    using closed by (auto simp: closed_native_package_at_def)
  show ?thesis unfolding native_package_environment_def
    by (rule read_environment_closed_fixed[OF native_package_read_boundary[OF package] boundary])
       (simp add: native_package_sources_def)
qed

lemma native_package_root_position:
  assumes package: "native_package_at E u r P"
  shows "(u,r)\<in>environment_positions E"
proof -
  obtain Q R M where source: "artifact_at E u R" "family_at R r M"
    using package by (auto simp: native_package_at_def native_root_family_at_def)
  have root: "r\<in>rra_carrier (object_structure R)" using source(2) by (simp add: family_at_def)
  show ?thesis using source(1) root by auto
qed

lemma native_package_entry_position:
  assumes package: "native_package_at E u r P" and member: "d\<in>system_definitions P"
  shows "d\<in>environment_positions E"
proof -
  have formed: "native_package_formed E (native_package_roots E u r)"
    by (rule native_package_projection(1)[OF package])
  have site: "d\<in>native_definition_sites E (native_package_roots E u r)"
    using member native_package_projection(3)[OF package] by (simp add: native_package_sites_def)
  show ?thesis using native_package_sites(1)[OF formed] site by blast
qed

definition program_scope_quoted_at ::
  "exact_artifact \<Rightarrow> local_address \<Rightarrow> local_address option artifact_environment \<Rightarrow>
    local_address option \<Rightarrow> local_address \<Rightarrow> local_address option native_system \<Rightarrow> bool" where
  "program_scope_quoted_at C q E u r P \<longleftrightarrow>
    site_value_quoted_at C q E u r \<and> closed_native_package_at E u r P"

theorem program_scope_quoted_unique:
  assumes first: "program_scope_quoted_at C q E u r P" and second: "program_scope_quoted_at C q F v s Q"
  shows "E=F \<and> u=v \<and> r=s \<and> P=Q"
proof -
  have left: "site_value_quoted_at C q E u r" "native_package_at E u r P"
    using first by (auto simp: program_scope_quoted_at_def closed_native_package_at_def)
  have right: "site_value_quoted_at C q F v s" "native_package_at F v s Q"
    using second by (auto simp: program_scope_quoted_at_def closed_native_package_at_def)
  have scope: "E=F \<and> u=v \<and> r=s" by (rule site_value_quoted_unique[OF left(1) right(1)])
  have other: "native_package_at E u r Q" using right(2) scope by simp
  have program: "P=Q" by (rule native_package_unique[OF left(2) other])
  show ?thesis using scope program by blast
qed

lemma program_scope_is_minimal:
  assumes "program_scope_quoted_at C q E u r P"
  shows "native_package_environment E u r=E"
  using assms unfolding program_scope_quoted_at_def by (meson native_package_closed_environment_fixed)

theorem program_scope_whole_unique:
  assumes first: "program_scope_quoted_at C q E u r P"
    and second: "program_scope_quoted_at C s F v a Q"
  shows "q=s \<and> E=F \<and> u=v \<and> r=a \<and> P=Q"
proof -
  obtain t where left: "complete_data_quoted_at C q t"
    using first unfolding program_scope_quoted_at_def site_value_quoted_at_def by blast
  obtain x where right: "complete_data_quoted_at C s x"
    using second unfolding program_scope_quoted_at_def site_value_quoted_at_def by blast
  have roots: "q=s" using complete_data_quotation_whole_unique[OF left right] by blast
  have other: "program_scope_quoted_at C q F v a Q" using second roots by simp
  show ?thesis using roots program_scope_quoted_unique[OF first other] by blast
qed

lemma program_scope_quoted_formed:
  assumes quote: "program_scope_quoted_at C q E u r P"
  shows "exact_formed C \<and> environment_formed E \<and> schema_system_formed P \<and> (u,r)\<in>environment_positions E"
proof -
  have data: "site_value_quoted_at C q E u r" and package: "native_package_at E u r P"
    using quote by (auto simp: program_scope_quoted_at_def closed_native_package_at_def)
  show ?thesis using site_value_quoted_formed[OF data] native_package_system_formed[OF package] by blast
qed

theorem program_scope_quoted_total:
  fixes E :: "local_address option artifact_environment"
  assumes package: "native_package_at E u r P"
  shows "\<exists>C. exact_formed C \<and> program_scope_quoted_at C [] (native_package_environment E u r) u r P"
proof -
  let ?F="native_package_environment E u r"
  have closed: "closed_native_package_at ?F u r P" by (rule native_package_closed_restriction[OF package])
  have kept: "native_package_at ?F u r P" using closed by (simp add: closed_native_package_at_def)
  have formed: "environment_formed ?F" by (rule native_package_environment_formed[OF package])
  have site: "(u,r)\<in>environment_positions ?F" by (rule native_package_root_position[OF kept])
  obtain C where quote: "exact_formed C" "site_value_quoted_at C [] ?F u r"
    using site_value_quoted_total[OF formed site] by blast
  show ?thesis using quote closed unfolding program_scope_quoted_at_def by blast
qed

theorem program_scope_quoted_in_environment:
  assumes quote: "program_scope_quoted_at C q E u r P"
    and formed: "environment_formed F" and source: "artifact_at F v C"
  shows "\<exists>t. site_value_presents E u r t \<and>
    term_quoted_at F v q t (rra_carrier (object_structure C)) {}"
  using quote unfolding program_scope_quoted_at_def
  by (meson site_value_quoted_in_environment[OF _ formed source])

theorem program_scope_future_application:
  assumes quote: "program_scope_quoted_at C q E pu pr P" and formed: "environment_formed F"
    and included: "environment_included E F" and app: "native_application_at F au ar d t I K"
  shows "native_package_at F pu pr P"
    and "native_package_environment F pu pr=E"
    and "native_application_formed F pu pr au ar\<longleftrightarrow>schema_call_formed P d t"
    and "native_positive_holds F pu pr au ar\<longleftrightarrow>(d,t)\<in>positive_meaning P"
proof -
  have package: "native_package_at E pu pr P"
    using quote by (simp add: program_scope_quoted_at_def closed_native_package_at_def)
  have copied: "native_package_at F pu pr P" by (rule native_package_included[OF package included formed])
  show "native_package_at F pu pr P" by (rule copied)
  show "native_package_environment F pu pr=E"
    using native_package_environment_extension[OF package included formed] program_scope_is_minimal[OF quote] by simp
  show "native_application_formed F pu pr au ar\<longleftrightarrow>schema_call_formed P d t"
    by (rule native_application_formed_with_reads[OF copied app])
  show "native_positive_holds F pu pr au ar\<longleftrightarrow>(d,t)\<in>positive_meaning P"
    by (rule native_positive_holds_with_reads[OF copied app])
qed

text \<open>
  The record stores a complete finite environment and its actual program site.
  The native reader derives the program; no second program value is stored.
  Closure entails that this environment is exactly its minimal program scope.
  Every actual package has such a finite quotation, including an empty program.

  Equal quotation targets recover the identical environment, site, and program.
  A formed extension retaining that scope preserves its native program and the
  formation and truth of every actual future application. Ordinary arguments
  may lie outside the recorded program. Quoting a scope does not select it as
  an authority or establish a foundation transition.
\<close>

end
