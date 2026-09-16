theory Factor_Development_Criterion_Sources
  imports Factor_Development_Cases Factor_Finite_Ground_Source
begin

definition development_existing_condition where
  "development_existing_condition d F u=\<lparr>condition_source=F,condition_source_use=u,
    condition_source_root=[],condition_goals=[Existing_Admission d]\<rparr>"

lemma development_existing_condition_exact:
  assumes native: "native_package_at (decode_finite_environment F) u [] P"
  shows "development_condition_holds (development_existing_condition d F u) x y \<longleftrightarrow>
    (d,Pair_Term (decode_finite_term x) (decode_finite_term y))\<in>positive_meaning P"
proof -
  have present: "finite_native_source F u []\<noteq>None"
    using native by (simp only: finite_native_source_absent; blast)
  obtain N where finite: "native_package_at (decode_finite_environment F) u [] (decode_finite_system N)"
    using present by (cases "finite_native_source F u []") (auto simp only: finite_native_source_correct)
  have same: "decode_finite_system N=P" by (rule native_package_unique[OF finite native])
  have unique: "decode_finite_system M=P"
    if "native_package_at (decode_finite_environment F) u [] (decode_finite_system M)" for M
    by (rule native_package_unique[OF that native])
  let ?t="Pair_Term (decode_finite_term x) (decode_finite_term y)"
  have representation: "development_condition_holds (development_existing_condition d F u) x y \<longleftrightarrow>
    (\<exists>M. native_package_at (decode_finite_environment F) u [] (decode_finite_system M) \<and>
      term_formed ?t \<and> (d,?t)\<in>positive_meaning (decode_finite_system M))"
    by (simp add: development_condition_holds_def development_condition_requirement_def
      workflow_requirement_holds_def development_existing_condition_def admission_requirements_hold_def)
  show ?thesis
  proof
    assume holds: "development_condition_holds (development_existing_condition d F u) x y"
    obtain M where actual: "native_package_at (decode_finite_environment F) u [] (decode_finite_system M)"
      and positive: "(d,?t)\<in>positive_meaning (decode_finite_system M)"
      using holds by (simp only: representation; blast)
    show "(d,?t)\<in>positive_meaning P" using positive by (simp only: unique[OF actual])
  next
    assume positive: "(d,?t)\<in>positive_meaning P"
    have formed: "term_formed ?t"
      using schema_call_formed_target[OF positive_meaning_formed[OF positive]] by blast
    show "development_condition_holds (development_existing_condition d F u) x y"
      unfolding representation by (rule exI[of _ N]) (use finite formed positive in \<open>simp only: same; blast\<close>)
  qed
qed

definition finite_ground_condition where
  "finite_ground_condition xs=map_option (\<lambda>(d,F,u). development_existing_condition d F u) (finite_ground_source xs)"

lemma finite_ground_condition_exact:
  assumes source: "finite_ground_condition xs=Some C"
  shows "development_condition_holds C x y \<longleftrightarrow> Finite_Pair x y\<in>set xs"
proof -
  obtain d F u where installed: "finite_ground_source xs=Some (d,F,u)"
    and condition: "C=development_existing_condition d F u"
    using source by (auto simp: finite_ground_condition_def split: option.splits prod.splits)
  obtain P where native: "native_package_at (decode_finite_environment F) u [] P"
    and exact: "\<forall>t. (d,t)\<in>positive_meaning P \<longleftrightarrow> t\<in>decode_finite_term ` set xs"
    by (rule finite_ground_source_meaning[OF installed]) blast
  show ?thesis using exact
    by (simp only: condition development_existing_condition_exact[OF native])
      (metis decode_finite_term_injective decode_finite_term.simps(3) image_iff)
qed

end
