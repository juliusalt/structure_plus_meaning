theory Observation_Revisions
  imports Observation_Repairs
begin

section \<open>Revision retains sound selections and explains every withdrawal\<close>

definition retained_observation_facets where
  "retained_observation_facets C relation U F observe=
    F\<inter>sound_observation_facets C relation U observe"

definition withdrawn_observation_facets where
  "withdrawn_observation_facets C relation U F observe=
    F-sound_observation_facets C relation U observe"

lemma retained_observation_facets_available:
  "retained_observation_facets C relation U F observe\<subseteq>U"
  by (auto simp: retained_observation_facets_def)

lemma retained_observation_facets_sound:
  "comparison_observations_sound C relation
    (retained_observation_facets C relation U F observe) observe"
  by (rule comparison_sound_restriction[OF sound_observation_facets_sound])
    (auto simp: retained_observation_facets_def)

theorem withdrawal_has_an_actual_conflict:
  assumes "F\<subseteq>U"
  shows "f\<in>withdrawn_observation_facets C relation U F observe \<longleftrightarrow>
    (\<exists>c d w. (c,d,f,w)\<in>observation_conflicts C relation F observe)"
  using assms by (auto simp: withdrawn_observation_facets_def observation_conflicts_def; blast)

theorem every_available_basis_excludes_the_withdrawals:
  assumes available: "G\<subseteq>U" and basis: "comparison_basis C relation G observe"
  shows "withdrawn_observation_facets C relation U F observe\<inter>G={}"
proof -
  have sound: "comparison_observations_sound C relation G observe"
    using basis by (simp only: comparison_basis_exact)
  have "G\<subseteq>sound_observation_facets C relation U observe"
    using sound by (simp only: sound_selection_uses_only_sound_facets[OF available])
  then show ?thesis by (auto simp: withdrawn_observation_facets_def)
qed

section \<open>Repair witnesses are recomputed after the necessary withdrawals\<close>

definition revised_observation_selection where
  "revised_observation_selection C relation U F observe=
    reported_observation_extension (retained_observation_facets C relation U F observe)
      (available_observation_repairs C relation U
        (retained_observation_facets C relation U F observe) observe)"

lemma revised_observation_selection_bounds:
  "retained_observation_facets C relation U F observe\<subseteq>
    revised_observation_selection C relation U F observe"
  "revised_observation_selection C relation U F observe\<subseteq>
    sound_observation_facets C relation U observe"
  by (auto simp: revised_observation_selection_def reported_observation_extension_def
    retained_observation_facets_def available_observation_repairs_def)

theorem revised_observation_selection_sound:
  "comparison_observations_sound C relation
    (revised_observation_selection C relation U F observe) observe"
  by (rule comparison_sound_restriction[OF sound_observation_facets_sound
    revised_observation_selection_bounds(2)])

theorem revision_withdraws_exactly_the_unsound_selections:
  "F-revised_observation_selection C relation U F observe=
    withdrawn_observation_facets C relation U F observe"
  using revised_observation_selection_bounds[of C relation U F observe]
  by (auto simp: retained_observation_facets_def withdrawn_observation_facets_def)

theorem every_added_facet_has_a_recomputed_repair:
  "f\<in>revised_observation_selection C relation U F observe-F \<longleftrightarrow>
    f\<notin>F \<and> (\<exists>c d w. (c,d,f,w)\<in>available_observation_repairs C relation U
      (retained_observation_facets C relation U F observe) observe)"
  by (auto simp: revised_observation_selection_def reported_observation_extension_def
    retained_observation_facets_def)

theorem revision_has_exactly_the_full_sound_language_failures:
  "comparison_failures C relation (revised_observation_selection C relation U F observe) observe=
    comparison_failures C relation (sound_observation_facets C relation U observe) observe"
proof (rule subset_antisym)
  let ?K="retained_observation_facets C relation U F observe"
  let ?G="revised_observation_selection C relation U F observe"
  let ?A="sound_observation_facets C relation U observe"
  show "comparison_failures C relation ?G observe\<subseteq>comparison_failures C relation ?A observe"
  proof
    fix pair assume member: "pair\<in>comparison_failures C relation ?G observe"
    obtain c d where pair: "pair=(c,d)" by (cases pair)
    have earlier: "(c,d)\<in>comparison_failures C relation ?K observe"
      using subsetD[OF comparison_failures_antimono[OF revised_observation_selection_bounds(1)] member]
      by (simp only: pair)
    have absent: "\<nexists>f w. (c,d,f,w)\<in>available_observation_repairs C relation U ?K observe"
    proof
      assume "\<exists>f w. (c,d,f,w)\<in>available_observation_repairs C relation U ?K observe"
      then obtain f w where repair: "(c,d,f,w)\<in>available_observation_repairs C relation U ?K observe"
        by blast
      have inside: "f\<in>?G"
        using repair by (auto simp: revised_observation_selection_def reported_observation_extension_def)
      have first: "w\<in>observe f c" and second: "w\<notin>observe f d"
        using repair by (auto simp: available_observation_repairs_def)
      show False using member pair inside first second
        by (auto simp: comparison_failures_def candidate_profile_comparison)
    qed
    show "pair\<in>comparison_failures C relation ?A observe"
      using a_missing_pair_has_no_available_repair_exactly_when_the_language_misses_it[OF earlier]
        absent by (simp only: pair; blast)
  qed
  show "comparison_failures C relation ?A observe\<subseteq>comparison_failures C relation ?G observe"
    by (rule comparison_failures_antimono[OF revised_observation_selection_bounds(2)])
qed

theorem revision_is_adequate_exactly_when_the_sound_language_is_adequate:
  "comparison_basis C relation (revised_observation_selection C relation U F observe) observe \<longleftrightarrow>
    comparison_failures C relation (sound_observation_facets C relation U observe) observe={}"
  by (simp only: comparison_basis_exact revised_observation_selection_sound
    revision_has_exactly_the_full_sound_language_failures simp_thms)

theorem revision_is_adequate_exactly_when_an_available_basis_exists:
  "comparison_basis C relation (revised_observation_selection C relation U F observe) observe \<longleftrightarrow>
    (\<exists>G. G\<subseteq>U \<and> comparison_basis C relation G observe)"
proof -
  have empty: "observation_conflicts C relation {} observe={}"
    by (auto simp: observation_conflicts_def)
  have available: "{}\<subseteq>U" by simp
  show ?thesis using available_basis_extension_exact[OF available, of C relation observe]
    by (simp only: empty empty_subsetI simp_thms
      revision_is_adequate_exactly_when_the_sound_language_is_adequate)
qed

text \<open>
  The original extension operation preserves all selected facets. Revision is
  a separate candidate transition: it keeps every selected sound facet, removes
  exactly the selected facets outside the sound available language, and adds
  every facet with an actual repair witness after that removal. A removed
  unsound facet may previously have separated a missing comparison, so its
  removal can expose a new repair obligation.

  The result is sound and has exactly the failures of the full sound available
  language, even when that language has no adequate basis. Selected redundant
  sound facets remain selected. Alternative repair facets are all retained;
  this construction asserts neither minimality nor uniqueness. Actual conflict
  explanations for every withdrawal require the original selection to be
  available. Whole input admission remains a separate prerequisite for use.
\<close>

end
