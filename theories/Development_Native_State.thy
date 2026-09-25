theory Development_Native_State
  imports Development_Given_Installation Development_Owner_Records Finite_Presented_Coordinates
begin

section \<open>The given as one site value\<close>

text \<open>
  The given of the native loop's first problem (DECISIONS.md "The native loop's first problem is what a problem
  is", the row "the state the answer extends") is the program entry the given's installation returns: its
  environment, holding the development package and the readers the guard and a request call, and its package
  site (\<open>given_package\<close>). It is stated once, as the complete data of that site value: the environment's
  complete value beside the site's data. Nothing is added to the environment or to the site, and no entry
  coordinate is stated. The given's environment is not closed at its site (\<open>given_environment_not_closed\<close>), so
  package retention is refused of this value (\<open>given_retention_refused\<close>): the value presents the given as it
  stands, not its least scope.
\<close>

definition development_given_value :: finite_factor_term where
  "development_given_value=Finite_Pair (finite_environment_value given_environment) (finite_site_data (given_use,[]))"

theorem development_given_value_presents:
  "site_value_presents (decode_finite_environment given_environment) given_use [] (decode_finite_term development_given_value)"
proof -
  have formed: "finite_environment_formed given_environment"
    using given_package(3) by (simp only: finite_environment_formed_correct)
  have environment: "environment_value_presents (decode_finite_environment given_environment)
      (decode_finite_term (finite_environment_value given_environment))"
    using formed by (simp only: finite_environment_value_exact simp_thms)
  show ?thesis unfolding site_value_presents_def development_given_value_def
    using native_package_site_position[OF given_package(1)] environment by simp
qed

text \<open>The value recovers exactly the given's environment and site, and is formed and self-contained.\<close>

corollary development_given_value_recovers:
  assumes "site_value_presents F v s (decode_finite_term development_given_value)"
  shows "F=decode_finite_environment given_environment \<and> v=given_use \<and> s=[]"
  using site_value_presents_unique[OF assms development_given_value_presents] .

corollary development_given_value_formed:
  "environment_formed (decode_finite_environment given_environment) \<and>
    term_formed (decode_finite_term development_given_value) \<and> self_contained_term (decode_finite_term development_given_value)"
  by (rule site_value_presents_formed[OF development_given_value_presents])

section \<open>The native state's first generation\<close>

text \<open>
  The native state's first generation is a base generation recorded in the empty environment at the index of
  its own payload, the given's value: the indexed generation (\<open>development_indexed_generation\<close>), read by nothing
  but a snapshot's lookup. Recording it at the empty environment with no predecessor is the owner records'
  construction, so its contract is that construction's instance (\<open>development_owner_record_certified\<close>). Choosing
  the given as the state's first payload is made outside the loop, a residual; a later publication supersedes it.
\<close>

definition development_native_state_first_generation ::
    "(local_address option finite_artifact_environment\<times>local_address option\<times>finite_generation) option" where
  "development_native_state_first_generation=
     development_indexed_generation development_given_value (finite_enumerated_environment [] []) []"

lemmas development_native_state_first_generation_certified=
  development_owner_record_certified[of development_given_value, unfolded development_owner_record_def,
    folded development_native_state_first_generation_def]

lemmas development_native_state_first_generation_recorded=
  development_indexed_generation_recorded[of development_given_value "finite_enumerated_environment [] []" "[]",
    folded development_native_state_first_generation_def]

end
