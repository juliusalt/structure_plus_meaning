theory Factor_Finite_Site_Value_Reader_Controls
  imports Factor_Finite_Site_Value_Readers
begin

section \<open>Controls of the readers over an environment value\<close>

text \<open>
  Two environments: the empty one (@{const finite_empty_environment}), and one holding a single artifact at the
  use @{term None} whose carrier is the empty address alone, with no incidence and no data. Each reader is
  executed at a presented and at a malformed or refused term, and its presentation relation's outcome follows
  beside it from the reader's exactness: a reading states the presentation, an absent reading refuses it for
  every value. No library theory imports these controls.
\<close>

definition environment_reader_control_artifact :: finite_exact_artifact where
  "environment_reader_control_artifact=\<lparr>finite_structure=\<lparr>finite_carrier={|[]|},finite_incidence={||}\<rparr>,
    finite_data=\<lparr>finite_bag={#},finite_bindings={||}\<rparr>\<rparr>"

definition environment_reader_control_rooted :: "local_address option finite_artifact_environment" where
  "environment_reader_control_rooted=\<lparr>finite_environment_artifacts={|(None,environment_reader_control_artifact)|},
    finite_environment_bindings={||}\<rparr>"

abbreviation environment_pair_read_control_term where
  "environment_pair_read_control_term\<equiv>
    Finite_Pair (finite_environment_value finite_empty_environment) (finite_environment_value environment_reader_control_rooted)"

abbreviation environment_pair_read_control_malformed_term where
  "environment_pair_read_control_malformed_term\<equiv>
    Finite_Pair (finite_environment_value finite_empty_environment) (Finite_Payload [1])"

abbreviation source_root_read_control_term where
  "source_root_read_control_term\<equiv>
    Finite_Pair (Finite_Pair (finite_environment_value environment_reader_control_rooted) (Finite_Payload [])) (Finite_Payload [])"

abbreviation source_root_read_control_malformed_term where
  "source_root_read_control_malformed_term\<equiv>
    Finite_Pair (Finite_Pair (finite_environment_value environment_reader_control_rooted) (Finite_Payload [1])) (Finite_Payload [])"

subsection \<open>The pair of environment values\<close>

lemma environment_pair_read_control:
  "finite_environment_pair_read environment_pair_read_control_term=
    Some (finite_empty_environment,environment_reader_control_rooted)"
  by eval

lemmas environment_pair_read_control_presents=
  environment_pair_read_control[unfolded finite_environment_pair_read_exact]

lemma environment_pair_read_control_malformed:
  "finite_environment_pair_read environment_pair_read_control_malformed_term=None"
  by eval

lemma environment_pair_read_control_malformed_refused:
  "\<not>(\<exists>e f. decode_finite_term environment_pair_read_control_malformed_term=Pair_Term e f \<and>
    environment_value_presents (decode_finite_environment E) e \<and>
    environment_value_presents (decode_finite_environment F) f)"
  by (metis finite_environment_pair_read_exact environment_pair_read_control_malformed option.distinct(1))

subsection \<open>The source-root argument\<close>

lemma source_root_read_control:
  "finite_source_root_read source_root_read_control_term=Some ((environment_reader_control_rooted,None),[])"
  by eval

lemmas source_root_read_control_presents=
  source_root_read_control[unfolded finite_source_root_read_exact]

lemma source_root_read_control_malformed:
  "finite_source_root_read source_root_read_control_malformed_term=None"
  by eval

lemma source_root_read_control_malformed_refused:
  "\<not>(\<exists>e. decode_finite_term source_root_read_control_malformed_term=
      source_root_argument e (use_data_term u) (Payload_Term r) \<and>
    environment_value_presents (decode_finite_environment E) e)"
  by (metis finite_source_root_read_exact source_root_read_control_malformed option.distinct(1))

subsection \<open>The site value\<close>

text \<open>
  The site value presented at the rooted environment's one position is read back as that environment and site;
  the value presented at the address [1], outside the artifact's carrier and so no position of the environment,
  is read as nothing, and no environment and site are presented by it.
\<close>

lemma site_read_control:
  "finite_site_read (finite_site_presented environment_reader_control_rooted None [])=
    Some (environment_reader_control_rooted,None,[])"
  by eval

lemmas site_read_control_presents=site_read_control[unfolded finite_site_read_exact]

lemma site_read_control_outside:
  "finite_site_read (finite_site_presented environment_reader_control_rooted None [1])=None"
  by eval

lemma site_read_control_outside_refused:
  "\<not>site_value_presents (decode_finite_environment E) u r
    (decode_finite_term (finite_site_presented environment_reader_control_rooted None [1]))"
  by (metis finite_site_read_exact site_read_control_outside option.distinct(1))

end
