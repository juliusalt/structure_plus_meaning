theory Factor_Finite_Site_Value_Readers
  imports Finite_Presentation_Readers Factor_Finite_Environment_Value_Readers Factor_Executable_Environment_Values_Base
    Factor_Site_Values Factor_Schema_Admission RRA_Finite_Environment_Positions
begin

section \<open>Three argument shapes over an environment value\<close>

text \<open>
  A pair of environment values, each component read by the environment value reader; an environment value
  beside a use's data term; and a source-root argument, that pair beside an address payload. Each reader is
  the pair reader of its components' readers (@{thm [source] finite_pair_read_present}), and so exact at
  every term to the presentation relation of its shape. The readers decide no entry: they read presentations.
\<close>

definition finite_environment_pair_read :: "finite_factor_term \<Rightarrow>
    (local_address option finite_artifact_environment\<times>local_address option finite_artifact_environment) option" where
  "finite_environment_pair_read=finite_pair_read finite_environment_value_read finite_environment_value_read"

theorem finite_environment_pair_read_exact:
  "finite_environment_pair_read t=Some (E,F) \<longleftrightarrow> (\<exists>e f. decode_finite_term t=Pair_Term e f \<and>
    environment_value_presents (decode_finite_environment E) e \<and>
    environment_value_presents (decode_finite_environment F) f)"
  unfolding finite_environment_pair_read_def
  by (rule finite_pair_read_present[where P="\<lambda>E e. environment_value_presents (decode_finite_environment E) e"
    and Q="\<lambda>E e. environment_value_presents (decode_finite_environment E) e",
    OF finite_environment_value_read_exact finite_environment_value_read_exact])

lemma finite_environment_use_read_exact:
  "finite_pair_read finite_environment_value_read finite_use_value_read v=Some z \<longleftrightarrow>
    (\<exists>e. decode_finite_term v=Pair_Term e (use_data_term (snd z)) \<and>
      environment_value_presents (decode_finite_environment (fst z)) e)"
proof -
  obtain F w where z: "z=(F,w)" by (cases z)
  show ?thesis
    by (auto simp: z finite_pair_read_present[where P="\<lambda>E e. environment_value_presents (decode_finite_environment E) e"
      and Q="\<lambda>u w. w=use_data_term u", OF finite_environment_value_read_exact finite_use_value_read_exact])
qed

definition finite_source_root_read :: "finite_factor_term \<Rightarrow>
    ((local_address option finite_artifact_environment\<times>local_address option)\<times>local_address) option" where
  "finite_source_root_read=
    finite_pair_read (finite_pair_read finite_environment_value_read finite_use_value_read) finite_payload_value_read"

theorem finite_source_root_read_exact:
  "finite_source_root_read t=Some ((E,u),r) \<longleftrightarrow> (\<exists>e.
    decode_finite_term t=source_root_argument e (use_data_term u) (Payload_Term r) \<and>
    environment_value_presents (decode_finite_environment E) e)"
  by (auto simp: finite_source_root_read_def finite_pair_read_present[where
    P="\<lambda>z v. \<exists>e. v=Pair_Term e (use_data_term (snd z)) \<and>
      environment_value_presents (decode_finite_environment (fst z)) e"
    and Q="\<lambda>r w. w=Payload_Term r", OF finite_environment_use_read_exact finite_payload_value_read_exact])

section \<open>A site value, read back and presented\<close>

text \<open>
  A site value is an environment value beside a site's data term, the site a position of the environment
  (@{const site_value_presents}). Its reader reads the environment and the site by their own readers, as a pair
  (@{thm [source] finite_pair_read_present}), and keeps the reading only when the site is a position of the
  environment read; every other term is read as nothing. A site value has one presentation for every enumeration
  of its environment's tables, so the reader is exact in the relational form of @{const finite_reads}: a term is
  read as an environment, a use and an address exactly when it presents them.
\<close>

definition finite_site_read :: "finite_factor_term \<Rightarrow>
    (local_address option finite_artifact_environment\<times>local_address option\<times>local_address) option" where
  "finite_site_read t=(case finite_pair_read finite_environment_value_read finite_site_value_read t of
    None \<Rightarrow> None
  | Some (E,u,r) \<Rightarrow> if (u,r) |\<in>| finite_environment_positions E then Some (E,u,r) else None)"

theorem finite_site_read_exact:
  "finite_site_read t=Some (E,u,r) \<longleftrightarrow>
    site_value_presents (decode_finite_environment E) u r (decode_finite_term t)"
proof -
  have site: "finite_site_value_read v=Some y \<longleftrightarrow> decode_finite_term v=site_data_term (fst y) (snd y)" for v y
    by (cases y) (simp only: finite_site_value_read_exact fst_conv snd_conv)
  have pair: "finite_pair_read finite_environment_value_read finite_site_value_read t=Some (E,(u,r)) \<longleftrightarrow>
      (\<exists>e q. decode_finite_term t=Pair_Term e q \<and> environment_value_presents (decode_finite_environment E) e \<and>
        q=site_data_term u r)"
    using finite_pair_read_present[where P="\<lambda>E e. environment_value_presents (decode_finite_environment E) e"
      and Q="\<lambda>y q. q=site_data_term (fst y) (snd y)", OF finite_environment_value_read_exact site, of t E "(u,r)"]
    by simp
  have "finite_site_read t=Some (E,u,r) \<longleftrightarrow>
      finite_pair_read finite_environment_value_read finite_site_value_read t=Some (E,(u,r)) \<and>
      (u,r) |\<in>| finite_environment_positions E"
    by (auto simp: finite_site_read_def split: option.splits prod.splits if_splits)
  then show ?thesis
    by (auto simp: pair site_value_presents_def finite_environment_positions_correct[symmetric])
qed

text \<open>
  The presenter of a site value: the environment's complete value beside the site's data. At a formed
  environment and one of its positions it presents that site value, and the reader reads it back as exactly the
  environment and the site it presents.
\<close>

definition finite_site_presented :: "local_address option finite_artifact_environment \<Rightarrow> local_address option \<Rightarrow>
    local_address \<Rightarrow> finite_factor_term" where
  "finite_site_presented E u r=Finite_Pair (finite_environment_value E) (finite_site_data (u,r))"

theorem finite_site_presented_presents:
  assumes formed: "environment_formed (decode_finite_environment E)"
    and site: "(u,r)\<in>environment_positions (decode_finite_environment E)"
  shows "site_value_presents (decode_finite_environment E) u r (decode_finite_term (finite_site_presented E u r))"
proof -
  have environment: "environment_value_presents (decode_finite_environment E) (decode_finite_term (finite_environment_value E))"
    using formed by (simp only: finite_environment_value_exact finite_environment_formed_correct simp_thms)
  show ?thesis unfolding site_value_presents_def finite_site_presented_def using site environment by simp
qed

corollary finite_site_presented_read:
  assumes "environment_formed (decode_finite_environment E)" "(u,r)\<in>environment_positions (decode_finite_environment E)"
  shows "finite_site_read (finite_site_presented E u r)=Some (E,u,r)"
  by (simp only: finite_site_read_exact finite_site_presented_presents[OF assms])

end
