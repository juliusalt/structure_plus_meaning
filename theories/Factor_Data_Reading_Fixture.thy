theory Factor_Data_Reading_Fixture
  imports Factor_Certified_Cause_Cases Finite_Uniform_Optional_Values
begin

definition data_reading_fixture where
  "data_reading_fixture seed=fimage (\<lambda>(key,result). (key,case result of
      None \<Rightarrow> None | Some (X,built) \<Rightarrow>
        map_option (\<lambda>(E,u,G,J,C). C) built))
    (certified_cause_seed_family seed 0)"

definition data_reading_fixture_source where
  "data_reading_fixture_source rows=finite_uniform_optional_value rows"

lemma data_reading_fixture_source_exact:
  "data_reading_fixture_source (data_reading_fixture seed)=Some C \<longleftrightarrow>
    fimage snd (data_reading_fixture seed)={|Some C|}"
  by (simp only: data_reading_fixture_source_def finite_uniform_optional_value_exact)

definition data_reading_fixture_packet where
  "data_reading_fixture_packet=(let rows=data_reading_fixture literal_replay_seed in
    (rows,data_reading_fixture_source rows))"

text \<open>
  The complete native replay and joined generation constructor produce the
  fixture's cause. Every original certificate key and failed constructor
  position is retained. A source is available only when all positions produce
  the same complete cause; no host artifact or expected reading supplies it.
\<close>

end
