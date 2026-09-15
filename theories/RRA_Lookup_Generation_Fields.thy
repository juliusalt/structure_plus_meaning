theory RRA_Lookup_Generation_Fields
  imports RRA_Lookup_Citation_Readings
begin

definition lookup_generation_field_readings where
  "lookup_generation_field_readings artifacts bindings u r=
    ffUnion (fimage (\<lambda>C. ffUnion (fimage (\<lambda>(ps,xs).
      if length xs=4 then let lr=xs!0; pr=xs!1; payr=xs!2; cr=xs!3 in
        ffUnion (fimage (\<lambda>l. ffUnion (fimage (\<lambda>M.
          ffUnion (fimage (\<lambda>p. fimage (\<lambda>c. (l,M,p,c))
            (lookup_anchored_targets artifacts bindings u cr)) (lookup_anchored_targets artifacts bindings u payr)))
          (finite_family_candidates C pr))) (lookup_anchored_targets artifacts bindings u lr))
      else {||}) (finite_record_candidates C r 4))) (artifacts u))"

context environment_lookup_reading
begin

theorem generation_fields_exact:
  "finite_environment_formed E \<Longrightarrow>
    lookup_generation_field_readings artifacts bindings u r=finite_generation_field_readings E u r"
  by (simp only: lookup_generation_field_readings_def finite_generation_field_readings_def
    if_True artifacts_exact anchored_targets_exact)

end

text \<open>
  Formation is supplied once by the original environment contract. The actual
  field operation reads the source artifact and its bound targets through
  point lookups, and preserves the entire predecessor socket family.
\<close>

end
