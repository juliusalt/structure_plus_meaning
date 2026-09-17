theory RRA_Structural_Generation_Checking
  imports Structural_Generation_Identity Structural_Word_Collections RRA_Lookup_Generation_Checking
begin

lemma structural_generation_code_inj:
  "inj structural_generation_code"
  by (auto simp: inj_def structural_generation_code_injective)

lemma structural_generation_bijection:
  "finite_bijective_relation A (fimage structural_generation_code P)
    (fimage (map_prod id structural_generation_code) R)=finite_bijective_relation A P R"
  by (rule finite_bijective_relation_value_map[OF structural_generation_code_inj])

lemma structural_generation_distinct:
  "distinct (map structural_generation_code rows)=distinct rows"
  by (rule structural_distinct_map[OF structural_generation_code_injective])

declare lookup_check_generation.simps[code del]

lemma lookup_check_generation_structural_code [code]:
  "lookup_check_generation (Generation l P p c) artifacts bindings u r=
    fBex (lookup_generation_field_readings artifacts bindings u r) (\<lambda>(l',M,p',c').
      structural_target_code l=structural_target_code l' \<and>
      structural_target_code p=structural_target_code p' \<and>
      structural_target_code c=structural_target_code c' \<and>
      finite_bijective_relation (fimage fst M) (fimage structural_generation_code P)
        (fimage (map_prod id structural_generation_code)
          (lookup_generation_child_rows (lookup_located_values artifacts bindings) u M
            (fimage (\<lambda>H. (H,lookup_check_generation H artifacts bindings)) P))))"
  by (simp only: structural_target_code_injective structural_generation_bijection lookup_check_generation.simps)

declare finite_check_generation.simps[code del]

lemma finite_check_generation_structural_code [code]:
  "finite_check_generation (Generation l P p c) E u r=
    fBex (finite_generation_field_readings E u r) (\<lambda>(l',M,p',c').
      structural_target_code l=structural_target_code l' \<and>
      structural_target_code p=structural_target_code p' \<and>
      structural_target_code c=structural_target_code c' \<and>
      finite_bijective_relation (fimage fst M) (fimage structural_generation_code P)
        (fimage (map_prod id structural_generation_code)
          (finite_generation_child_rows E u M (fimage (\<lambda>H. (H,finite_check_generation H)) P))))"
  by (simp only: structural_target_code_injective structural_generation_bijection finite_check_generation.simps)

declare lookup_generation_record_ready_def[code del]

lemma lookup_generation_record_ready_structural_code [code]:
  "lookup_generation_record_ready artifacts bindings l p c rows=
    (finite_target_formed l \<and> finite_target_formed p \<and> finite_target_formed c \<and>
      distinct (map structural_generation_code (map snd rows)) \<and> list_all (\<lambda>(d,G).
        lookup_check_generation G artifacts bindings (fst d) (snd d)) rows)"
  by (simp only: structural_generation_distinct lookup_generation_record_ready_def)

declare finite_generation_record_ready_def[code del]

lemma finite_generation_record_ready_structural_code [code]:
  "finite_generation_record_ready E l p c rows=(finite_environment_formed E \<and>
    finite_target_formed l \<and> finite_target_formed p \<and> finite_target_formed c \<and>
    distinct (map structural_generation_code (map snd rows)) \<and> list_all (\<lambda>(d,G).
      finite_check_generation G E (fst d) (snd d)) rows)"
  by (simp only: structural_generation_distinct finite_generation_record_ready_def)

text \<open>
  Exact value-map and distinctness equations compare complete generation words
  inside the original predecessor bijection and readiness operations. Original
  field reading, recursive predecessor checking and every original guard stay
  explicit in the executable equations. Injectivity establishes these equations
  for every input. It supplies no physical cost bound or new semantic reading.
\<close>

end
