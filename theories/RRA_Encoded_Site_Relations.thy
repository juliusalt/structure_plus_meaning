theory RRA_Encoded_Site_Relations
  imports RRA_Encoded_Environment_Views
begin

definition encoded_site_lookup where
  "encoded_site_lookup uc sc I u k=nested_relation_lookup I (uc u) (sc k)"

definition encoded_site_rows where
  "encoded_site_rows uc sc rows=nested_relation_store
    (map (\<lambda>((u,k),v). ((uc u,sc k),v)) rows)"

definition encoded_site_insert where
  "encoded_site_insert uc sc I u k v=nested_relation_insert (uc u) (sc k) v I"

definition encoded_site_represents where
  "encoded_site_represents uc sc I A \<longleftrightarrow>
    (\<forall>u k v. v |\<in>| encoded_site_lookup uc sc I u k \<longleftrightarrow> ((u,k),v)\<in>A)"

definition encoded_site_view where
  "encoded_site_view ud sd I=finite_optional_image (decode_encoded_binding_row ud sd)
    (nested_relation_entries I)"

context environment_key_encoding
begin

theorem site_rows_exact:
  "encoded_site_represents use_code slot_code (encoded_site_rows use_code slot_code rows) (set rows)"
  by (auto simp: encoded_site_represents_def encoded_site_rows_def encoded_site_lookup_def
    nested_relation_store_member; force)

lemma site_insert_lookup:
  "encoded_site_lookup use_code slot_code (encoded_site_insert use_code slot_code I u k v) x y=
    (if x=u \<and> y=k then finsert v (encoded_site_lookup use_code slot_code I x y)
      else encoded_site_lookup use_code slot_code I x y)"
  by (simp add: encoded_site_lookup_def encoded_site_insert_def)

theorem site_insert_exact:
  "encoded_site_represents use_code slot_code I A \<Longrightarrow>
    encoded_site_represents use_code slot_code (encoded_site_insert use_code slot_code I u k v)
      (insert ((u,k),v) A)"
  by (auto simp: encoded_site_represents_def site_insert_lookup)

end

context environment_key_codec
begin

lemma site_view_member:
  "((u,k),v) |\<in>| encoded_site_view use_decode slot_decode I \<longleftrightarrow>
    v |\<in>| encoded_site_lookup use_code slot_code I u k"
  by (auto simp: encoded_site_view_def finite_optional_image_exact binding_row_exact
    nested_relation_entries_exact encoded_site_lookup_def)

theorem site_view_exact:
  "encoded_site_represents use_code slot_code I A \<Longrightarrow>
    fset (encoded_site_view use_decode slot_decode I)=A"
  by (auto simp: encoded_site_represents_def site_view_member)

end

text \<open>
  The existing separate use and slot codecs index arbitrary relation values.
  Complete pointwise meaning, incremental insertion and whole decoded view
  reuse the original nested-store and codec contracts. Multiple values at a
  site remain distinct. The view is for complete observation; lookup and
  insertion do not enumerate it.
\<close>

end
