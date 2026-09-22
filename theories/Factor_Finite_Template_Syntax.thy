theory Factor_Finite_Template_Syntax
  imports Factor_Finite_Pattern_Syntax Factor_Finite_Reference_Forests Factor_Executable_Premises Factor_Schema_Bodies
    Factor_Finite_Citation_Syntax
begin

section \<open>Complete finite pattern records reuse the original child placement\<close>

text \<open>
  The executable forest places each body where the forest places it, at its branch with its
  binders fixed, so its carrier holds exactly the slots of its table. It is the executable placed
  forest over that family, and reads each child through the placed forest's code equation.
\<close>

definition finite_bound_forest :: "finite_exact_artifact list \<Rightarrow> finite_exact_artifact" where
  "finite_bound_forest Rs=finite_placed_forest bound_branch Rs"

lemma decode_finite_bound_forest [simp]:
  "decode_finite_object (finite_bound_forest Rs)=bound_forest (map decode_finite_object Rs)"
  by (simp add: finite_bound_forest_def bound_forest_def)

definition finite_pattern_forest_syntax :: "('a\<Rightarrow>local_address) \<Rightarrow> 'a finite_term_pattern list \<Rightarrow> finite_exact_artifact" where
  "finite_pattern_forest_syntax f ps=finite_bound_forest (map (finite_pattern_syntax f) ps)"

lemma decode_finite_pattern_forest_syntax [simp]:
  "decode_finite_object (finite_pattern_forest_syntax f ps)=pattern_forest_syntax f (map decode_finite_pattern ps)"
  by (simp add: finite_pattern_forest_syntax_def pattern_forest_syntax_def comp_def)

definition finite_pattern_forest_bindings :: "'a finite_term_pattern list \<Rightarrow> (local_address\<times>finite_exact_artifact) fset" where
  "finite_pattern_forest_bindings ps=finite_placed_table syntax_branch (map finite_pattern_literal_bindings ps)"

lemma finite_pattern_forest_bindings_exact:
  "map_relation_values decode_finite_object (fset (finite_pattern_forest_bindings ps))=
    pattern_forest_bindings (map decode_finite_pattern ps)"
  by (simp add: finite_pattern_forest_bindings_def pattern_forest_bindings_def placed_table_values comp_def
    finite_pattern_literal_bindings_exact)

definition finite_pattern_record_syntax :: "('a\<Rightarrow>local_address) \<Rightarrow> 'a finite_term_pattern list \<Rightarrow> finite_exact_artifact" where
  "finite_pattern_record_syntax f ps=finite_record_wrapper (finite_pattern_forest_syntax f ps) []
    (syntax_record_ports (length ps)) (pattern_forest_roots ps)"

lemma decode_finite_pattern_record_syntax [simp]:
  "decode_finite_object (finite_pattern_record_syntax f ps)=pattern_record_syntax f (map decode_finite_pattern ps)"
  by (simp add: finite_pattern_record_syntax_def pattern_record_syntax_def)

definition finite_material_syntax :: "('a\<Rightarrow>local_address) \<Rightarrow> 'a finite_material_pattern \<Rightarrow> finite_exact_artifact" where
  "finite_material_syntax f M=finite_pattern_record_syntax f (finite_material_fields M)"

lemma decode_finite_material_syntax [simp]:
  "decode_finite_object (finite_material_syntax f M)=material_syntax f (decode_finite_material M)"
  by (simp add: finite_material_syntax_def material_syntax_def finite_material_fields_correct)

definition finite_prospective_syntax :: "('a\<Rightarrow>local_address) \<Rightarrow> local_address \<Rightarrow>
    'a finite_term_pattern \<Rightarrow> finite_exact_artifact" where
  "finite_prospective_syntax f a p=finite_bound_pair_syntax (finite_external_occurrence_syntax a) (finite_pattern_syntax f p)"

lemma decode_finite_prospective_syntax [simp]:
  "decode_finite_object (finite_prospective_syntax f a p)=prospective_syntax f a (decode_finite_pattern p)"
  by (simp add: finite_prospective_syntax_def prospective_syntax_def)

section \<open>Both premise kinds retain their complete variables and references\<close>

fun finite_template_syntax :: "('a\<Rightarrow>local_address) \<Rightarrow> ('a,'u) finite_premise_template \<Rightarrow> finite_exact_artifact" where
  "finite_template_syntax f (Inl (d,p))=finite_prospective_syntax f (snd d) p"
| "finite_template_syntax f (Inr M)=finite_material_syntax f M"

lemma decode_finite_template_syntax [simp]:
  "decode_finite_object (finite_template_syntax f t)=template_syntax f (decode_finite_native_premise t)"
  by (cases t) (auto simp: decode_finite_call_pattern_def split: prod.splits)

fun finite_template_variables :: "('a,'u) finite_premise_template \<Rightarrow> 'a fset" where
  "finite_template_variables (Inl (d,p))=finite_pattern_variables p"
| "finite_template_variables (Inr M)=finite_material_variables M"

lemma finite_template_variables_exact [simp]:
  "fset (finite_template_variables t)=template_variables (decode_finite_native_premise t)"
  by (cases t) (auto simp: decode_finite_call_pattern_def finite_pattern_variables_correct
    finite_material_variables_correct split: prod.splits)

fun finite_template_formed :: "('a,'u) finite_premise_template \<Rightarrow> bool" where
  "finite_template_formed (Inl (d,p))=(octets_formed (snd d) \<and> finite_pattern_formed p)"
| "finite_template_formed (Inr M)=finite_material_formed M"

lemma finite_template_formed_exact [simp]:
  "finite_template_formed t \<longleftrightarrow> template_formed (decode_finite_native_premise t)"
  by (cases t) (auto simp: decode_finite_call_pattern_def finite_pattern_formed_correct
    finite_material_formed_correct split: prod.splits)

fun finite_template_literals :: "('a,'u) finite_premise_template \<Rightarrow> (local_address\<times>finite_exact_artifact) fset" where
  "finite_template_literals (Inl (d,p))=finite_slot_keys (Cons 3) (finite_pattern_literal_bindings p)"
| "finite_template_literals (Inr M)=finite_pattern_forest_bindings (finite_material_fields M)"

lemma finite_template_literals_exact [simp]:
  "map_relation_values decode_finite_object (fset (finite_template_literals t))=template_literals (decode_finite_native_premise t)"
  by (cases t) (auto simp: decode_finite_call_pattern_def finite_slot_keys_values
    finite_pattern_literal_bindings_exact finite_pattern_forest_bindings_exact finite_material_fields_correct split: prod.splits)

fun finite_template_callees :: "('a,'u) finite_premise_template \<Rightarrow> (local_address\<times>'u definition_site) fset" where
  "finite_template_callees (Inl (d,p))={|([2,4],d)|}"
| "finite_template_callees (Inr M)={||}"

lemma finite_template_callees_exact [simp]:
  "fset (finite_template_callees t)=template_callees (decode_finite_native_premise t)"
  by (cases t) (auto simp: decode_finite_call_pattern_def split: prod.splits)

text \<open>
  The executable premise forest and its tables place each premise as the premise forest does: its
  syntax through the executable bound forest, its literal and callee tables through the executable
  placed table at the forest's branch.
\<close>

definition finite_premise_forest_syntax :: "('a\<Rightarrow>local_address) \<Rightarrow> ('a,'u) finite_premise_template list \<Rightarrow> finite_exact_artifact" where
  "finite_premise_forest_syntax f ts=finite_bound_forest (map (finite_template_syntax f) ts)"

lemma decode_finite_premise_forest_syntax [simp]:
  "decode_finite_object (finite_premise_forest_syntax f ts)=premise_forest_syntax f (map decode_finite_native_premise ts)"
  by (simp add: finite_premise_forest_syntax_def premise_forest_syntax_def comp_def)

definition finite_premise_forest_literals :: "('a,'u) finite_premise_template list \<Rightarrow> (local_address\<times>finite_exact_artifact) fset" where
  "finite_premise_forest_literals ts=finite_placed_table syntax_branch (map finite_template_literals ts)"

lemma finite_premise_forest_literals_exact [simp]:
  "map_relation_values decode_finite_object (fset (finite_premise_forest_literals ts))=
    premise_forest_literals (map decode_finite_native_premise ts)"
  by (simp add: finite_premise_forest_literals_def premise_forest_literals_def placed_table_values comp_def)

definition finite_premise_forest_callees :: "('a,'u) finite_premise_template list \<Rightarrow> (local_address\<times>'u definition_site) fset" where
  "finite_premise_forest_callees ts=finite_placed_table syntax_branch (map finite_template_callees ts)"

lemma finite_premise_forest_callees_exact [simp]:
  "fset (finite_premise_forest_callees ts)=premise_forest_callees (map decode_finite_native_premise ts)"
  by (simp add: finite_premise_forest_callees_def premise_forest_callees_def comp_def)

section \<open>The complete mixed schema body shares one actual binder boundary\<close>

definition finite_schema_body_variables :: "'a finite_term_pattern \<Rightarrow> ('a,'u) finite_premise_template list \<Rightarrow> 'a fset" where
  "finite_schema_body_variables p ts=finite_pattern_variables p |\<union>|
    ffUnion (fimage finite_template_variables (fset_of_list ts))"

lemma finite_schema_body_variables_exact [simp]:
  "fset (finite_schema_body_variables p ts)=schema_body_variables (decode_finite_pattern p) (map decode_finite_native_premise ts)"
  by (auto simp: finite_schema_body_variables_def schema_body_variables_def template_list_variables_def
    finite_pattern_variables_correct ffUnion.rep_eq fimage.rep_eq fset_of_list.rep_eq)

definition finite_schema_body_syntax :: "('a\<Rightarrow>local_address) \<Rightarrow> 'a finite_term_pattern \<Rightarrow>
    ('a,'u) finite_premise_template list \<Rightarrow> finite_exact_artifact" where
  "finite_schema_body_syntax f p ts=finite_bound_union (finite_pattern_syntax f p) (finite_premise_forest_syntax f ts)"

lemma decode_finite_schema_body_syntax [simp]:
  "decode_finite_object (finite_schema_body_syntax f p ts)=schema_body_syntax f (decode_finite_pattern p) (map decode_finite_native_premise ts)"
  by (simp add: finite_schema_body_syntax_def schema_body_syntax_def)

definition finite_schema_body_literals :: "'a finite_term_pattern \<Rightarrow> ('a,'u) finite_premise_template list \<Rightarrow>
    (local_address\<times>finite_exact_artifact) fset" where
  "finite_schema_body_literals p ts=finite_slot_keys (syntax_prefix 2) (finite_pattern_literal_bindings p) |\<union>|
    finite_slot_keys (syntax_prefix 3) (finite_premise_forest_literals ts)"

lemma finite_schema_body_literals_exact [simp]:
  "map_relation_values decode_finite_object (fset (finite_schema_body_literals p ts))=
    schema_body_literals (decode_finite_pattern p) (map decode_finite_native_premise ts)"
  by (simp only: finite_schema_body_literals_def finite_reference_union_values finite_slot_keys_values
    finite_pattern_literal_bindings_exact finite_premise_forest_literals_exact schema_body_literals_def)

definition finite_schema_body_callees :: "('a,'u) finite_premise_template list \<Rightarrow> (local_address\<times>'u definition_site) fset" where
  "finite_schema_body_callees ts=finite_slot_keys (syntax_prefix 3) (finite_premise_forest_callees ts)"

lemma finite_schema_body_callees_exact [simp]:
  "fset (finite_schema_body_callees ts)=schema_body_callees (map decode_finite_native_premise ts)"
  by (simp add: finite_schema_body_callees_def schema_body_callees_def)

export_code finite_schema_body_variables finite_schema_body_syntax finite_schema_body_literals
  finite_schema_body_callees finite_template_formed checking SML

text \<open>
  Every call pattern and all five fields of each material premise are retained.
  The complete executable body and both reference tables decode to the original
  schema-body constructors. No observation result is supplied while constructing
  material syntax; its later satisfaction remains the original native condition.
\<close>

end
