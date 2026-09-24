theory Ordered_Artifact_Comparison
  imports Ordered_Complete_Artifacts Linear_Comparisons
begin

section \<open>Canonical artifact rows compare field by field\<close>

definition compare_incidence_rows ::
  "(local_address\<times>local_address\<times>local_address) list \<Rightarrow> (local_address\<times>local_address\<times>local_address) list \<Rightarrow>
    linear_comparison" where
  "compare_incidence_rows=compare_listed (compare_paired compare_address (compare_paired compare_address compare_address))"

definition compare_data_rows :: "(local_address\<times>octets) list \<Rightarrow> (local_address\<times>octets) list \<Rightarrow> linear_comparison" where
  "compare_data_rows=compare_listed (compare_paired compare_address compare_address)"

lemma compare_row_fields_linear:
  "compare_listed compare_address A B=compare_linear A B"
  "compare_incidence_rows E F=compare_linear E F"
  "compare_data_rows D G=compare_linear D G"
proof -
  have address: "\<And>x y. compare_address x y=compare_linear x y" by (rule compare_address_linear)
  have triple: "\<And>x y. compare_paired compare_address (compare_paired compare_address compare_address) x y=compare_linear x y"
    by (rule compare_paired_linear[OF address compare_paired_linear[OF address address]])
  have pair: "\<And>x y. compare_paired compare_address compare_address x y=compare_linear x y"
    by (rule compare_paired_linear[OF address address])
  show "compare_listed compare_address A B=compare_linear A B" by (rule compare_listed_linear[OF address])
  show "compare_incidence_rows E F=compare_linear E F"
    unfolding compare_incidence_rows_def by (rule compare_listed_linear[OF triple])
  show "compare_data_rows D G=compare_linear D G"
    unfolding compare_data_rows_def by (rule compare_listed_linear[OF pair])
qed

definition compare_artifact_rows :: "artifact_value_rows \<Rightarrow> artifact_value_rows \<Rightarrow> linear_comparison" where
  "compare_artifact_rows=compare_paired (compare_listed compare_address)
    (compare_paired compare_incidence_rows (compare_paired compare_data_rows compare_data_rows))"

lemma compare_artifact_rows_linear: "compare_artifact_rows p q=compare_linear p q"
  unfolding compare_artifact_rows_def
  by (intro compare_paired_linear compare_row_fields_linear)

definition compare_artifacts :: "finite_exact_artifact \<Rightarrow> finite_exact_artifact \<Rightarrow> linear_comparison" where
  "compare_artifacts R S=(case compare_listed compare_address
      (sorted_list_of_fset (finite_carrier (finite_structure R))) (sorted_list_of_fset (finite_carrier (finite_structure S))) of
    Linear_Equal \<Rightarrow> (case compare_incidence_rows
        (sorted_list_of_fset (finite_incidence (finite_structure R))) (sorted_list_of_fset (finite_incidence (finite_structure S))) of
      Linear_Equal \<Rightarrow> (case compare_data_rows
          (sorted_list_of_multiset (finite_bag (finite_data R))) (sorted_list_of_multiset (finite_bag (finite_data S))) of
        Linear_Equal \<Rightarrow> compare_data_rows
          (sorted_list_of_fset (finite_bindings (finite_data R))) (sorted_list_of_fset (finite_bindings (finite_data S)))
      | c \<Rightarrow> c)
    | c \<Rightarrow> c)
  | c \<Rightarrow> c)"

theorem compare_artifacts_rows:
  "compare_artifacts R S=compare_linear (finite_artifact_rows R) (finite_artifact_rows S)"
  by (simp only: compare_artifacts_def finite_artifact_rows_def compare_linear_pair compare_row_fields_linear)

lemma less_eq_ordered_complete_artifact_compared_code [code]:
  "Ordered_Complete_Artifact R\<le>Ordered_Complete_Artifact S \<longleftrightarrow> compare_artifacts R S\<noteq>Linear_Greater"
  by (simp add: less_eq_ordered_complete_artifact_def compare_artifacts_rows compare_linear_order)

lemma less_ordered_complete_artifact_compared_code [code]:
  "Ordered_Complete_Artifact R<Ordered_Complete_Artifact S \<longleftrightarrow> compare_artifacts R S=Linear_Less"
  by (simp add: less_ordered_complete_artifact_def compare_artifacts_rows compare_linear_order)

section \<open>Listed rows with their sizes are ordered keys\<close>

type_synonym artifact_row_sizes = "nat\<times>nat\<times>nat\<times>nat"

fun artifact_row_sizes :: "artifact_value_rows \<Rightarrow> artifact_row_sizes" where
  "artifact_row_sizes (A,E,B,F)=(length A,length E,length B,length F)"

datatype compared_artifact_rows = Compared_Artifact_Rows artifact_row_sizes artifact_value_rows

fun compared_rows_key :: "compared_artifact_rows \<Rightarrow> artifact_row_sizes\<times>artifact_value_rows" where
  "compared_rows_key (Compared_Artifact_Rows z p)=(z,p)"

fun compared_rows_listing :: "compared_artifact_rows \<Rightarrow> artifact_value_rows" where
  "compared_rows_listing (Compared_Artifact_Rows z p)=p"

definition compared_artifact_rows :: "artifact_value_rows \<Rightarrow> compared_artifact_rows" where
  "compared_artifact_rows p=Compared_Artifact_Rows (artifact_row_sizes p) p"

lemma compared_artifact_rows_listing [simp]: "compared_rows_listing (compared_artifact_rows p)=p"
  by (simp add: compared_artifact_rows_def)

lemma compared_rows_key_injective:
  "compared_rows_key x=compared_rows_key y \<longleftrightarrow> x=y"
  by (cases x; cases y) simp

instantiation compared_artifact_rows :: linorder
begin

definition "x\<le>y \<longleftrightarrow> compared_rows_key x\<le>compared_rows_key y"
definition "x<y \<longleftrightarrow> compared_rows_key x<compared_rows_key y"

instance
  by standard
    (auto simp: less_eq_compared_artifact_rows_def less_compared_artifact_rows_def
      less_le_not_le compared_rows_key_injective
      intro: order_trans dest: order_antisym)

end

definition compare_row_sizes :: "artifact_row_sizes \<Rightarrow> artifact_row_sizes \<Rightarrow> linear_comparison" where
  "compare_row_sizes=compare_paired compare_natural (compare_paired compare_natural (compare_paired compare_natural compare_natural))"

definition compare_compared_rows :: "compared_artifact_rows \<Rightarrow> compared_artifact_rows \<Rightarrow> linear_comparison" where
  "compare_compared_rows x y=compare_paired compare_row_sizes compare_artifact_rows (compared_rows_key x) (compared_rows_key y)"

lemma compare_compared_rows_linear: "compare_compared_rows x y=compare_linear x y"
proof -
  have sizes: "compare_row_sizes a b=compare_linear a b" for a b
    unfolding compare_row_sizes_def
    by (intro compare_paired_linear compare_natural_linear)
  have keys: "compare_compared_rows x y=compare_linear (compared_rows_key x) (compared_rows_key y)"
    unfolding compare_compared_rows_def
    by (intro compare_paired_linear sizes compare_artifact_rows_linear)
  show ?thesis
    by (auto simp: keys compare_linear_def less_compared_artifact_rows_def compared_rows_key_injective)
qed

lemma less_eq_compared_artifact_rows_code [code]:
  "x\<le>(y::compared_artifact_rows) \<longleftrightarrow> compare_compared_rows x y\<noteq>Linear_Greater"
  by (simp add: compare_compared_rows_linear compare_linear_order)

lemma less_compared_artifact_rows_code [code]:
  "x<(y::compared_artifact_rows) \<longleftrightarrow> compare_compared_rows x y=Linear_Less"
  by (simp add: compare_compared_rows_linear compare_linear_order)

text \<open>
  Two complete artifacts compare by their canonical carriers, then incidence,
  counted data and bindings, each listing lexicographically in one pass, so the
  comparison of the complete canonical rows stops at the first differing field
  and value. Complete listed rows used as ordered keys retain their field sizes,
  which are compared first and computed once per key. The artifact order and
  every compared value are unchanged.
\<close>

section \<open>A target's key\<close>

text \<open>
  A target's key is its artifact's compared rows with its occurrence. It is injective, so a table of
  targets is keyed by it (\<open>Shared_Term_Tables.keyed_reference_step\<close>).
\<close>

fun finite_target_occurrence :: "finite_exact_target \<Rightarrow> local_address option" where
  "finite_target_occurrence (Finite_Whole a)=None"
| "finite_target_occurrence (Finite_Anchor a r)=Some r"

definition finite_target_key :: "finite_exact_target \<Rightarrow> compared_artifact_rows\<times>local_address option" where
  "finite_target_key x=(compared_artifact_rows (finite_artifact_rows (finite_target_artifact x)),finite_target_occurrence x)"

lemma finite_target_key_injective: "inj finite_target_key"
proof (rule injI)
  fix x y
  assume same: "finite_target_key x=finite_target_key y"
  show "x=y"
    using same by (cases x; cases y) (simp_all add: finite_target_key_def compared_artifact_rows_def
      finite_artifact_rows_injective)
qed

end
