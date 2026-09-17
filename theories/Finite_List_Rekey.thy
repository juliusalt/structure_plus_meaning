theory Finite_List_Rekey
  imports Bootstrap_Relations
begin

section \<open>An explicit lookup realizes the existing complete list correspondence\<close>

definition listed_rekey :: "'a list \<Rightarrow> 'b list \<Rightarrow> 'b \<Rightarrow> 'a \<Rightarrow> 'b" where
  "listed_rekey xs ys b x=(case map_of (zip xs ys) x of None \<Rightarrow> b | Some y \<Rightarrow> y)"

theorem listed_rekey_properties:
  assumes lengths: "length xs=length ys" and distinct: "distinct xs" "distinct ys"
  shows "inj_on (listed_rekey xs ys b) (set xs)" "map (listed_rekey xs ys b) xs=ys"
proof -
  obtain h where source: "inj_on h (set xs)" "map h xs=ys"
    using distinct_list_rekey[OF lengths distinct] by blast
  have actual: "listed_rekey xs ys b x=h x" if "x\<in>set xs" for x
    using that by (simp only: listed_rekey_def source(2)[symmetric] map_of_zip_map; simp)
  show "inj_on (listed_rekey xs ys b) (set xs)"
    using source(1) actual by (auto simp: inj_on_def)
  show "map (listed_rekey xs ys b) xs=ys"
    using source(2) by (subst map_cong[OF refl actual]) simp
qed

text \<open>
  The existing distinct-list correspondence supplies the proof, and the
  executable lookup agrees with it on every actual source key. The fallback
  value is inspected only outside that complete boundary.
\<close>

end
