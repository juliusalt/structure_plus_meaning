theory Keyed_Option_Maps
  imports Option_List_Maps
begin

section \<open>A complete partial traversal retains its original keys\<close>

definition keyed_option_map :: "('a\<Rightarrow>'b option)\<Rightarrow>'a list\<Rightarrow>('a\<times>'b) list option" where
  "keyed_option_map f xs=map_option (zip xs) (those (map f xs))"

lemma keyed_option_map_domain:
  "keyed_option_map f xs=None \<longleftrightarrow> (\<exists>x\<in>set xs. f x=None)"
  by (simp add: keyed_option_map_def those_map_none_iff split: option.splits)

lemma keyed_option_map_result:
  assumes result: "keyed_option_map f xs=Some rows"
  shows "map fst rows=xs" and "\<forall>(x,y)\<in>set rows. f x=Some y"
proof -
  obtain ys where vals: "those (map f xs)=Some ys" and rows: "rows=zip xs ys"
    using result by (auto simp: keyed_option_map_def split: option.splits)
  have related: "list_all2 (\<lambda>x y. f x=Some y) xs ys"
    using vals by (simp only: those_map_result)
  have length: "length xs=length ys" by (rule list_all2_lengthD[OF related])
  show "map fst rows=xs" using length by (simp add: rows)
  show "\<forall>(x,y)\<in>set rows. f x=Some y"
    using related by (simp add: rows list_all2_iff)
qed

lemma keyed_option_map_lookup:
  assumes result: "keyed_option_map f xs=Some rows" and member: "x\<in>set xs"
  shows "f x=Some (the (map_of rows x))"
proof -
  have key: "x\<in>image fst (set rows)" using keyed_option_map_result(1)[OF result] member
    by (metis list.set_map)
  obtain y where selected: "map_of rows x=Some y"
    using key by (cases "map_of rows x") (auto simp: map_of_eq_None_iff)
  have row: "(x,y)\<in>set rows" by (rule map_of_SomeD[OF selected])
  show ?thesis using keyed_option_map_result(2)[OF result] row by (auto simp: selected)
qed

theorem keyed_option_map_at:
  assumes result: "keyed_option_map f xs=Some rows" and index: "i<length xs"
  shows "i<length rows \<and> fst (rows!i)=xs!i \<and> f (xs!i)=Some (snd (rows!i))"
proof -
  have keys: "map fst rows=xs" by (rule keyed_option_map_result(1)[OF result])
  have bound: "i<length rows" using index keys by (metis length_map)
  have key: "fst (rows!i)=xs!i" using keys bound by (metis nth_map)
  have queried: "f (fst (rows!i))=Some (snd (rows!i))"
    using keyed_option_map_result(2)[OF result] nth_mem[OF bound]
    by (cases "rows!i") auto
  show ?thesis using bound key queried by simp
qed

end
