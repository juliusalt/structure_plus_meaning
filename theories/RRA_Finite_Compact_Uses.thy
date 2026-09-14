theory RRA_Finite_Compact_Uses
  imports RRA_Compact_Uses RRA_Finite_Environment_Construction
begin

definition finite_compact_use_head where
  "finite_compact_use_head U u=Suc (fMax (fimage use_word_head (finsert u U)))"

definition finite_compact_use_map where
  "finite_compact_use_map U u=prefix_use_map [finite_compact_use_head U u] u"

theorem finite_compact_use_map_exact:
  "finite_compact_use_map U u=compact_use_map (fset U) u"
  by (simp add: finite_compact_use_map_def compact_use_map_def compact_use_prefix_def
    finite_compact_use_head_def compact_use_head_def fMax.F.rep_eq fimage.rep_eq)

corollary finite_compact_use_map_injective:
  "inj (finite_compact_use_map U u)"
  by (simp only: finite_compact_use_map_exact; rule compact_use_map_injective; simp)

corollary finite_compact_use_map_outside:
  "finite_compact_use_map U u (Some word)\<notin>insert u (fset U)"
  by (simp only: finite_compact_use_map_exact; rule compact_use_map_outside; simp)

export_code finite_compact_use_head finite_compact_use_map checking SML

end
