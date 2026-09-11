theory Factor_Paired_List_Relations
  imports Main
begin

section \<open>Jointly determining relations retain complete sequence occurrences\<close>

theorem paired_list_relations_determine:
  assumes element: "\<And>a b x y. R a x \<Longrightarrow> S a y \<Longrightarrow> R b x \<Longrightarrow> S b y \<Longrightarrow> a=b"
    and first: "list_all2 R as xs" "list_all2 S as ys"
    and second: "list_all2 R bs xs" "list_all2 S bs ys"
  shows "as=bs"
proof -
  have lengths: "length as=length bs"
    using first(1) second(1) by (simp add: list_all2_conv_all_nth)
  show ?thesis
  proof (rule nth_equalityI[OF lengths])
    fix i assume inside: "i<length as"
    show "as!i=bs!i"
      by (rule element) (use first second inside lengths in \<open>auto simp: list_all2_conv_all_nth\<close>)
  qed
qed

text \<open>
  Neither relation needs to determine its input alone. The same two complete
  output sequences determine every input occurrence when their element
  relations jointly do so. Empty sequences and repetitions are included.
\<close>

end
