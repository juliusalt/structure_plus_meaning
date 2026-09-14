theory Factor_Literal_Replay_Alternatives
  imports Factor_Literal_Replay_Cases Finite_Singleton_Projections
begin

lemma finite_literal_application_singleton:
  "finite_singleton_option (fimage (\<lambda>((d,t),I,K). t) (finite_application_readings E u r))=
      Some (Finite_Target (Finite_Whole R)) \<longleftrightarrow>
    finite_literal_application_ready E u r R"
proof -
  have unique: "(case x of ((d,t),I,K) \<Rightarrow> t)=(case y of ((d,t),I,K) \<Rightarrow> t)"
    if first: "x |\<in>| finite_application_readings E u r"
      and second: "y |\<in>| finite_application_readings E u r" for x y
  proof -
    obtain d t I K where left: "x=((d,t),I,K)" by (cases x) auto
    obtain e s J W where right: "y=((e,s),J,W)" by (cases y) auto
    have readings: "((d,t),I,K) |\<in>| finite_application_readings E u r"
      "((e,s),J,W) |\<in>| finite_application_readings E u r"
      using first second by (simp_all only: left right)
    show ?thesis using finite_application_readings_unique[OF readings]
      by (simp only: left right case_prod_conv; blast)
  qed
  show ?thesis
    using finite_singleton_projection_member[OF unique, where a="Finite_Target (Finite_Whole R)"]
    by (simp only: finite_literal_application_ready_def case_prod_unfold)
qed

theorem literal_replay_singleton_exact:
  "literal_replay_method 6 X=literal_replay_holds X"
proof -
  obtain E pu pr au ar root R where input: "X=(E,pu,pr,au,ar,root,R)" by (cases X) auto
  have same: "literal_replay_method 6 X=literal_replay_method 0 X"
    by (simp add: input literal_replay_method_def literal_replay_report_def literal_replay_decide_def
      Let_def finite_literal_application_singleton finite_literal_application_ready_def)
  show ?thesis by (simp only: same literal_replay_original_exact)
qed

end
