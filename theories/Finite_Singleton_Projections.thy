theory Finite_Singleton_Projections
  imports Finite_Singleton_Selection
begin

lemma finite_singleton_projection_member:
  assumes unique: "\<And>x y. x |\<in>| R \<Longrightarrow> y |\<in>| R \<Longrightarrow> h x=h y"
  shows "finite_singleton_option (fimage h R)=Some a \<longleftrightarrow>
    fBex R (\<lambda>x. h x=a)"
proof -
  have projected: "x=y" if first: "x |\<in>| fimage h R"
    and second: "y |\<in>| fimage h R" for x y
  proof -
    obtain p where p: "p |\<in>| R" "x=h p" using first by (simp only: fimage_iff; blast)
    obtain q where q: "q |\<in>| R" "y=h q" using second by (simp only: fimage_iff; blast)
    show ?thesis using unique[OF p(1) q(1)] p(2) q(2) by simp
  qed
  have selected: "finite_singleton_option (fimage h R)=Some a \<longleftrightarrow> a |\<in>| fimage h R"
    by (rule finite_singleton_option_member) (rule projected)
  show ?thesis by (simp only: selected fimage_iff; blast)
qed

end
