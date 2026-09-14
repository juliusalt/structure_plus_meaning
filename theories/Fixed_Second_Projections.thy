theory Fixed_Second_Projections
  imports Main
begin

lemma fixed_second_shape:
  assumes fixed: "\<forall>x\<in>A. snd x=b" and member: "x\<in>A"
  shows "(fst x,b)=x"
  using fixed member by (cases x) auto

lemma fixed_second_image_member:
  assumes fixed: "\<forall>x\<in>A. snd x=b" and member: "u\<in>fst ` A"
  shows "(u,b)\<in>A"
proof -
  obtain x where actual: "x\<in>A" and key: "u=fst x" using member by blast
  show ?thesis by (simp only: key fixed_second_shape[OF fixed actual]; rule actual)
qed

lemma fixed_second_first_injective:
  assumes fixed: "\<forall>x\<in>A. snd x=b"
  shows "inj_on fst A"
proof (rule inj_onI)
  fix x y assume left: "x\<in>A" and right: "y\<in>A" and same: "fst x=fst y"
  have "(fst x,b)=(fst y,b)" using same by simp
  then show "x=y" by (simp only: fixed_second_shape[OF fixed left] fixed_second_shape[OF fixed right])
qed

end
