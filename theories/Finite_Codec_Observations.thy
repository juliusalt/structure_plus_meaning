theory Finite_Codec_Observations
  imports Finite_Map_Observations
begin

definition finite_codec_assess where
  "finite_codec_assess encode decode A P=(
    finite_map_rows A (\<lambda>x. (encode x,decode (encode x))),
    finite_map_rows P (\<lambda>p. (decode p,map_option encode (decode p))))"

definition finite_codec_roundtrip where
  "finite_codec_roundtrip report=finite_map_preserves (fst report) (\<lambda>x (p,r). r=Some x)"

definition finite_codec_reflection where
  "finite_codec_reflection report=finite_map_preserves (snd report)
    (\<lambda>p (r,q). case q of None \<Rightarrow> True | Some q \<Rightarrow> p=q)"

definition finite_codec_injective where
  "finite_codec_injective report=finite_map_injective
    (fimage (\<lambda>(x,p,r). (x,p)) (fst report))"

definition finite_codec_preserves where
  "finite_codec_preserves report B=finite_map_preserves (fst report) (\<lambda>x (p,r). B x p)"

lemma finite_codec_roundtrip_exact:
  "finite_codec_roundtrip (finite_codec_assess encode decode A P)=
    (\<forall>x\<in>fset A. decode (encode x)=Some x)"
  by (simp add: finite_codec_roundtrip_def finite_codec_assess_def finite_map_preserves_exact)

lemma finite_codec_reflection_exact:
  "finite_codec_reflection (finite_codec_assess encode decode A P)=
    (\<forall>p\<in>fset P. \<forall>x. decode p=Some x \<longrightarrow> p=encode x)"
  by (auto simp: finite_codec_reflection_def finite_codec_assess_def finite_map_preserves_exact
    split: option.splits)

lemma finite_codec_injective_exact:
  "finite_codec_injective (finite_codec_assess encode decode A P)=inj_on encode (fset A)"
proof -
  have graph: "fimage (\<lambda>(x,p,r). (x,p))
    (finite_map_rows A (\<lambda>x. (encode x,decode (encode x))))=finite_map_rows A encode"
    by (simp add: finite_map_rows_def fimage_fimage comp_def)
  show ?thesis by (simp add: finite_codec_injective_def finite_codec_assess_def graph finite_map_injective_exact)
qed

lemma finite_codec_preserves_exact:
  "finite_codec_preserves (finite_codec_assess encode decode A P) B=(\<forall>x\<in>fset A. B x (encode x))"
  by (simp add: finite_codec_preserves_def finite_codec_assess_def finite_map_preserves_exact)

text \<open>
  Both finite graphs come from the actual encoder and decoder. Roundtrip,
  reflection of every accepted observed path, injection and an independent
  input/output condition are recovered from these complete graphs. The decoder
  result and its re-encoding remain present even when reflection fails.
\<close>

end
