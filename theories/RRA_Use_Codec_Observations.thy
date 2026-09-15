theory RRA_Use_Codec_Observations
  imports RRA_Digit_Use_Paths RRA_Binary_Path_Decoding Finite_Codec_Observations
begin

type_synonym use_codec =
  "(local_address option\<Rightarrow>bool list)\<times>(bool list\<Rightarrow>local_address option option)"
type_synonym use_codec_subject = "local_address option fset\<times>bool list fset\<times>nat"

type_synonym use_codec_report =
  "use_codec_subject\<times>
    (local_address option\<times>bool list\<times>local_address option option) fset\<times>
    (bool list\<times>local_address option option\<times>bool list option) fset"

fun use_coordinate_bound :: "nat\<Rightarrow>local_address option\<Rightarrow>bool" where
  "use_coordinate_bound k None=True"
| "use_coordinate_bound k (Some word)=(\<forall>n\<in>set word. n<2^k)"

fun use_path_budget where
  "use_path_budget k None=1"
| "use_path_budget k (Some word)=1+length word*(2*k+1)"

definition use_path_budget_condition where
  "use_path_budget_condition k u path=(use_coordinate_bound k u \<longrightarrow>
    length path\<le>use_path_budget k u)"

definition use_codec_condition where
  "use_codec_condition (f::nat) codec X=(case (codec,X) of ((encode,decode),(A,P,k)) \<Rightarrow>
    if f=0 then (\<forall>u\<in>fset A. decode (encode u)=Some u)
    else if f=1 then (\<forall>p\<in>fset P. \<forall>u. decode p=Some u \<longrightarrow> p=encode u)
    else if f=2 then inj_on encode (fset A)
    else if f=3 then (\<forall>u\<in>fset A. use_path_budget_condition k u (encode u))
    else False)"

definition use_codec_assess where
  "use_codec_assess codec X=(case (codec,X) of ((encode,decode),(A,P,k)) \<Rightarrow>
    (X,finite_codec_assess encode decode A P))"

definition use_codec_inspect :: "use_codec_report\<Rightarrow>nat\<Rightarrow>bool" where
  "use_codec_inspect report (f::nat)=(case report of ((A,P,k),graphs) \<Rightarrow>
    if f=0 then finite_codec_roundtrip graphs
    else if f=1 then finite_codec_reflection graphs
    else if f=2 then finite_codec_injective graphs
    else if f=3 then finite_codec_preserves graphs (use_path_budget_condition k)
    else False)"

theorem use_codec_assessment_exact:
  "use_codec_inspect (use_codec_assess codec X) f=use_codec_condition f codec X"
  by (cases codec; cases X)
    (simp add: use_codec_assess_def use_codec_inspect_def use_codec_condition_def
      finite_codec_roundtrip_exact finite_codec_reflection_exact finite_codec_injective_exact
      finite_codec_preserves_exact)

lemma digit_address_bound:
  assumes "\<forall>n\<in>set word. n<2^k"
  shows "length (digit_address_path word)\<le>length word*(2*k+1)"
  using assms
proof (induction word)
  case Nil
  then show ?case by (simp add: digit_address_path_def)
next
  case (Cons n word)
  have head: "length (digit_natural_path n)\<le>2*k+1"
    by (rule digit_natural_path_bound) (use Cons.prems in simp)
  have tail: "length (digit_address_path word)\<le>length word*(2*k+1)"
    by (rule Cons.IH) (use Cons.prems in simp)
  show ?case using head tail by (simp add: digit_address_path_def; arith)
qed

theorem digit_use_path_budget:
  "use_path_budget_condition k u (digit_use_path u)"
proof (cases u)
  case None
  then show ?thesis by (simp add: use_path_budget_condition_def)
next
  case (Some word)
  have bound: "use_coordinate_bound k u \<Longrightarrow>
    length (digit_address_path word)\<le>length word*(2*k+1)"
    by (rule digit_address_bound) (simp add: Some)
  show ?thesis using bound by (simp add: Some use_path_budget_condition_def; arith)
qed

lemma use_path_budget_reverse [simp]:
  "use_path_budget_condition k u (rev path)=use_path_budget_condition k u path"
  by (simp add: use_path_budget_condition_def)

end
