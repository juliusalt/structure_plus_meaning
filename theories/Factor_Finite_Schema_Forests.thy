theory Factor_Finite_Schema_Forests
  imports Factor_Finite_Schema_Compilation Factor_Schema_Forests Option_List_Maps
begin

section \<open>Every source clause supplies one complete compiled block\<close>

type_synonym finite_compiled_schema_forest = "finite_exact_artifact\<times>local_address list\<times>
  (local_address,local_address,local_address option definition_site) finite_factor_schema list\<times>
  (local_address\<times>finite_exact_artifact) fset\<times>(local_address\<times>local_address option definition_site) fset"

definition finite_schema_forest :: "finite_compiled_schema list\<Rightarrow>finite_compiled_schema_forest" where
  "finite_schema_forest Ks=(let Rs=map (\<lambda>(R,r,T,L,C). R) Ks;
    rs=map (\<lambda>(R,r,T,L,C). r) Ks; As=map (\<lambda>(R,r,T,L,C). T) Ks;
    Ls=map (\<lambda>(R,r,T,L,C). L) Ks; Cs=map (\<lambda>(R,r,T,L,C). C) Ks;
    is=[0..<length Ks] in (finite_syntax_forest Rs,
      map (\<lambda>i. syntax_branch i (rs!i)) is,
      map (\<lambda>i. finite_rename_schema (syntax_branch i) (syntax_branch i) id (As!i)) is,
      finite_syntax_forest_table Ls,finite_syntax_forest_table Cs))"

definition finite_compile_schema_forest ::
  "('a::linorder,'s::linorder,local_address option definition_site) finite_factor_schema list\<Rightarrow>finite_compiled_schema_forest option" where
  "finite_compile_schema_forest Ss=map_option finite_schema_forest (those (map finite_compile_schema Ss))"

lemma finite_compile_schema_forest_domain:
  "finite_compile_schema_forest Ss=None \<longleftrightarrow> (\<exists>S\<in>set Ss. finite_compile_schema S=None)"
  by (simp add: finite_compile_schema_forest_def those_map_none_iff)

theorem finite_compile_schema_forest_correct:
  assumes result: "finite_compile_schema_forest Ss=Some (R,rs,As,L,C)"
  shows "finite_exact_formed R" "bag_count (object_data (decode_finite_object R))=(\<lambda>_. 0)"
    "length rs=length Ss" "length As=length Ss"
    "reference_table_formed (map_relation_values decode_finite_object (fset L)) (fset C)"
    "rel_dom (fset L)\<union>rel_dom (fset C)\<subseteq>rra_carrier (object_structure (decode_finite_object R))"
    "rel_ran (fset C)=(\<Union>S\<in>set Ss. schema_dependencies (decode_finite_schema S))"
    "set rs\<subseteq>rra_carrier (object_structure (decode_finite_object R))"
    "\<forall>i<length Ss. schema_alpha_variant (decode_finite_schema (Ss!i)) (decode_finite_schema (As!i))"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u (decode_finite_object R) \<longrightarrow>
      syntax_references E u (map_relation_values decode_finite_object (fset L)) (fset C) \<longrightarrow>
      (\<forall>i<length Ss. native_schema_at E u (rs!i) (decode_finite_schema (As!i)))"
proof -
  obtain Ks where compiled: "those (map finite_compile_schema Ss)=Some Ks"
    and assembled: "finite_schema_forest Ks=(R,rs,As,L,C)"
    using result by (auto simp: finite_compile_schema_forest_def split: option.splits)
  have paired: "list_all2 (\<lambda>S K. finite_compile_schema S=Some K) Ss Ks"
    using compiled by (simp only: those_map_result)
  have length: "length Ks=length Ss"
    and each: "\<forall>i<length Ss. finite_compile_schema (Ss!i)=Some (Ks!i)"
    using paired by (auto simp: list_all2_conv_all_nth)
  let ?Ss="map decode_finite_schema Ss"
  let ?RR="map (\<lambda>(R,r,T,L,C). R) Ks"
  let ?rr="map (\<lambda>(R,r,T,L,C). r) Ks"
  let ?AA="map (\<lambda>(R,r,T,L,C). T) Ks"
  let ?LL="map (\<lambda>(R,r,T,L,C). L) Ks"
  let ?CC="map (\<lambda>(R,r,T,L,C). C) Ks"
  let ?Rs="map decode_finite_object ?RR"
  let ?Ts="map decode_finite_schema ?AA"
  let ?Ls="map (\<lambda>M. map_relation_values decode_finite_object (fset M)) ?LL"
  let ?Cs="map fset ?CC"
  have counts: "length ?Rs=length ?Ss" "length ?rr=length ?Ss" "length ?Ts=length ?Ss"
    "length ?Ls=length ?Ss" "length ?Cs=length ?Ss" using length by simp_all
  have codes: "\<forall>i<length ?Ss. schema_alpha_variant (?Ss!i) (?Ts!i) \<and>
    schema_code (?Rs!i) (?rr!i) (?Ts!i) (?Ls!i) (?Cs!i)"
  proof (intro allI impI)
    fix i assume index: "i<length ?Ss"
    have si: "i<length Ss" and ki: "i<length Ks" using index length by simp_all
    obtain A a T B D where row: "Ks!i=(A,a,T,B,D)" by (metis surjective_pairing)
    have child: "finite_compile_schema (Ss!i)=Some (A,a,T,B,D)" using each si row by simp
    show "schema_alpha_variant (?Ss!i) (?Ts!i) \<and> schema_code (?Rs!i) (?rr!i) (?Ts!i) (?Ls!i) (?Cs!i)"
      using finite_compile_schema_correct(3)[OF child] finite_compiled_schema_code[OF child]
      by (simp add: si ki row)
  qed
  interpret forest: schema_forest_construction ?Ss ?Rs ?rr ?Ts ?Ls ?Cs
    by (rule schema_forest_construction.intro[OF counts codes])
  have raw: "R=finite_syntax_forest ?RR"
    "rs=map (\<lambda>i. syntax_branch i (?rr!i)) [0..<length Ks]"
    "As=map (\<lambda>i. finite_rename_schema (syntax_branch i) (syntax_branch i) id (?AA!i)) [0..<length Ks]"
    "L=finite_syntax_forest_table ?LL" "C=finite_syntax_forest_table ?CC"
    using assembled by (auto simp: finite_schema_forest_def Let_def)
  have actual: "decode_finite_object R=forest.artifact" "rs=forest.roots"
    "map_relation_values decode_finite_object (fset L)=forest.literals" "fset C=forest.callees"
  proof -
    show "decode_finite_object R=forest.artifact" by (simp only: raw(1) decode_finite_syntax_forest)
    show "rs=forest.roots" by (simp only: raw(2) length_map length)
    show "map_relation_values decode_finite_object (fset L)=forest.literals"
      by (simp only: raw(4) finite_syntax_forest_table_values)
    show "fset C=forest.callees" by (simp only: raw(5) finite_syntax_forest_table_exact)
  qed
  have encoded: "map decode_finite_schema As=map (\<lambda>i.
    decode_finite_schema (finite_rename_schema (syntax_branch i) (syntax_branch i) id (?AA!i))) [0..<length Ks]"
    by (simp only: raw(3) map_map comp_def)
  have schemas: "map decode_finite_schema As=forest.schemas"
  proof (simp only: encoded length_map length; rule map_cong[OF refl])
    fix i assume index: "i\<in>set [0..<length Ss]"
    have ki: "i<length Ks" using index length by simp
    show "decode_finite_schema (finite_rename_schema (syntax_branch i) (syntax_branch i) id (?AA!i))=
      rename_schema (syntax_branch i) (syntax_branch i) id (?Ts!i)"
      by (simp add: comp_def finite_rename_schema_correct ki)
  qed
  have size: "length As=length Ss" using arg_cong[OF schemas, of length] forest.properties(4) by simp
  have literal_domain: "rel_dom (fset L)=rel_dom forest.literals"
    using arg_cong[OF actual(3), of rel_dom] by (simp only: map_relation_values_domain)
  show "finite_exact_formed R" "bag_count (object_data (decode_finite_object R))=(\<lambda>_. 0)"
    "length rs=length Ss" "length As=length Ss"
    using forest.properties(1-4) size by (simp_all add: finite_exact_formed_correct actual)
  show "reference_table_formed (map_relation_values decode_finite_object (fset L)) (fset C)"
    "rel_dom (fset L)\<union>rel_dom (fset C)\<subseteq>rra_carrier (object_structure (decode_finite_object R))"
    "rel_ran (fset C)=(\<Union>S\<in>set Ss. schema_dependencies (decode_finite_schema S))"
    "set rs\<subseteq>rra_carrier (object_structure (decode_finite_object R))"
    using forest.properties(5-8) by (simp_all add: actual literal_domain)
  show "\<forall>i<length Ss. schema_alpha_variant (decode_finite_schema (Ss!i)) (decode_finite_schema (As!i))"
    using forest.properties(9) by (simp only: schemas[symmetric]) (simp add: size)
  show "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u (decode_finite_object R) \<longrightarrow>
    syntax_references E u (map_relation_values decode_finite_object (fset L)) (fset C) \<longrightarrow>
    (\<forall>i<length Ss. native_schema_at E u (rs!i) (decode_finite_schema (As!i)))"
    using forest.properties(10) by (simp only: actual schemas[symmetric]) (simp add: size)
qed

text \<open>
  Partial compilation uses the existing complete option-list traversal. A
  failed clause prevents the whole result; every successful source occurrence
  has one compiled block in the original order. All blocks then instantiate
  the same forest-construction proof as the original general compiler.
\<close>

end
