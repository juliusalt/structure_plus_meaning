theory Factor_Related_Test_References
  imports Factor_Related_Test_Clauses
begin

section \<open>One complete report shape retains both witness roles\<close>

definition related_test_reference_value ::
  "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow>
    factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term" where
  "related_test_reference_value x y s t k d=
    schema_reference_value (data_list_term [x,y]) x
      (data_list_term [Pair_Term s (Pair_Term k (Pair_Term x y)),Pair_Term t (Pair_Term d y)])
      (Payload_Term []) (Target_Term (Whole_Artifact empty_artifact))
      (data_list_term [Pair_Term s (Pair_Term k
        (Pair_Term (Target_Term (Whole_Artifact empty_artifact)) (Target_Term (Whole_Artifact empty_artifact)))),
        Pair_Term t (Pair_Term d (Target_Term (Whole_Artifact empty_artifact)))]) (Payload_Term [])"

definition related_test_reference_pattern ::
  "'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow>
    'a term_pattern \<Rightarrow> 'a term_pattern \<Rightarrow> 'a term_pattern" where
  "related_test_reference_pattern x y s t k d=
    schema_reference_pattern (data_list_pattern [x,y]) x
      (data_list_pattern [Pattern_Pair s (Pattern_Pair k (Pattern_Pair x y)),Pattern_Pair t (Pattern_Pair d y)])
      (Pattern_Payload []) (Pattern_Target (Whole_Artifact empty_artifact))
      (data_list_pattern [Pattern_Pair s (Pattern_Pair k
        (Pattern_Pair (Pattern_Target (Whole_Artifact empty_artifact)) (Pattern_Target (Whole_Artifact empty_artifact)))),
        Pattern_Pair t (Pattern_Pair d (Pattern_Target (Whole_Artifact empty_artifact)))]) (Pattern_Payload [])"

lemma evaluate_related_test_reference [simp]:
  "evaluate_pattern h (related_test_reference_pattern x y s t k d)=
    related_test_reference_value (evaluate_pattern h x) (evaluate_pattern h y)
      (evaluate_pattern h s) (evaluate_pattern h t) (evaluate_pattern h k) (evaluate_pattern h d)"
  by (simp add: related_test_reference_pattern_def related_test_reference_value_def)

theorem related_test_reference_presents:
  assumes variables: "x\<noteq>y" and sockets: "s\<noteq>t"
    and addresses: "octets_formed x" "octets_formed y" "octets_formed s" "octets_formed t"
      "octets_formed (snd k)" "octets_formed (snd d)"
  shows "schema_reference_presents (related_test_clause x y s t k d)
    (related_test_reference_value (Payload_Term x) (Payload_Term y) (Payload_Term s) (Payload_Term t)
      (definition_site_value k) (definition_site_value d))"
proof -
  let ?a="Payload_Term x" let ?b="Payload_Term y"
  let ?z="Target_Term (Whole_Artifact empty_artifact)"
  let ?S="related_test_clause x y s t k d"
  have formed: "schema_data_formed ?S" using sockets addresses
    by (auto simp: schema_data_formed_def)
  have data: "schema_reference_data ?S=({x,y},
    ((?a,({(s,k,Pair_Term ?a ?b),(t,d,?b)},{})),
     (?z,({(s,k,Pair_Term ?z ?z),(t,d,?z)},{}))))"
    by (auto simp: schema_reference_data_def schema_reference_outputs_def related_test_clause_def
      evaluate_schema_premises_def evaluate_schema_materials_def schema_variables_def)
  show ?thesis unfolding schema_reference_presents_def
    apply (rule conjI[OF formed])
    apply (simp only: data schema_reference_record_fields)
    apply (rule exI[of _ "[x,y]"], rule exI[of _ "[(s,k,Pair_Term ?a ?b),(t,d,?b)]"],
      rule exI[of _ "[]"], rule exI[of _ "[(s,k,Pair_Term ?z ?z),(t,d,?z)]"], rule exI[of _ "[]"])
    using variables sockets apply (simp add: related_test_reference_value_def call_instance_value_def)
    done
qed

lemma two_call_rows_recover:
  assumes rows: "call_instance_rows_term qs=
    data_list_term [Pair_Term s (Pair_Term k p),Pair_Term t (Pair_Term d q)]"
  obtains a b c e where "s=Payload_Term a" "t=Payload_Term b"
    "k=definition_site_value c" "d=definition_site_value e" "qs=[(a,c,p),(b,e,q)]"
proof -
  have list: "map call_row_value qs=[Pair_Term s (Pair_Term k p),Pair_Term t (Pair_Term d q)]"
    using rows by (simp only: call_row_values[symmetric] data_list_term_injective)
  have length: "length qs=2" using arg_cong[OF list, of length] by simp
  obtain first rest where initial: "qs=first#rest" using length by (cases qs) auto
  obtain second tail where final: "rest=second#tail" using length initial by (cases rest) auto
  have tail: "tail=[]" using length initial final by simp
  obtain a c p' where first: "first=(a,c,p')" by (cases first) auto
  obtain b e q' where second: "second=(b,e,q')" by (cases second) auto
  have shape: "qs=[(a,c,p'),(b,e,q')]" using initial final tail first second by simp
  have fields: "s=Payload_Term a" "t=Payload_Term b" "k=definition_site_value c"
    "d=definition_site_value e" "p'=p" "q'=q"
    using list by (auto simp: shape call_instance_value_def)
  show thesis using that fields shape by blast
qed

theorem related_test_reference_recovers:
  assumes report: "schema_reference_presents S (related_test_reference_value x y s t k d)"
  shows "\<exists>a b r q compare test. x=Payload_Term a \<and> y=Payload_Term b \<and>
    s=Payload_Term r \<and> t=Payload_Term q \<and>
    k=definition_site_value compare \<and> d=definition_site_value test \<and>
    a\<noteq>b \<and> r\<noteq>q \<and> S=related_test_clause a b r q compare test"
proof -
  let ?z="Target_Term (Whole_Artifact empty_artifact)"
  obtain Vs u qs cs v ws ds where parts: "distinct Vs"
    "schema_instance S (image (\<lambda>a. (a,Payload_Term a)) (set Vs)) u (set qs)"
    "related_test_reference_value x y s t k d=
      schema_reference_value (data_list_term (map Payload_Term Vs)) u (call_instance_rows_term qs)
        (binding_rows_term cs) v (call_instance_rows_term ws) (binding_rows_term ds)"
    using schema_reference_presents_fields[THEN iffD1, OF report] by blast
  let ?left="\<lambda>v. case v of Pair_Term a b \<Rightarrow> a | _ \<Rightarrow> Payload_Term []"
  let ?right="\<lambda>v. case v of Pair_Term a b \<Rightarrow> b | _ \<Rightarrow> Payload_Term []"
  have binder_projection: "data_list_term [x,y]=data_list_term (map Payload_Term Vs)"
    using arg_cong[OF parts(3), of ?left] by (simp add: related_test_reference_value_def)
  have binder_value: "data_list_term (map Payload_Term Vs)=data_list_term [x,y]"
    by (rule binder_projection[symmetric])
  have call_projection: "data_list_term
      [Pair_Term s (Pair_Term k (Pair_Term x y)),Pair_Term t (Pair_Term d y)]=call_instance_rows_term qs"
    using arg_cong[OF parts(3), of "\<lambda>v. ?left (?right (?left (?right v)))"]
    by (simp add: related_test_reference_value_def)
  have calls:
    "call_instance_rows_term qs=data_list_term
      [Pair_Term s (Pair_Term k (Pair_Term x y)),Pair_Term t (Pair_Term d y)]"
    by (rule call_projection[symmetric])
  have binder_list: "map Payload_Term Vs=[x,y]" using binder_value by (simp only: data_list_term_injective)
  have length: "length Vs=2" using arg_cong[OF binder_list, of length] by simp
  obtain a rest where initial: "Vs=a#rest" using length by (cases Vs) auto
  obtain b tail where final: "rest=b#tail" using length initial by (cases rest) auto
  have tail: "tail=[]" using length initial final by simp
  have Vs: "Vs=[a,b]" using initial final tail by simp
  have variables: "x=Payload_Term a" "y=Payload_Term b" "a\<noteq>b"
    using binder_list parts(1) by (simp_all add: Vs)
  obtain r q compare test where rows: "s=Payload_Term r" "t=Payload_Term q"
    "k=definition_site_value compare" "d=definition_site_value test"
    "qs=[(r,compare,Pair_Term x y),(q,test,y)]"
    using two_call_rows_recover[OF calls] by blast
  have functional: "single_valued (set qs)"
    using schema_instance_socket_boundary[OF parts(2)] by blast
  have sockets: "r\<noteq>q"
  proof
    assume same: "r=q"
    have first: "(r,compare,Pair_Term x y)\<in>set qs" using rows(5) by simp
    have second: "(r,test,y)\<in>set qs" using rows(5) same by simp
    have equal: "(compare,Pair_Term x y)=(test,y)"
      by (rule single_valued_outputs[OF functional first second])
    show False using equal variables(2) by simp
  qed
  have formed: "term_formed (related_test_reference_value x y s t k d)"
    by (rule schema_reference_presents_formed[OF report])
  have addresses: "octets_formed a" "octets_formed b" "octets_formed r" "octets_formed q"
    "octets_formed (snd compare)" "octets_formed (snd test)"
    using formed by (auto simp: related_test_reference_value_def variables(1,2) rows(1-4))
  have expected: "schema_reference_presents (related_test_clause a b r q compare test)
      (related_test_reference_value x y s t k d)"
    using related_test_reference_presents[OF variables(3) sockets addresses]
    by (simp only: variables(1,2) rows(1-4))
  have same: "S=related_test_clause a b r q compare test"
    by (rule schema_reference_presentations.recovery[OF report expected])
  show ?thesis by (rule exI[of _ a], rule exI[of _ b], rule exI[of _ r], rule exI[of _ q],
      rule exI[of _ compare], rule exI[of _ test])
    (use variables rows(1-4) sockets same in blast)
qed

text \<open>
  These reports use the complete schema-observation class. One private report
  orders the two binder roles and the two premise roles for construction;
  it represents every instance of the profile, including arbitrary renamed
  coordinates. The public source definition keeps its actual syntax.

  Complete reference admission forces distinct binders. Functional prospective
  rows force distinct premise sockets because their arguments have different
  constructors. No additional inequality test or preferred source order is
  required. Both outputs retain the actual callees and empty material families.
\<close>

end
