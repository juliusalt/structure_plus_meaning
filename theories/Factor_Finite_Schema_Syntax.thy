theory Factor_Finite_Schema_Syntax
  imports Factor_Finite_Template_Syntax RRA_Finite_Fresh_Addresses Factor_Schema_Encoding
begin

section \<open>The complete executable schema frame is the existing native wrapper\<close>

definition finite_schema_wrapper :: "finite_exact_artifact \<Rightarrow> local_address fset \<Rightarrow>
    local_address \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow> local_address \<Rightarrow>
    local_address list \<Rightarrow> (local_address\<times>local_address) fset \<Rightarrow> finite_exact_artifact" where
  "finite_schema_wrapper R V c b m r ps M=finite_record_wrapper
    (finite_family_wrapper (finite_family_wrapper R b (fimage (\<lambda>a. (a,a)) V)) m M) r ps [b,c,m]"

lemma decode_finite_schema_wrapper [simp]:
  "decode_finite_object (finite_schema_wrapper R V c b m r ps M)=
    schema_wrapper (decode_finite_object R) (fset V) c b m r ps (fset M)"
  by (simp add: finite_schema_wrapper_def schema_wrapper_def fimage.rep_eq)

definition finite_schema_code :: "('a\<Rightarrow>local_address) \<Rightarrow> 'a finite_term_pattern \<Rightarrow>
    ('a,'u) finite_premise_template list \<Rightarrow> finite_exact_artifact\<times>local_address\<times>local_address list" where
  "finite_schema_code f p ts=(let R=finite_schema_body_syntax f p ts;
    hs=finite_fresh_addresses (finite_carrier (finite_structure R)) (6+length ts) in
    case schema_header_parts hs of (b,m,r,ps,ss) \<Rightarrow>
      (finite_schema_wrapper R (fimage f (finite_schema_body_variables p ts)) [2] b m r ps
        (fset_of_list (zip ss (schema_body_roots ts))),r,ss))"

theorem finite_schema_code_properties:
  fixes ts :: "('a,local_address option) finite_premise_template list"
  assumes pattern: "finite_pattern_formed p" and templates: "\<forall>t\<in>set ts. finite_template_formed t"
    and addressing: "binder_addressing (fset (finite_schema_body_variables p ts)) f"
    and result: "finite_schema_code f p ts=(R,r,ss)"
  shows "finite_exact_formed R"
    "bag_count (object_data (decode_finite_object R))=(\<lambda>_. 0)"
    "r\<in>rra_carrier (object_structure (decode_finite_object R))"
    "length ss=length ts" "distinct ss" "\<forall>a\<in>set ss. octets_formed a"
    "reference_table_formed (map_relation_values decode_finite_object (fset (finite_schema_body_literals p ts)))
      (fset (finite_schema_body_callees ts))"
    "rel_dom (map_relation_values decode_finite_object (fset (finite_schema_body_literals p ts)))\<union>
      rel_dom (fset (finite_schema_body_callees ts))\<subseteq>rra_carrier (object_structure (decode_finite_object R))"
    "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u (decode_finite_object R) \<longrightarrow>
      syntax_references E u (map_relation_values decode_finite_object (fset (finite_schema_body_literals p ts)))
        (fset (finite_schema_body_callees ts)) \<longrightarrow>
      native_schema_at E u r (schema_list_projection f (decode_finite_pattern p) ss (map decode_finite_native_premise ts))"
proof -
  let ?p="decode_finite_pattern p"
  let ?ts="map decode_finite_native_premise ts"
  have pf: "pattern_formed ?p" using pattern by (simp only: finite_pattern_formed_correct)
  have tf: "\<forall>t\<in>set ?ts. template_formed t" using templates by auto
  have addr: "binder_addressing (schema_body_variables ?p ?ts) f" using addressing by simp
  interpret body: schema_bodies f ?p ?ts by (rule schema_bodies.intro[OF pf tf addr])
  let ?B="finite_schema_body_syntax f p ts"
  let ?U="finite_carrier (finite_structure ?B)"
  let ?xs="finite_fresh_addresses ?U (6+length ts)"
  obtain b m a ps es where headers: "schema_header_parts ?xs=(b,m,a,ps,es)" by (metis surjective_pairing)
  have raw: "length ?xs=6+length ts" "distinct ?xs" "set ?xs\<inter>fset ?U={}"
    "\<forall>a\<in>set ?xs. octets_formed a" by (rule finite_fresh_addresses_properties)+
  have head: "length ps=3" "length es=length ts" "distinct (b#m#a#(ps@es))"
    "({b,m,a}\<union>set ps\<union>set es)\<inter>fset ?U={}"
    "\<forall>x\<in>{b,m,a}\<union>set ps\<union>set es. octets_formed x"
    by (rule schema_header_parts_properties[OF raw headers])+
  have carrier: "fset ?U=rra_carrier (object_structure body.body)"
    by (simp only: decode_finite_schema_body_syntax[symmetric]
      decode_finite_object_selectors decode_finite_structure_fields)
  have lengths: "length es=length (schema_body_roots ?ts)" "length es=length ?ts"
    using head(2) by simp_all
  have sockets: "distinct es" using head(3) by (simp add: distinct_append)
  have separate: "({b,m,a}\<union>set ps\<union>set es)\<inter>rra_carrier (object_structure body.body)={}"
    using head(4) by (simp only: carrier)
  interpret frame: schema_frame body.body body.variables "[2]" b m a ps "set (zip es (schema_body_roots ?ts))"
    by (rule schema_frame_from_headers[OF body.formed body.silent body.variables_inside body.boundary
      body.conclusion_inside body.premise_roots_inside head(1) lengths(1) head(3) separate head(5)])
  have fields: "R=finite_schema_wrapper ?B (fimage f (finite_schema_body_variables p ts)) [2] b m a ps
      (fset_of_list (zip es (schema_body_roots ts)))" "r=a" "ss=es"
    using result by (auto simp: finite_schema_code_def Let_def headers)
  have actual: "decode_finite_object R=frame.framed"
    by (simp only: fields(1) decode_finite_schema_wrapper decode_finite_schema_body_syntax
      fimage.rep_eq finite_schema_body_variables_exact fset_of_list.rep_eq schema_body_roots_map)
  show "finite_exact_formed R" by (simp only: finite_exact_formed_correct actual; rule frame.formed)
  show "bag_count (object_data (decode_finite_object R))=(\<lambda>_. 0)"
    by (simp only: actual frame.data) (simp add: schema_body_syntax_def)
  show "r\<in>rra_carrier (object_structure (decode_finite_object R))"
    by (simp only: actual fields(2) frame.carrier) simp
  show "length ss=length ts" "distinct ss" "\<forall>x\<in>set ss. octets_formed x"
    using head(2,5) sockets by (auto simp only: fields(3))
  show "reference_table_formed (map_relation_values decode_finite_object (fset (finite_schema_body_literals p ts)))
    (fset (finite_schema_body_callees ts))"
    by (simp only: finite_schema_body_literals_exact finite_schema_body_callees_exact; rule body.reference_table)
  have included: "rra_carrier (object_structure body.body)\<subseteq>rra_carrier (object_structure frame.framed)"
    using frame.reads by (simp add: object_reads_agree_def)
  have bounds: "rel_dom body.literals\<union>rel_dom body.callees\<subseteq>rra_carrier (object_structure frame.framed)"
    by (rule subset_trans[OF body.reference_slots_inside included])
  show "rel_dom (map_relation_values decode_finite_object (fset (finite_schema_body_literals p ts)))\<union>
    rel_dom (fset (finite_schema_body_callees ts))\<subseteq>rra_carrier (object_structure (decode_finite_object R))"
    by (simp only: finite_schema_body_literals_exact finite_schema_body_callees_exact actual; rule bounds)
  show "\<forall>E u. environment_formed E \<longrightarrow> artifact_at E u (decode_finite_object R) \<longrightarrow>
    syntax_references E u (map_relation_values decode_finite_object (fset (finite_schema_body_literals p ts)))
      (fset (finite_schema_body_callees ts)) \<longrightarrow>
    native_schema_at E u r (schema_list_projection f ?p ss ?ts)"
  proof (intro allI impI)
    fix E u assume ef: "environment_formed E" and source: "artifact_at E u (decode_finite_object R)"
      and refs: "syntax_references E u (map_relation_values decode_finite_object (fset (finite_schema_body_literals p ts)))
        (fset (finite_schema_body_callees ts))"
    have code_source: "artifact_at E u frame.framed" using source by (simp only: actual)
    have references: "syntax_references E u body.literals body.callees" using refs by simp
    have read: "native_schema_at E u a (schema_list_projection f ?p es ?ts)"
      by (rule schema_syntax_recovers[OF body.schema_bodies_axioms frame.schema_frame_axioms lengths(2)
        sockets ef code_source references])
    show "native_schema_at E u r (schema_list_projection f ?p ss ?ts)"
      using read by (simp only: fields(2,3))
  qed
qed

export_code finite_schema_code checking SML

text \<open>
  The actual mixed body determines every fresh header and premise socket.
  Both the original existence proof and this executed frame use the same
  header decomposition and frame-construction theorem. The native reader
  recovers the complete resulting schema in its real reference environment.
\<close>

end
