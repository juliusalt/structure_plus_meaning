theory Native_Child_Presentation
  imports Finite_Presented_Reasoning Finite_Term_Words Inference_Claim_Execution Finite_Keyed_Fibre_Values
    Factor_Finite_Child_Premises Factor_Prefixed_Observation_Execution
begin

section \<open>The child claim table and its controls\<close>

definition child_site_term :: "local_address option \<Rightarrow> local_address \<Rightarrow> finite_factor_term" where
  "child_site_term u a=Finite_Pair (the (finite_self_contained_term (use_data_term u))) (Finite_Payload a)"

definition child_owner :: finite_factor_term where
  "child_owner=the (finite_self_contained_term (use_data_term (Some [2])))"

definition child_callee where "child_callee=child_site_term (Some [2]) [1]"
definition child_parent_key where "child_parent_key=child_site_term (Some []) []"
definition child_child_key where "child_child_key=child_site_term (Some [1]) []"
definition child_premise_key where "child_premise_key=child_site_term (Some [2]) [24]"

definition child_claim :: "finite_factor_term \<Rightarrow> finite_factor_term" where
  "child_claim callee=Finite_Pair callee (Finite_Pair (Finite_Payload []) (Finite_Payload []))"

definition child_table :: "(finite_factor_term\<times>finite_factor_term) list \<Rightarrow> finite_factor_term" where
  "child_table rows=finite_data_list (map (\<lambda>(k,v). Finite_Pair k v) rows)"

definition child_claim_rows where
  "child_claim_rows=[(child_parent_key,child_claim child_callee),(child_child_key,child_claim child_callee)]"

definition child_discharge_rows where
  "child_discharge_rows=[(child_premise_key,child_child_key)]"

definition child_ordinary_rows where
  "child_ordinary_rows=[(Finite_Payload [24],Finite_Pair child_callee (Finite_Payload []))]"

definition child_table_controls :: "(finite_factor_term\<times>finite_factor_term) list list" where
  "child_table_controls=(let
      parent=(child_parent_key,child_claim child_callee);
      wrong_pattern=Finite_Pair child_callee (Finite_Pair (Finite_Payload [9]) (Finite_Payload [9]));
      wrong_callee=child_claim (child_site_term (Some [2]) [9])
    in [child_claim_rows,[parent],[parent,(child_child_key,wrong_pattern)],[parent,(child_child_key,wrong_callee)],
      child_claim_rows@[(child_child_key,child_claim child_callee)],child_claim_rows@[(Finite_Payload [200],Finite_Payload [256])],
      [(child_parent_key,wrong_pattern),(child_child_key,child_claim child_callee)],rev child_claim_rows,
      child_claim_rows@[(Finite_Payload [200],Finite_Payload [])]])"

definition child_row_fields :: "finite_factor_term \<Rightarrow> (finite_factor_term\<times>finite_factor_term) option" where
  "child_row_fields t=(case t of Finite_Pair k v \<Rightarrow> Some (k,v) | _ \<Rightarrow> None)"

definition child_projected_comparison :: "finite_factor_term list \<Rightarrow> bool" where
  "child_projected_comparison xs=(case those (map child_row_fields xs) of None \<Rightarrow> False
    | Some rows \<Rightarrow> finite_keyed_table_comparison rows child_ordinary_rows)"

definition child_table_control where
  "child_table_control rows=(let
      values=finite_key_fibre_values child_child_key rows;
      joined=(case values of [v] \<Rightarrow> [Finite_Pair child_premise_key v] | _ \<Rightarrow> []);
      projected=finite_prefixed_observation_outputs child_owner joined;
      (left,right)=(case projected of Some p \<Rightarrow> p | None \<Rightarrow> ([],[]));
      calls=[(21::nat,child_table rows),
        (28,Finite_Pair child_parent_key (Finite_Pair (child_table rows) (finite_data_list [child_claim child_callee]))),
        (28,Finite_Pair child_child_key (Finite_Pair (child_table rows) (finite_data_list values))),
        (358,Finite_Pair child_owner (Finite_Pair (finite_data_list joined)
          (Finite_Pair (finite_data_list left) (finite_data_list right)))),
        (353,Finite_Pair (finite_data_list left) (child_table child_ordinary_rows)),
        (353,Finite_Pair (finite_data_list right) (child_table child_ordinary_rows))];
      truth=[finite_keyed_table_comparison rows rows,
        finite_key_fibre_holds child_parent_key rows [child_claim child_callee],
        finite_key_fibre_holds child_child_key rows values,projected\<noteq>None,
        child_projected_comparison left,child_projected_comparison right];
      join=(100::nat,Finite_Pair (child_table rows) (Finite_Pair (child_table child_discharge_rows) (finite_data_list joined)))
    in (rows,values,joined,(left,right),calls,truth,join,list_all id truth \<and> length values=1))"

section \<open>The source reader application, fibres and guided constructions\<close>

definition child_application_problem where
  "child_application_problem=(let
      source=finite_child_inference_value []; control=child_table_control child_claim_rows;
      calls=fst (snd (snd (snd (snd control)))); join=fst (snd (snd (snd (snd (snd (snd control))))))
    in map_option (\<lambda>(S,ps). make_application_problem 359 S ps (fset_of_list ((350,source)#join#calls))
      {|(359,Finite_Pair source (child_table child_claim_rows))|} {||})
      (map_of inference_claim_construction_library 359))"

definition child_fibre_controls :: "(finite_factor_term\<times>(finite_factor_term\<times>finite_factor_term) list) list" where
  "child_fibre_controls=[(child_child_key,child_claim_rows),(Finite_Payload [200],child_claim_rows),
    (child_child_key,child_claim_rows@[(child_child_key,child_claim child_callee)]),
    (child_child_key,child_claim_rows@[(Finite_Payload [201],Finite_Payload [256])]),
    (Finite_Payload [256],[(Finite_Payload [256],Finite_Payload [])])]"

definition child_guided_case where
  "child_guided_case omitted rounds known control=(let
      source=finite_child_inference_value [];
      (rows,values,joined,projection,calls,truth,join,local)=control;
      L=filter (\<lambda>(d,row). d\<notin>set omitted) inference_claim_construction_library;
      frontier=finite_child_inference_known []@[(350,source),join]@calls;
      goals=[(0::nat,350::nat,source),(1,359,Finite_Pair source (child_table rows))];
      requested=map snd goals
    in (omitted,rounds,known,natural_guided_investigation rounds L frontier (fset_of_list known) (fset_of_list goals),
      map (\<lambda>j. natural_guided_state j L (fset_of_list frontier) (fset_of_list requested)) [0..<rounds+2]))"

definition child_positive_calls where
  "child_positive_calls control=(case control of (rows,values,joined,projection,calls,truth,join,local) \<Rightarrow>
    map fst (filter snd (zip calls truth)))"

definition child_guided_cases where
  "child_guided_cases=(let
      controls=map child_table_control child_table_controls; base=hd controls;
      known=finite_child_inference_known []@child_positive_calls base;
      child_fibre=fst (snd (snd (snd (snd base)))) ! 2
    in map (\<lambda>c. child_guided_case [] 3 (finite_child_inference_known []@child_positive_calls c) c) controls@
      [child_guided_case [] 0 known base,child_guided_case [] 2 known base,
       child_guided_case [] 3 (filter (\<lambda>q. fst q\<noteq>94) known) base,
       child_guided_case [] 3 (filter (\<lambda>q. q\<noteq>child_fibre) known) base,
       child_guided_case [] 3 (finite_literal_inference_known []@child_positive_calls base) base,
       child_guided_case [] 3 [] base]@
      map (\<lambda>d. child_guided_case [d] 3 known base) [350,100,359])"

section \<open>Paired projections over complete declared values\<close>

definition child_projection_owner :: finite_factor_term where
  "child_projection_owner=Finite_Payload [3]"

definition child_projection_target :: finite_factor_term where
  "child_projection_target=Finite_Target (Finite_Whole finite_empty_artifact)"

definition child_projection_row where
  "child_projection_row a d x y=Finite_Pair (Finite_Pair child_projection_owner a) (Finite_Pair d (Finite_Pair x y))"

definition child_projection_values :: "finite_factor_term list" where
  "child_projection_values=[Finite_Payload [7],child_projection_target,Finite_Pair (Finite_Payload [9]) child_projection_target]"

definition child_projection_rows :: "finite_factor_term list" where
  "child_projection_rows=map (\<lambda>(i,(x,y)). child_projection_row (Finite_Payload [i]) (Finite_Payload [11]) x y)
    (enumerate 0 (concat (map (\<lambda>x. map (Pair x) child_projection_values) child_projection_values)))"

definition child_projection_cases :: "(finite_factor_term\<times>finite_factor_term list) list" where
  "child_projection_cases=(let owner=child_projection_owner; target=child_projection_target; rows=child_projection_rows;
      large=map (\<lambda>i. child_projection_row (Finite_Payload [i div 256,i mod 256]) (Finite_Payload [i mod 7])
        (child_projection_values!(i mod 3)) (child_projection_values!((i+1) mod 3))) [0..<512]
    in [(owner,[])]@map (\<lambda>r. (owner,[r])) rows@
      [(owner,rows),(owner,rev rows),(owner,[hd rows,hd rows]),
       (owner,[child_projection_row (Finite_Payload [0]) (Finite_Payload [11]) target (Finite_Payload [9]),
         child_projection_row (Finite_Payload [1]) (Finite_Payload [12]) target (Finite_Payload [9])]),
       (Finite_Payload [4],[hd rows]),
       (owner,[Finite_Pair (Finite_Pair (Finite_Payload [4]) (Finite_Payload [0]))
         (Finite_Pair (Finite_Payload [11]) (Finite_Pair target (Finite_Payload [9])))]),
       (owner,[Finite_Pair (Finite_Pair owner (Finite_Payload [0])) (Finite_Pair target (Finite_Payload [9]))]),
       (owner,[Finite_Pair (Finite_Pair owner (Finite_Payload [0])) (Finite_Payload [7])]),
       (Finite_Payload [256],[]),
       (owner,[child_projection_row (Finite_Payload [256]) (Finite_Payload [11]) target (Finite_Payload [9])]),
       (owner,[child_projection_row (Finite_Payload [0]) (Finite_Payload [256]) target (Finite_Payload [9])]),
       (owner,[child_projection_row (Finite_Payload [0]) (Finite_Payload [11]) (Finite_Payload [256]) (Finite_Payload [9])]),
       (owner,[child_projection_row (Finite_Payload [0]) (Finite_Payload [11]) target (Finite_Payload [256])]),
       (owner,rows@[Finite_Payload [256]]),(target,[]),(owner,large),(owner,rev large)])"

section \<open>The complete native child report\<close>

definition native_child_presented_report where
  "native_child_presented_report cases=(
    (inference_claim_construction_library,inference_reader_investigation_library,keyed_table_construction_library),
    (finite_literal_inference_value [],finite_literal_inference_known []),
    map (\<lambda>(u,rs). (u,rs,finite_prefixed_observation_outputs u rs)) cases,
    (finite_child_inference_value [],finite_child_claim_value [],finite_child_inference_known []),
    map child_table_control child_table_controls,
    map_option (\<lambda>P. (P,application_construction_result Joined_Application_Observations P)) child_application_problem,
    map (\<lambda>(k,rows). (k,rows,finite_key_fibre_values k rows,
      finite_key_fibre_holds k rows (finite_key_fibre_values k rows))) child_fibre_controls,
    child_guided_cases)"

definition finite_child_call_value :: "nat\<times>finite_factor_term \<Rightarrow> finite_factor_term" where
  "finite_child_call_value=finite_coordinate_call_value finite_natural_data"

definition finite_child_control_value where
  "finite_child_control_value=finite_pair_presentation (finite_sequence_presentation (finite_pair_presentation id id))
    (finite_pair_presentation (finite_sequence_presentation id) (finite_pair_presentation (finite_sequence_presentation id)
      (finite_pair_presentation (finite_pair_presentation (finite_sequence_presentation id) (finite_sequence_presentation id))
        (finite_pair_presentation (finite_sequence_presentation finite_child_call_value)
          (finite_pair_presentation (finite_sequence_presentation finite_boolean_data)
            (finite_pair_presentation finite_child_call_value finite_boolean_data))))))"

definition finite_child_guided_case_value where
  "finite_child_guided_case_value=finite_pair_presentation finite_index_sequence_value
    (finite_pair_presentation finite_natural_data (finite_pair_presentation (finite_sequence_presentation finite_child_call_value)
      (finite_pair_presentation finite_guided_result_value (finite_sequence_presentation finite_guided_state_value))))"

definition finite_native_child_packet_value where
  "finite_native_child_packet_value=finite_pair_presentation
    (finite_pair_presentation finite_natural_library_value (finite_pair_presentation finite_natural_library_value
      finite_natural_library_value))
    (finite_pair_presentation (finite_pair_presentation id (finite_sequence_presentation finite_child_call_value))
      (finite_pair_presentation (finite_sequence_presentation (finite_pair_presentation id (finite_pair_presentation
          (finite_sequence_presentation id)
          (finite_option_presentation (finite_pair_presentation (finite_sequence_presentation id)
            (finite_sequence_presentation id))))))
        (finite_pair_presentation (finite_pair_presentation id (finite_pair_presentation id
            (finite_sequence_presentation finite_child_call_value)))
          (finite_pair_presentation (finite_sequence_presentation finite_child_control_value)
            (finite_pair_presentation (finite_option_presentation (finite_pair_presentation finite_application_problem_value
                (finite_collection_presentation finite_natural_application_value)))
              (finite_pair_presentation (finite_sequence_presentation (finite_pair_presentation id
                  (finite_pair_presentation (finite_sequence_presentation (finite_pair_presentation id id))
                    (finite_pair_presentation (finite_sequence_presentation id) finite_boolean_data))))
                (finite_sequence_presentation finite_child_guided_case_value)))))))"

lemma finite_native_child_values_injective [intro]:
  "inj finite_child_call_value" "inj finite_child_control_value" "inj finite_child_guided_case_value"
  "inj finite_native_child_packet_value"
  unfolding finite_child_call_value_def finite_child_control_value_def finite_child_guided_case_value_def
    finite_native_child_packet_value_def
  by (intro finite_pair_presentation_injective finite_sequence_presentation_injective inj_on_id
      finite_coordinate_call_value_injective finite_natural_data_injective finite_boolean_data_injective
      finite_index_values_injective finite_reasoning_values_injective finite_option_presentation_injective
      finite_collection_presentation_injective)+

definition native_child_report_value where
  "native_child_report_value cases=finite_native_child_packet_value (native_child_presented_report cases)"

theorem native_child_report_word_exact:
  "finite_term_shared_word (native_child_report_value cs)=finite_term_shared_word (native_child_report_value ds) \<longleftrightarrow>
    native_child_presented_report cs=native_child_presented_report ds"
  by (simp add: finite_term_shared_word_injective native_child_report_value_def
      inj_eq[OF finite_native_child_values_injective(4)])

text \<open>
  The native child report keeps the three compiled libraries, the literal source
  with its known calls, every declared paired projection, the child source,
  claim and known calls, every claim-table control with its fibre values, joins,
  projections, condition calls and truth, the source reader application problem
  and its constructed applications, every fibre control and every guided
  construction with its omitted entries, rounds, known calls, result and states.
  All controls and cases are definitions over the existing child example and
  its native operations; the host supplies no input or expected value.
\<close>

end
