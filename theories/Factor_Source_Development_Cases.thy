theory Factor_Source_Development_Cases
  imports Factor_Source_Development_Admission Factor_Source_Development_Input
begin

definition source_development_example_program where
  "source_development_example_program tagged=(let p=Finite_Variable [0];
    output=(if tagged then Finite_Pattern_Pair (Finite_Pattern_Payload [7]) p else Finite_Pattern_Pair p p);
    rule=\<lparr>finite_schema_conclusion=Finite_Pattern_Pair p output,
      finite_schema_premises={|([0],(None,[1]),p)|},finite_schema_materials={||}\<rparr>
    in finite_add_view_definition (finite_guard_source_program True) (Some [],[]) (Finite_Variable [])
      {|([],rule)|})"

definition source_development_case :: "nat \<Rightarrow> source_development_request" where
  "source_development_case i=(let
    E=(if i=3 then \<lparr>finite_environment_artifacts={||},finite_environment_bindings={||}\<rparr>
      else finite_guard_source (i\<noteq>4));
    Q=source_development_example_program False;
    target=(Q,if i=5 then (Some [99],[]) else (Some [],[]));
    targets=(if i=6 then [] else if i=1 then [target,target]
      else if i=2 then [target,(source_development_example_program True,(Some [],[]))] else [target]);
    x=Finite_Payload (if i=7 then [256] else [42]);
    y=Finite_Pair x x;
    ys=(if i=8 then [x] else if i=1 then [y,y,x]
      else [y,Finite_Pair (Finite_Payload [7]) x,x])
    in source_development_request_input E None [0] targets x ys)"

definition source_development_cases where
  "source_development_cases=map source_development_case [0..<9]"

definition source_development_report_controls :: "source_development_request \<Rightarrow> source_development_report \<Rightarrow>
    (nat\<times>source_development_report\<times>
      (source_development_proposal\<times>source_development_entry\<times>native_workflow_stage_result) option) list" where
  "source_development_report_controls R report=map (\<lambda>(i,actual).
      (i,actual,source_development_admission R actual))
    [(0,report),(1,report\<lparr>source_report_query:=None\<rparr>),
      (2,report\<lparr>source_report_installed:=None\<rparr>),
      (3,report\<lparr>source_report_proposals:=[]\<rparr>)]"

text \<open>The complete source-change inputs exercise a new native pair-producing
  definition, repeated target occurrences and repeated query answers, two
  distinct adequate target programs, an unreadable source, changed original
  source meaning, an absent target entry, no requested target, a malformed
  subsequent query, and a completed empty answer. Report controls remove the
  query, installation or original proposal scope and run the same admission
  again. They supply no expected satisfaction or acceptance fields.\<close>

end
