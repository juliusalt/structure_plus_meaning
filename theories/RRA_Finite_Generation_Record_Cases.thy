theory RRA_Finite_Generation_Record_Cases
  imports RRA_Finite_Generation_Construction
begin

type_synonym generation_record_problem =
  "local_address option finite_artifact_environment \<times> finite_exact_target \<times>
    finite_exact_target \<times> finite_exact_target \<times>
    (local_address option definition_site\<times>finite_generation) list"

type_synonym generation_record_result =
  "local_address option finite_artifact_environment \<times> local_address option \<times> finite_generation"

type_synonym generation_record_fixture =
  "local_address option definition_site\<times>finite_exact_artifact\<times>finite_generation"

definition generation_fixture_row where
  "generation_fixture_row z=(case z of (d,R,G) \<Rightarrow> (d,G))"

definition generation_fixture_append ::
  "local_address option finite_artifact_environment \<Rightarrow> finite_exact_target \<Rightarrow>
    finite_exact_target \<Rightarrow> finite_exact_target \<Rightarrow> generation_record_fixture list \<Rightarrow>
    local_address option finite_artifact_environment\<times>generation_record_fixture" where
  "generation_fixture_append E l p c zs=(let
    anchors=map (\<lambda>(d,R,G). (R,snd d)) zs;
    uses=(\<lambda>i. fst (fst (zs!i)));
    F=finite_generation_record_environment E l p c anchors uses;
    u=finite_generation_record_use E;
    R=finite_generation_record_frame l p c anchors;
    G=finite_generation_record_core l p c (map generation_fixture_row zs)
    in (F,((u,[]),R,G)))"

definition generation_record_case :: "nat\<Rightarrow>generation_record_problem" where
  "generation_record_case w=(let
    l=Finite_Whole (finite_payload_syntax [21]);
    p=Finite_Whole (finite_payload_syntax [22]);
    c=Finite_Whole (finite_payload_syntax [23]);
    empty=finite_enumerated_environment [] [];
    initial=finite_enumerated_environment [(None,finite_payload_syntax [31]),
      (Some [9],finite_payload_syntax [32])] [((None,[]),Some [9])];
    first=generation_fixture_append initial l p c [];
    second=generation_fixture_append (fst first) l (Finite_Whole (finite_payload_syntax [24])) c [snd first];
    third=generation_fixture_append (fst second) l (Finite_Whole (finite_payload_syntax [25])) c [snd first];
    duplicate=generation_fixture_append (fst third) l p c [];
    row=generation_fixture_row;
    old=fst third;
    one=row (snd first);
    two=row (snd second);
    three=row (snd third)
    in if w=0 then (empty,l,p,c,[])
    else if w=1 then (initial,l,p,c,[])
    else if w=2 then (fst first,l,p,c,[one])
    else if w=3 then (fst second,l,p,c,[two])
    else if w=4 then (old,l,p,c,[two,three])
    else if w=5 then (old,l,p,c,[one,two,three])
    else if w=6 then (fst duplicate,l,p,c,[one,row (snd duplicate)])
    else if w=7 then (old,Finite_Anchor (finite_payload_syntax [21]) [8],p,c,[one])
    else if w=8 then (old,l,p,Finite_Whole (finite_payload_syntax [256]),[one])
    else if w=9 then (old,l,p,c,[(fst one,snd two)])
    else if w=10 then (old,l,p,c,[((Some [99],[]),snd one)])
    else if w=11 then (finite_add_artifact_use old None (finite_payload_syntax [33]),l,p,c,[one])
    else if w=12 then (old,l,p,c,[((fst (fst one),[99]),snd one)])
    else if w=13 then (fst duplicate,l,p,c,[row (snd duplicate)])
    else if w=14 then (old,l,p,c,[three,two])
    else (old,l,p,c,[one,one]))"

definition generation_record_base :: "generation_record_problem\<Rightarrow>generation_record_result option" where
  "generation_record_base X=(case X of (E,l,p,c,rows) \<Rightarrow>
    finite_construct_generation_record E l p c rows)"

definition generation_record_variant :: "nat\<Rightarrow>generation_record_problem\<Rightarrow>generation_record_result option" where
  "generation_record_variant m X=(case X of (E,l,p,c,rows) \<Rightarrow>
    if m=1 then finite_construct_generation_record E l p c (rev rows)
    else if m=3 then finite_construct_generation_record E (Finite_Whole (finite_payload_syntax [41])) p c rows
    else if m=4 then finite_construct_generation_record E l (Finite_Whole (finite_payload_syntax [42])) c rows
    else if m=5 then finite_construct_generation_record E l p (Finite_Whole (finite_payload_syntax [43])) rows
    else if m=6 then finite_construct_generation_record E l p c (tl rows)
    else generation_record_base X)"

definition generation_record_alias_target where
  "generation_record_alias_target E b=finite_singleton_option (fimage fst
    (ffilter (\<lambda>(v,R). v\<noteq>b \<and> R |\<in>| finite_artifacts_at E b)
      (finite_environment_artifacts E)))"

definition generation_record_mutation ::
  "nat\<Rightarrow>generation_record_problem\<Rightarrow>generation_record_result option\<Rightarrow>generation_record_result option" where
  "generation_record_mutation (m::nat) X result=(case X of (E,l,p,c,rows) \<Rightarrow>
    if m=2 then None else map_option (\<lambda>(F,u,G).
      (if m=7 then F\<lparr>finite_environment_bindings:={||}\<rparr>
        else if m=8 then F\<lparr>finite_environment_artifacts:=
          ffilter (\<lambda>(v,R). v\<noteq>None) (finite_environment_artifacts F)\<rparr>
        else if m=9 then F\<lparr>finite_environment_bindings:=
          fimage (\<lambda>((v,k),b). ((v,k),if v=u \<and> k=generation_predecessor_slot 0 then u else b))
            (finite_environment_bindings F)\<rparr>
        else if m=11 then F\<lparr>finite_environment_bindings:=
          fimage (\<lambda>((v,k),b). ((v,k),if v=u \<and> k=generation_predecessor_slot 0 then
            (case generation_record_alias_target E b of None \<Rightarrow> b | Some a \<Rightarrow> a) else b))
            (finite_environment_bindings F)\<rparr>
        else if m=12 then F\<lparr>finite_environment_artifacts:=
          ffilter (\<lambda>(v,R). v\<noteq>Some [9]) (finite_environment_artifacts F),
          finite_environment_bindings:=ffilter (\<lambda>((v,k),b). v\<noteq>Some [9] \<and> b\<noteq>Some [9])
            (finite_environment_bindings F)\<rparr>
        else F,
       u,if m=10 then Generation l {||} p c else G)) result)"

definition generation_record_method where
  "generation_record_method (m::nat) X=generation_record_mutation m X
    (generation_record_variant m X)"

lemma generation_record_method_original:
  "generation_record_method 0 (E,l,p,c,rows)=finite_construct_generation_record E l p c rows"
  by (simp add: generation_record_method_def generation_record_mutation_def
    generation_record_variant_def generation_record_base_def option.map_id split: option.splits)

text \<open>
  Fixture environments use the explicit frame and environment operations before
  the guarded candidate is called. They retain complete original sites, source
  artifacts and generation values. The cases include empty, chain and shared
  predecessor structures, equal cores at different uses, unrelated old bindings,
  malformed targets and sources, and incorrect predecessor claims. Reversing
  the predecessor presentation is an admissible candidate, not a change to the
  independently requested predecessor set or its actual original references.
\<close>

end
