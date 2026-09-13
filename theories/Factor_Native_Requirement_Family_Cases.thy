theory Factor_Native_Requirement_Family_Cases
  imports Factor_Finite_Native_Requirements Factor_Native_Admission_Cases
    Factor_Finite_Requirement_Term_Observations
begin

type_synonym native_requirement_problem =
  "local_address option finite_artifact_environment\<times>local_address option\<times>local_address\<times>
    local_address option definition_site admission_goal list\<times>finite_factor_term fset"

definition native_requirement_shapes :: "(nat\<times>nat) list" where
  "native_requirement_shapes=concat (map (\<lambda>s. map (Pair s) [0..<10]) [0,1,4,5,8,9,10,11,12])"

definition native_requirement_family :: "nat\<Rightarrow>'d\<Rightarrow>'d\<Rightarrow>'d\<Rightarrow>'d admission_goal list" where
  "native_requirement_family k a b absent=(let x=Existing_Admission a; y=Existing_Admission b in
    if k=0 then [] else if k=1 then [x] else if k=2 then [x,y] else if k=3 then [x,x]
    else if k=4 then [Paired_Admission x y,Paired_Admission x x]
    else if k=5 then [Collected_Admission x,Collected_Admission y]
    else if k=6 then [Collected_Admission (Paired_Admission x y),Collected_Admission (Paired_Admission y x)]
    else if k=7 then [x,Collected_Admission x] else if k=8 then [Existing_Admission absent,x]
    else [x,Existing_Admission absent])"

definition native_requirement_samples where
  "native_requirement_samples B gs=ffUnion (fimage (admission_goal_samples B) (fset_of_list gs))"

definition native_requirement_problem :: "nat\<Rightarrow>native_requirement_problem option" where
  "native_requirement_problem w=(if w<length native_requirement_shapes then
    (case native_requirement_shapes!w of (s,k) \<Rightarrow> map_option (\<lambda>(E,u,r).
      native_source_goal_problem native_requirement_family native_requirement_samples k E u r
        (finsert (Finite_Payload [256]) program_evaluation_terms)) (native_admission_seed s)) else None)"

definition native_requirement_variant :: "nat\<Rightarrow>'g list\<Rightarrow>'g list" where
  "native_requirement_variant m gs=(if m=1 then tl gs else if m=2 then butlast gs
    else if m=3 then (case gs of [] \<Rightarrow> [] | g#rest \<Rightarrow> map (\<lambda>_. g) gs) else gs)"

lemma native_requirement_variant_original [simp]: "native_requirement_variant 0 gs=gs"
  by (simp only: native_requirement_variant_def; simp)

definition native_requirement_method :: "nat\<Rightarrow>native_requirement_problem\<Rightarrow>
    (local_address option definition_site\<times>local_address option finite_artifact_environment\<times>local_address option) option" where
  "native_requirement_method m X=(case X of (E,u,r,gs,T) \<Rightarrow>
    if m=5 \<or> (m=6 \<and> gs=[]) then None else
      map_option (\<lambda>(d,F,v). (d,(if m=4 then F\<lparr>finite_environment_artifacts:=
        ffilter (\<lambda>(a,A). a\<noteq>Some [255]) (finite_environment_artifacts F)\<rparr> else F),v))
        (finite_construct_source_requirements E u r (native_requirement_variant m gs)))"

lemma native_requirement_method_original:
  "native_requirement_method 0 (E,u,r,gs,T)=finite_construct_source_requirements E u r gs"
  by (cases "finite_construct_source_requirements E u r gs")
    (simp_all add: native_requirement_method_def split: prod.splits)

definition native_requirement_source_report where
  "native_requirement_source_report X=(case X of (E,u,r,gs,T) \<Rightarrow>
    let source=finite_native_source E u r;
      supported=(case source of None \<Rightarrow> False | Some P \<Rightarrow> finite_admission_requirements_supported gs P);
      D=(case source of None \<Rightarrow> {||} | Some P \<Rightarrow> finite_program_term_demand P T);
      evaluated=finite_native_program_evaluation E u r D
    in (source,supported,D,evaluated,
      map_option (\<lambda>(P,A). ffilter (finite_admission_requirements_test gs A) T) evaluated))"

definition native_requirement_target_report where
  "native_requirement_target_report X result=(case X of (E,u,r,gs,T) \<Rightarrow>
    native_entry_target_report u r T result)"

definition native_requirement_report where
  "native_requirement_report w=map_option (\<lambda>X. (X,native_requirement_source_report X,
    map (\<lambda>m. (m,native_requirement_target_report X (native_requirement_method m X))) [0,1,2,3,4,5,6]))
    (native_requirement_problem w)"

definition native_requirement_indices :: "nat list" where
  "native_requirement_indices=[0..<length native_requirement_shapes]"

export_code native_requirement_report native_requirement_indices checking SML

end
