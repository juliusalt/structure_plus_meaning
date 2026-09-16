theory Finite_Directed_Execution_Base
  imports Finite_Directed_Contributions Finite_Candidate_Assembly "HOL-Library.Code_Target_Nat"
begin

definition natural_directed_bindings where
  "natural_directed_bindings (scope::nat fset) (B::((nat\<times>nat) fset) fset)=
    finite_scoped_compatible_unions scope B"

definition natural_candidate_assembly where
  "natural_candidate_assembly (As::nat list) (Ps::nat list) (coverage::(nat\<times>nat) fset)=
    finite_construct_candidate As Ps (\<lambda>p. fimage snd (ffilter (\<lambda>r. fst r=p) coverage))"

end
