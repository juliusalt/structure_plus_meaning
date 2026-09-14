theory Factor_Finite_Source_Computation
  imports Factor_Finite_Native_Sources
begin

definition finite_source_computation where
  "finite_source_computation E u r f=(case finite_native_source E u r of None \<Rightarrow> None
    | Some P \<Rightarrow> map_option (Pair P) (f P))"

theorem finite_source_computation_exact:
  "finite_source_computation E u r f=Some (P,x) \<longleftrightarrow>
    native_package_at (decode_finite_environment E) u r (decode_finite_system P) \<and> f P=Some x"
  by (auto simp: finite_source_computation_def finite_native_source_correct[symmetric] split: option.splits)

theorem finite_source_computation_projection:
  "map_option (map_prod id h) (finite_source_computation E u r f)=
    finite_source_computation E u r (\<lambda>P. map_option h (f P))"
  by (cases "finite_native_source E u r")
    (simp_all add: finite_source_computation_def option.map_comp comp_def)

text \<open>
  The actual complete source reader supplies the program for a partial
  computation. A successful result retains that same program and the exact
  original native package reading. Projection preserves the shared source
  contract without adding a supplied program or a satisfaction claim.
\<close>

end
