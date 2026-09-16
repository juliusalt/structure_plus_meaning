theory Native_Admission_Execution_Base
  imports Factor_Native_Admission_Cases
begin

definition native_admission_indices :: "nat list" where
  "native_admission_indices=[0..<length native_admission_shapes]"

end
