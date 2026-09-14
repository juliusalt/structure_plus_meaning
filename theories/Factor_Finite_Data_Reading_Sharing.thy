theory Factor_Finite_Data_Reading_Sharing
  imports Factor_Finite_Prepared_Data_Readings
begin

declare finite_complete_data_readings_def[code del]

lemma finite_complete_data_readings_shared_code [code]:
  "finite_complete_data_readings C r=finite_complete_data_readings_prepared C r"
  by (rule finite_complete_data_readings_prepared_exact[symmetric])

text \<open>
  The selected preparation method has the same complete result on every input.
  This code equation changes execution of the existing operation while its
  original quotation relation and all caller contracts remain the same.
\<close>

end
