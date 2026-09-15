theory Use_Codec_Execution
  imports RRA_Use_Codec_Investigation
begin

setup \<open>Finite_Observation_Contracts.export @{term use_codec_investigation}\<close>

export_code use_codec_packet use_codec_indices use_codec_inspect use_coordinate_bound use_path_budget
  length fset set nat_of_integer integer_of_nat
  in SML module_name Use_Codec_Execution file_prefix use_codec

end
