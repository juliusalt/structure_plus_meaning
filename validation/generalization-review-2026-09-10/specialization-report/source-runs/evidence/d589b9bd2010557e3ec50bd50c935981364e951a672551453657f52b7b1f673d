theory Factor_Program_Semantics
  imports Factor_Program_Construction Factor_System_Alpha
begin

theorem rooted_native_program_preserves_meaning:
  fixes P :: "('a,'s,local_address option definition_site,'c) schema_system"
  assumes formed: "schema_system_formed P" and roots: "\<forall>d\<in>system_definitions P. snd d = []"
  shows "\<exists>E. native_package_formed E (system_definitions P) \<and>
    positive_meaning (native_program E (system_definitions P)) = positive_meaning P"
  using rooted_native_program_variant[OF formed roots] system_alpha_positive_meaning by metis

text \<open>
  The constructed finite native program has exactly the independently defined
  meaning of the source system. The equality holds over all formed future
  arguments; its proof does not assume a derivation certificate or a semantic
  property of the compiler. Mutual recursion is included.
\<close>

end
