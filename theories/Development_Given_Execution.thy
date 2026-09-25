theory Development_Given_Execution
  imports Development_Given_Installation Native_Execution_Refinements
begin

text \<open>
  The given's construction executed, over the native package reader's refinements, in a thin theory of its own
  so that a refinement's change rebuilds this theory alone: the readers' program (formation, definitions,
  payloads, and the rooted program's formation and definitions), then the development package's kept
  environment and the given's in addresses, and the definitions the native package reader reads back at the
  given's site.
\<close>

value "(finite_system_formed finite_given_readers, fcard (finite_system_definitions finite_given_readers),
  finite_system_payloads finite_given_readers, finite_system_formed finite_rooted_given_readers,
  fcard (finite_system_definitions finite_rooted_given_readers))"

value "(fcard (finite_environment_positions development_package_environment),
  fcard (finite_environment_positions given_environment),
  map_option (\<lambda>P. fcard (finite_system_definitions P)) (finite_native_source given_environment given_use []))"

end
