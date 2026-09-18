theory Native_Control_Definition_Diagnostic
  imports Native_Control_Finite_Guard
begin
thm quoted_judgment_rows.artifact_system_def quoted_judgment_rows.body_system_def
ML \<open>
val thy = @{theory};
val kernel = Isabelle_Constant_Closure.kernel_definitions thy;
val _ = List.app (fn (name,prop) => writeln (name ^ " : " ^ Syntax.string_of_term @{context} prop))
  (kernel @{const_name quoted_judgment_rows.artifact_system} @ kernel @{const_name quoted_judgment_rows.body_system});
\<close>
end
