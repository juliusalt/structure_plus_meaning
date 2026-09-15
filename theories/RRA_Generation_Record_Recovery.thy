theory RRA_Generation_Record_Recovery
  imports RRA_Generation_Record_Construction RRA_Generation_References
begin

locale generation_record_recovery =
  fixes E H :: "'u artifact_environment" and u :: 'u
    and l p c :: exact_target and as :: "(exact_artifact\<times>local_address) list"
    and v :: "nat\<Rightarrow>'u"
  assumes formed: "environment_formed H" and included: "environment_included E H"
    and fields: "generation_fields_at H u [] l (generation_frame_members (length as)) p c"
    and locations: "\<forall>i<length as. located_at H u (generation_predecessor_node i) (v i) (snd (as!i))"
begin

theorem predecessor_references:
  "generation_predecessor_references H u [] l p c=
    {(v i,snd (as!i)) | i. i<length as}"
proof -
  have rows: "generation_frame_members (length as)=
    {(generation_predecessor_socket (length as) i,generation_predecessor_node i) | i. i\<in>{..<length as}}"
    by (auto simp: generation_frame_members_def)
  have at: "located_at H u (generation_predecessor_node i) (v i) (snd (as!i))"
    if "i\<in>{..<length as}" for i using locations that by simp
  show ?thesis using generation_predecessor_references_indexed[OF fields rows at] by simp
qed

theorem recovers:
  assumes distinct: "inj_on g {..<length as}"
    and predecessors: "\<forall>i<length as. generation_at E (v i) (snd (as!i)) (g i)"
  shows "generation_at H u [] (Generation l (Abs_fset (g ` {..<length as})) p c)"
proof -
  let ?n="length as"
  obtain h where hinj: "inj_on h (rel_dom (generation_frame_members ?n))"
    and hat: "\<forall>i<?n. h (generation_predecessor_socket ?n i)=g i"
    and hvalues: "h ` rel_dom (generation_frame_members ?n)=g ` {..<?n}"
    using generation_predecessor_assignment[OF distinct] by blast
  have refs: "\<forall>s d. (s,d)\<in>generation_frame_members ?n \<longrightarrow>
    (\<exists>w b. located_at H u d w b \<and> generation_at H w b (h s))"
  proof (intro allI impI)
    fix s d assume edge: "(s,d)\<in>generation_frame_members ?n"
    obtain i where index: "i<?n" and s: "s=generation_predecessor_socket ?n i"
      and d: "d=generation_predecessor_node i" using edge by (auto simp: generation_frame_member)
    have old: "generation_at E (v i) (snd (as!i)) (g i)" using predecessors index by blast
    have kept: "generation_at H (v i) (snd (as!i)) (g i)"
      by (rule generation_at_included[OF old included formed])
    have same: "h s=g i" using hat index s by simp
    show "\<exists>w b. located_at H u d w b \<and> generation_at H w b (h s)"
      by (rule exI[of _ "v i"], rule exI[of _ "snd (as!i)"])
        (use locations[rule_format, OF index] kept in \<open>simp only: d same; blast\<close>)
  qed
  show ?thesis using generation_at.generation[OF fields hinj refs] by (simp only: hvalues)
qed

end

context generation_record_construction
begin

sublocale recovery: generation_record_recovery E installed record_use l p c as v
  by (rule generation_record_recovery.intro[OF properties])

end

text \<open>
  Exact predecessor recovery depends on complete fields, locations, inclusion,
  formation and the original injective predecessor assignment. It is independent
  of the allocator, embedding and installation operation that established them.
\<close>

end
