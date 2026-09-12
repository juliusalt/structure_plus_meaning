theory Functional_Relation_Joins
  imports Bootstrap_Relations
begin

section \<open>A complete functional output is exactly the join of its links and values\<close>

theorem functional_relation_join_characterization:
  fixes Q :: "('s\<times>'v) set" and R :: "('s\<times>'n) set" and J :: "('n\<times>'v) set"
  assumes jsv: "single_valued J" and qsv: "single_valued Q"
    and covered: "rel_ran R\<subseteq>rel_dom J"
  shows "(rel_dom Q=rel_dom R \<and>
    (\<forall>s m. (s,m)\<in>R \<longrightarrow> (s,rel_value J m)\<in>Q)) \<longleftrightarrow> Q=R O J"
proof
  assume local: "rel_dom Q=rel_dom R \<and>
    (\<forall>s m. (s,m)\<in>R \<longrightarrow> (s,rel_value J m)\<in>Q)"
  have child: "(m,rel_value Q s)\<in>J" if edge: "(s,m)\<in>R" for s m
  proof -
    have key: "m\<in>rel_dom J" using covered rel_ranI[OF edge] by blast
    obtain v where row: "(m,v)\<in>J" using key by (auto simp: rel_dom_def)
    have lookup_value: "rel_value J m=v" by (rule rel_value_eq[OF jsv row])
    have result: "(s,v)\<in>Q" using local edge lookup_value by blast
    have selected: "rel_value Q s=v" by (rule rel_value_eq[OF qsv result])
    show ?thesis using row selected by simp
  qed
  show "Q=R O J" by (rule relation_join_recovers[OF qsv jsv conjunct1[OF local] child])
next
  assume joined: "Q=R O J"
  have domain: "rel_dom Q=rel_dom R" using relation_join_domain[OF covered] by (simp only: joined)
  have row: "(s,rel_value J m)\<in>Q" if edge: "(s,m)\<in>R" for s m
  proof -
    have key: "m\<in>rel_dom J" using covered rel_ranI[OF edge] by blast
    obtain v where child_row: "(m,v)\<in>J" using key by (auto simp: rel_dom_def)
    have selected: "rel_value J m=v" by (rule rel_value_eq[OF jsv child_row])
    show ?thesis using edge child_row joined selected by blast
  qed
  show "rel_dom Q=rel_dom R \<and> (\<forall>s m. (s,m)\<in>R \<longrightarrow> (s,rel_value J m)\<in>Q)"
    using domain row by blast
qed

text \<open>
  Every link target must have a value, and both value and output relations
  are functional. The links themselves need not be functional: several
  targets at one source key are permitted exactly when their resulting
  values agree. A missing target or an extra output key is not ignored.
\<close>

end
