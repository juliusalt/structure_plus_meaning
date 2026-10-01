theory Factor_Extension_Registrations
  imports Factor_Extension_Packages Factor_Reader_Witness_Registrations
begin

section \<open>The bound of an added site's closure\<close>

text \<open>
  AX2b of task 928's course (c), G2: the added part's bound (960's premise-only variable 3) registered in W2's
  family form and complete in W4a's. The family is 77's (@{const closure_witness_family}) at 960's clause, its
  environment the least environment l (variable 0) and its roots q (variable 2): base the roots selected (5), step
  the edges read in l (82). Under F\<Prime> of task 959 a site that passes 958 as a given site has no binding at its use
  in l and l's row there is the given's, so an edge from it is local and stays inside its closure in the given,
  whose sites pass as given sites too (@{text bounded_given_edge}). So the reach over l's edges from q is a bound
  whenever any bound is (@{text extension_bound_reach_passes}), although it need not lie inside every bound; the
  registration is complete (@{text extension_bound_registration_complete_in}). It is read by the construction alone.
\<close>

subsection \<open>A site that passes as a given site, and its local edges\<close>

abbreviation bounded_given_raw :: "factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> factor_term \<Rightarrow> bool" where
  "bounded_given_raw l g gu gr x \<equiv> \<exists>lw lb du dr R rest. l=Pair_Term lw lb \<and> x=Pair_Term du dr \<and>
    term_formed R \<and> term_formed rest \<and>
    (963,Pair_Term du lb)\<in>positive_meaning extension_package_system \<and>
    (5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system \<and>
    (37,Pair_Term g (Pair_Term du R))\<in>positive_meaning artifact_lookup_system \<and>
    ((83,package_subject_argument g gu gr x)\<in>positive_meaning package_membership_system \<or>
     (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system)"

lemma edge_answers_source:
  assumes edge: "(x,e)\<in>edge_answers (positive_meaning definition_edge_reading_system) l"
  obtains L dx de where "environment_value_presents L l" "x=definition_site_value dx" "e=definition_site_value de"
    "(dx,de)\<in>native_definition_edges L"
proof -
  have "\<exists>L. environment_value_presents L l"
  proof (rule ccontr)
    assume absent: "\<not>(\<exists>L. environment_value_presents L l)"
    have "edge_answers (positive_meaning definition_edge_reading_system) l={}"
      by (rule edge_answers_absent[of definition_edge_reading_system, OF refl absent])
    then show False using edge by blast
  qed
  then obtain L where least: "environment_value_presents L l" by blast
  obtain dx de where "x=definition_site_value dx" "e=definition_site_value de" "(dx,de)\<in>native_definition_edges L"
    using edge edge_answers_exact[of definition_edge_reading_system, OF refl least] by auto
  then show ?thesis using least that by blast
qed

lemma edge_answers_target_data:
  assumes edge: "(x,e)\<in>edge_answers (positive_meaning definition_edge_reading_system) l"
  shows "term_formed e \<and> self_contained_term e"
proof -
  obtain L dx de where ends: "e=definition_site_value de" by (rule edge_answers_source[OF edge])
  have call: "(82,Pair_Term l (Pair_Term x e))\<in>positive_meaning definition_edge_reading_system" using edge by simp
  have "term_formed (Pair_Term l (Pair_Term x e))"
    using schema_call_formed_target[OF positive_meaning_formed[OF call]] by simp
  then show ?thesis using ends by (simp add: site_data_term_def)
qed

lemma bounded_given_edge:
  assumes given: "bounded_given_raw l g gu gr x"
    and edge: "(x,e)\<in>edge_answers (positive_meaning definition_edge_reading_system) l"
  shows "bounded_given_raw l g gu gr e"
proof -
  obtain lw lb du dr R rest where parts: "l=Pair_Term lw lb" "x=Pair_Term du dr" "term_formed R" "term_formed rest"
    "(963,Pair_Term du lb)\<in>positive_meaning extension_package_system"
    "(5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system"
    "(37,Pair_Term g (Pair_Term du R))\<in>positive_meaning artifact_lookup_system"
    and calls: "(83,package_subject_argument g gu gr x)\<in>positive_meaning package_membership_system \<or>
      (77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
    using given by blast
  obtain L dx de where least: "environment_value_presents L l" and ends: "x=definition_site_value dx"
      "e=definition_site_value de" "(dx,de)\<in>native_definition_edges L"
    by (rule edge_answers_source[OF edge])
  obtain p C c S where read: "native_definition_at L (fst dx) (snd dx) p C" "(c,S)\<in>C" "de\<in>schema_dependencies S"
    using ends(3) by (auto simp: native_definition_edges_def)
  have du: "du=use_data_term (fst dx)" using parts(2) ends(1) by (simp add: site_data_term_def)
  have sf: "term_formed (site_data_term (fst dx) (snd dx))" by (rule native_definition_site_data_formed[OF read(1)])
  have key: "term_formed (use_data_term (fst dx))" "self_contained_term (use_data_term (fst dx))"
    using sf site_data_term_self_contained[of "fst dx" "snd dx"] by (simp_all add: site_data_term_def)
  have unbound: "\<forall>u k w. binds_slot L u k w \<longrightarrow> u\<noteq>fst dx"
    using source_absences_at_values[OF least[unfolded parts(1)] key] parts(5) du by simp
  have same_use: "fst de=fst dx"
    using native_definition_edge_uses[OF ends(3)] unbound by (auto simp: environment_edges_def)
  have e_parts: "e=Pair_Term du (Payload_Term (snd de))" using ends(2) same_use du by (simp add: site_data_term_def)
  obtain E e0 u0 R2 a0 where lookup: "Pair_Term g (Pair_Term du R)=artifact_lookup_argument e0 (use_data_term u0) a0"
      "environment_value_presents E e0" "artifact_at E u0 R2" "artifact_value_presents R2 a0"
    using parts(7) unfolding artifact_lookup_exact by blast
  have gE: "environment_value_presents E g" and u0: "u0=fst dx" and a0: "a0=R"
    using lookup du by (auto dest: injD[OF use_data_term_injective])
  have lf: "environment_formed L" using environment_value_presents_formed[OF least] by blast
  have ef: "environment_formed E" using environment_value_presents_formed[OF gE] by blast
  obtain q R1 where row: "du=use_data_term q" "artifact_at L q R1" "artifact_value_presents R1 R"
    using conjunct2[OF environment_artifact_selection[OF least[unfolded parts(1)]]] parts(6) by blast
  have q: "q=fst dx" using row(1) du by (auto dest: injD[OF use_data_term_injective])
  have same_artifact: "R1=R2" using artifact_value_presents_unique[OF row(3) lookup(4)[unfolded a0]] .
  let ?F="read_environment L {fst dx} {}"
  have boundary: "read_boundary_formed L {fst dx} {}"
    using lf row(2) q by (auto simp: read_boundary_formed_def environment_uses_def artifact_at_def rel_dom_def)
  have slots: "\<forall>k\<in>native_definition_slots L (fst dx) (snd dx). (fst dx,k)\<in>({}::(local_address option\<times>local_address) set)"
  proof
    fix k assume "k\<in>native_definition_slots L (fst dx) (snd dx)"
    then have "(fst dx,k)\<in>rel_dom (environment_bindings L)" by (rule native_definition_slots_bound)
    then obtain v where "binds_slot L (fst dx) k v" by (auto simp: rel_dom_def binds_slot_def)
    then show "(fst dx,k)\<in>({}::(local_address option\<times>local_address) set)" using unbound by blast
  qed
  have readF: "native_definition_at ?F (fst dx) (snd dx) p C"
    by (rule native_definition_read_environment(1)[OF read(1) boundary _ slots]) simp
  have included: "environment_included ?F E"
    unfolding environment_included_def
  proof (intro conjI subsetI)
    fix z assume z: "z\<in>environment_artifacts ?F"
    obtain v T where zv: "z=(v,T)" by (cases z)
    have "artifact_at ?F v T" using z zv by (simp add: artifact_at_def)
    then have v: "v=fst dx" "artifact_at L v T" by (auto simp: read_environment_uses_def)
    have "T=R1" using environment_artifact_unique[OF lf v(2)] row(2) q v(1) by blast
    then show "z\<in>environment_artifacts E" using lookup(3) u0 same_artifact v(1) zv by (simp add: artifact_at_def)
  next
    fix z assume z: "z\<in>environment_bindings ?F"
    obtain v k w where zv: "z=((v,k),w)" by (cases z) auto
    have "binds_slot ?F v k w" using z zv by (simp add: binds_slot_def)
    then show "z\<in>environment_bindings E" by simp
  qed
  have readE: "native_definition_at E (fst dx) (snd dx) p C" by (rule native_definition_included[OF readF included ef])
  have edgeE: "(dx,de)\<in>native_definition_edges E" using readE read(2,3) by (auto simp: native_definition_edges_def)
  have reached: "de\<in>native_definition_sites E {dx}"
    by (rule native_definition_step[OF subsetD[OF native_definition_roots] edgeE]) simp
  have e_calls: "(83,package_subject_argument g gu gr e)\<in>positive_meaning package_membership_system \<or>
      (77,Pair_Term g (Pair_Term e (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
    using calls
  proof
    assume "(83,package_subject_argument g gu gr x)\<in>positive_meaning package_membership_system"
    then obtain v a d P where member: "gu=use_data_term v" "gr=Payload_Term a" "x=definition_site_value d"
        "native_package_at E v a P" "d\<in>system_definitions P"
      by (simp only: package_membership_at_source[OF gE]) blast
    have "d=dx" using member(3) ends(1) by (simp add: prod_eq_iff)
    then have "native_definition_sites E {dx}\<subseteq>system_definitions P"
      using native_package_support_formed(2)[OF member(4), of "{dx}"] member(5) by simp
    then have "de\<in>system_definitions P" using reached by blast
    then have "(83,package_subject_argument g gu gr e)\<in>positive_meaning package_membership_system"
      using member(1,2,4) ends(2) by (simp only: package_membership_at_source[OF gE]) blast
    then show ?thesis by blast
  next
    assume "(77,Pair_Term g (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
    then obtain rs where rs: "Pair_Term x (Payload_Term [])=data_list_term (map (\<lambda>d. definition_site_value d) rs)"
        "native_package_formed E (set rs)"
      by (simp only: package_closure_admission_at_source[OF gE]) blast
    have "data_list_term [x]=data_list_term (map (\<lambda>d. definition_site_value d) rs)" using rs(1) by simp
    then have "[x]=map (\<lambda>d. definition_site_value d) rs" by (simp only: data_list_term_injective)
    then obtain d where d: "rs=[d]" "x=definition_site_value d" by (cases rs) auto
    have "d=dx" using d(2) ends(1) by (simp add: prod_eq_iff)
    then have formed: "native_package_formed E {dx}" using rs(2) d(1) by simp
    have sub: "native_definition_sites E {de}\<subseteq>native_definition_sites E {dx}"
    proof
      fix f assume "f\<in>native_definition_sites E {de}"
      then have "(de,f)\<in>(native_definition_edges E)\<^sup>*" by (auto simp: native_definition_sites_def)
      then have "(dx,f)\<in>(native_definition_edges E)\<^sup>*" by (rule converse_rtrancl_into_rtrancl[OF edgeE])
      then show "f\<in>native_definition_sites E {dx}" by (auto simp: native_definition_sites_def)
    qed
    have "native_package_formed E (set [de])" using formed sub by (auto simp: native_package_formed_def)
    then have "(77,Pair_Term g (Pair_Term e (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
      using package_closure_admission_on_values[OF gE, of "[de]"] ends(2) by simp
    then show ?thesis by blast
  qed
  show ?thesis using parts(1,3-7) e_parts e_calls by blast
qed

subsection \<open>The reach over the least environment's edges is a bound whenever any bound is\<close>

theorem extension_bound_reach_passes:
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning P \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
    and rows: "set zs=least_closure_bound (positive_meaning P) l q"
    and roots: "(47,Pair_Term q w)\<in>positive_meaning data_subset_system"
    and members: "(959,Pair_Term (Pair_Term (Pair_Term l s) w) w)\<in>positive_meaning extension_package_system"
  shows "(47,Pair_Term q (data_list_term zs))\<in>positive_meaning data_subset_system"
    and "(959,Pair_Term (Pair_Term (Pair_Term l s) (data_list_term zs)) (data_list_term zs))
      \<in>positive_meaning extension_package_system"
proof -
  let ?M="positive_meaning extension_package_system"
  let ?A="edge_answers (positive_meaning definition_edge_reading_system) l"
  let ?Z="least_closure_bound (positive_meaning P) l q"
  obtain qs ys where lists: "q=data_list_term qs" "w=data_list_term ys" "data_elements qs" "data_elements ys"
      "set qs\<subseteq>set ys"
    using roots by (auto simp: data_subset_exact)
  have held: "term_formed (Pair_Term (Pair_Term l s) w) \<and>
      (\<forall>y\<in>set ys. (958,Pair_Term (Pair_Term (Pair_Term l s) w) y)\<in>?M)"
    using members unfolding lists(2) bounded_members_lists.lists by blast
  have wf: "term_formed (Pair_Term l s)" using held by simp
  have edge_same: "edge_answers (positive_meaning P) l=?A" using edges by simp
  have selected: "selection_answers (positive_meaning P) q=set qs"
    unfolding lists(1) by (rule selection_answers_exact[OF selection lists(3)])
  have Z: "?Z=?A\<^sup>* `` set qs" using edge_same selected by simp
  define G where "G x \<longleftrightarrow> (\<exists>g gu gr. s=source_root_argument g gu gr \<and> term_formed l \<and> term_formed g \<and>
    term_formed gu \<and> term_formed gr \<and> bounded_given_raw l g gu gr x)" for x
  have split: "\<exists>g gu gr. s=source_root_argument g gu gr \<and> term_formed l \<and> term_formed g \<and> term_formed gu \<and>
      term_formed gr \<and> term_formed x \<and>
      ((76,Pair_Term (Pair_Term l k) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<or>
       bounded_given_raw l g gu gr x)"
    if raw: "(958,Pair_Term (Pair_Term (Pair_Term l s) k) x)\<in>?M" for k x
  proof -
    obtain l' g gu gr k' x' where eq: "Pair_Term (Pair_Term (Pair_Term l s) k) x=
        Pair_Term (Pair_Term (Pair_Term l' (source_root_argument g gu gr)) k') x'"
      and f: "term_formed l'" "term_formed g" "term_formed gu" "term_formed gr" "term_formed k'" "term_formed x'"
      and alt: "(76,Pair_Term (Pair_Term l' k') (Pair_Term x' (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<or>
        bounded_given_raw l' g gu gr x'"
      using raw unfolding bounded_member_raw by blast
    have eqs: "l'=l" "k'=k" "x'=x" and s: "s=source_root_argument g gu gr" using eq by simp_all
    show ?thesis using f[unfolded eqs] alt[unfolded eqs] s by blast
  qed
  have unsplit: "(958,Pair_Term (Pair_Term (Pair_Term l s) k) x)\<in>?M"
    if "s=source_root_argument g gu gr" "term_formed l" "term_formed g" "term_formed gu" "term_formed gr"
      "term_formed k" "term_formed x"
      "(76,Pair_Term (Pair_Term l k) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<or>
       bounded_given_raw l g gu gr x" for g gu gr k x
    using that(2-) unfolding bounded_member_raw that(1) by blast
  have callee_source: "\<exists>L u r p C. environment_value_presents L l \<and> x=site_data_term u r \<and>
      native_definition_at L u r p C \<and>
      (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set bs)"
    if callee: "(76,Pair_Term (Pair_Term l (data_list_term bs)) (Pair_Term x (Payload_Term [])))
      \<in>positive_meaning definition_callee_list_system" and data: "data_elements bs" for bs x
  proof -
    have listed: "(76,Pair_Term (Pair_Term l (data_list_term bs)) (data_list_term [x]))
        \<in>positive_meaning definition_callee_list_system" using callee by simp
    have "\<exists>L. environment_value_presents L l"
    proof (rule ccontr)
      assume absent: "\<not>(\<exists>L. environment_value_presents L l)"
      have "[x]=[]" by (rule callee_list_unsourced[of definition_callee_list_system, OF refl listed absent])
      then show False by simp
    qed
    then obtain L where least: "environment_value_presents L l" by blast
    have "\<exists>u r p C. x=site_data_term u r \<and> native_definition_at L u r p C \<and>
        (\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set bs)"
      using listed definition_callee_list_on_values[OF least data, of "[x]"] by simp
    then show ?thesis using least by blast
  qed
  have inv: "x\<in>set ys \<or> G x" if xz: "x\<in>?A\<^sup>* `` set qs" for x
  proof -
    from xz obtain y where y: "y\<in>set qs" and path: "(y,x)\<in>?A\<^sup>*" by blast
    from path show ?thesis
    proof (induction rule: rtrancl_induct)
      case base
      show ?case using y lists(5) by blast
    next
      case (step x e)
      from step(3) show ?case
      proof
        assume member: "x\<in>set ys"
        have "(958,Pair_Term (Pair_Term (Pair_Term l s) w) x)\<in>?M" using held member by blast
        then obtain g gu gr where s: "s=source_root_argument g gu gr" and formed: "term_formed l" "term_formed g"
            "term_formed gu" "term_formed gr"
          and alt: "(76,Pair_Term (Pair_Term l w) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<or>
            bounded_given_raw l g gu gr x"
          using split by blast
        from alt show ?thesis
        proof
          assume "(76,Pair_Term (Pair_Term l w) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system"
          then obtain L u r p C where defn: "environment_value_presents L l" "x=site_data_term u r"
              "native_definition_at L u r p C"
              "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ys"
            using callee_source[of ys x] lists(2,4) by blast
          obtain L' dx de where ends: "environment_value_presents L' l" "x=definition_site_value dx"
              "e=definition_site_value de" "(dx,de)\<in>native_definition_edges L'"
            by (rule edge_answers_source[OF step(2)])
          have "L'=L" by (rule environment_value_presents_unique[OF ends(1) defn(1)])
          moreover have "dx=(u,r)" using ends(2) defn(2) by (cases dx) (auto simp: site_data_term_def
            dest: injD[OF use_data_term_injective])
          ultimately obtain p' C' c S where edge_read: "native_definition_at L u r p' C'" "(c,S)\<in>C'"
              "de\<in>schema_dependencies S"
            using ends(4) by (auto simp: native_definition_edges_def)
          have "C'=C" using native_definition_unique[OF edge_read(1) defn(3)] by blast
          then have "e\<in>set ys" using defn(4) edge_read(2,3) ends(3) by blast
          then show ?thesis by blast
        next
          assume "bounded_given_raw l g gu gr x"
          then have "bounded_given_raw l g gu gr e" by (rule bounded_given_edge[OF _ step(2)])
          then show ?thesis unfolding G_def using s formed by blast
        qed
      next
        assume "G x"
        then obtain g gu gr where s: "s=source_root_argument g gu gr" and formed: "term_formed l" "term_formed g"
            "term_formed gu" "term_formed gr" and given: "bounded_given_raw l g gu gr x"
          unfolding G_def by blast
        have "bounded_given_raw l g gu gr e" by (rule bounded_given_edge[OF given step(2)])
        then show ?thesis unfolding G_def using s formed by blast
      qed
    qed
  qed
  have elem: "term_formed x \<and> self_contained_term x" if xz: "x\<in>?A\<^sup>* `` set qs" for x
  proof -
    from xz obtain y where y: "y\<in>set qs" and path: "(y,x)\<in>?A\<^sup>*" by blast
    from path show ?thesis
    proof (induction rule: rtrancl_induct)
      case base
      show ?case using y lists(3) by blast
    next
      case (step x e)
      show ?case by (rule edge_answers_target_data[OF step(2)])
    qed
  qed
  have closed: "e\<in>?A\<^sup>* `` set qs" if "x\<in>?A\<^sup>* `` set qs" "(x,e)\<in>?A" for x e
    using that by (meson Image_iff rtrancl.rtrancl_into_rtrancl)
  have zset: "set zs=?A\<^sup>* `` set qs" using rows Z by simp
  have zdata: "data_elements zs" using elem zset by blast
  have zf: "term_formed (data_list_term zs)" using zdata by (simp add: data_list_term_formed)
  have pass: "(958,Pair_Term (Pair_Term (Pair_Term l s) (data_list_term zs)) x)\<in>?M" if xz: "x\<in>set zs" for x
  proof -
    have xz': "x\<in>?A\<^sup>* `` set qs" using xz zset by blast
    have xf: "term_formed x" using elem[OF xz'] by blast
    from inv[OF xz'] show ?thesis
    proof
      assume member: "x\<in>set ys"
      have "(958,Pair_Term (Pair_Term (Pair_Term l s) w) x)\<in>?M" using held member by blast
      then obtain g gu gr where s: "s=source_root_argument g gu gr" and formed: "term_formed l" "term_formed g"
          "term_formed gu" "term_formed gr"
        and alt: "(76,Pair_Term (Pair_Term l w) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<or>
          bounded_given_raw l g gu gr x"
        using split by blast
      from alt show ?thesis
      proof
        assume "(76,Pair_Term (Pair_Term l w) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system"
        then obtain L u r p C where defn: "environment_value_presents L l" "x=site_data_term u r"
            "native_definition_at L u r p C"
          using callee_source[of ys x] lists(2,4) by blast
        have callees: "(\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set zs" if "(c,S)\<in>C" for c S
        proof
          fix y assume "y\<in>(\<lambda>d. definition_site_value d) ` schema_dependencies S"
          then obtain d where d: "y=definition_site_value d" "d\<in>schema_dependencies S" by blast
          have "((u,r),d)\<in>native_definition_edges L" using defn(3) that d(2) by (auto simp: native_definition_edges_def)
          then have "(x,y)\<in>?A" using edge_answers_exact[of definition_edge_reading_system, OF refl defn(1)] defn(2) d(1)
            by (auto simp: site_data_term_def intro!: image_eqI[where x="((u,r),d)"])
          then show "y\<in>set zs" using closed[OF xz'] zset by blast
        qed
        have "(76,Pair_Term (Pair_Term l (data_list_term zs)) (data_list_term [x]))
            \<in>positive_meaning definition_callee_list_system"
          using definition_callee_list_on_values[OF defn(1) zdata, of "[x]"] defn(2,3) callees by auto
        then have "(76,Pair_Term (Pair_Term l (data_list_term zs)) (Pair_Term x (Payload_Term [])))
            \<in>positive_meaning definition_callee_list_system" by simp
        then show ?thesis by (rule unsplit[OF s formed zf xf disjI1])
      next
        assume "bounded_given_raw l g gu gr x"
        then show ?thesis by (rule unsplit[OF s formed zf xf disjI2])
      qed
    next
      assume "G x"
      then obtain g gu gr where s: "s=source_root_argument g gu gr" and formed: "term_formed l" "term_formed g"
          "term_formed gu" "term_formed gr" and given: "bounded_given_raw l g gu gr x"
        unfolding G_def by blast
      show ?thesis by (rule unsplit[OF s formed zf xf disjI2[OF given]])
    qed
  qed
  show "(47,Pair_Term q (data_list_term zs))\<in>positive_meaning data_subset_system"
    unfolding data_subset_exact using lists(1,3) zdata zset by blast
  show "(959,Pair_Term (Pair_Term (Pair_Term l s) (data_list_term zs)) (data_list_term zs))\<in>?M"
    unfolding bounded_members_lists.lists using wf zf pass by simp
qed

theorem extension_bound_least_witness:
  assumes selection: "\<And>t. (5,t)\<in>positive_meaning P \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning P \<longleftrightarrow> (82,t)\<in>positive_meaning definition_edge_reading_system"
    and rows: "set zs=least_closure_bound (positive_meaning P) l q"
  shows "(\<exists>w. (47,Pair_Term q w)\<in>positive_meaning data_subset_system \<and>
      (959,Pair_Term (Pair_Term (Pair_Term l s) w) w)\<in>positive_meaning extension_package_system) \<longleftrightarrow>
    (47,Pair_Term q (data_list_term zs))\<in>positive_meaning data_subset_system \<and>
      (959,Pair_Term (Pair_Term (Pair_Term l s) (data_list_term zs)) (data_list_term zs))
        \<in>positive_meaning extension_package_system"
  using extension_bound_reach_passes[OF selection edges rows] by blast

subsection \<open>The registration and its completeness\<close>

definition extension_bound_registration :: "(nat,nat,nat,nat) collection_registration" where
  "extension_bound_registration=closure_witness_registration 960 bounded_closure_schema 3 0 2"

text \<open>The registration's value is its family's collection, which the construction evaluates without its schema.\<close>

lemma extension_bound_registration_value:
  "finite_registration_value_in \<Xi> P n extension_bound_registration B=
    finite_family_collected_in \<Xi> P n (closure_witness_family 0 2) B"
  by (simp add: extension_bound_registration_def closure_witness_registration_def finite_registration_value_in_def)

lemma extension_bound_premises_hold:
  "finite_variable_premises_hold P (finite_schema_of bounded_closure_schema) 3 \<theta> \<longleftrightarrow>
    (47,Pair_Term (decode_finite_term (\<theta> 2)) (decode_finite_term (\<theta> 3))) \<in> positive_meaning (decode_finite_system P) \<and>
    (959,Pair_Term (Pair_Term (Pair_Term (decode_finite_term (\<theta> 0)) (decode_finite_term (\<theta> 1)))
      (decode_finite_term (\<theta> 3))) (decode_finite_term (\<theta> 3))) \<in> positive_meaning (decode_finite_system P)"
  by (simp add: finite_variable_premises_hold_def finite_schema_of_premises_member finite_schema_of_materials_member
    bounded_closure_schema_def all_conj_distrib)

theorem extension_bound_registration_complete_in:
  fixes P :: "(nat,nat,nat,'c) finite_schema_system"
  assumes exact: "finite_query_exact \<Xi> P n"
    and selection: "\<And>t. (5,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (82,t)\<in>positive_meaning definition_edge_reading_system"
    and subset: "\<And>t. (47,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    and members: "\<And>t. (959,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (959,t)\<in>positive_meaning extension_package_system"
  shows "finite_registration_complete_in \<Xi> P n extension_bound_registration"
proof -
  let ?S="finite_schema_of bounded_closure_schema"
  let ?M="positive_meaning (decode_finite_system P)"
  have fields: "registration_schema extension_bound_registration=?S" "registration_variable extension_bound_registration=3"
    by (simp_all add: extension_bound_registration_def closure_witness_registration_def)
  have head: "3 |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)"
    by (simp add: finite_schema_of_def bounded_closure_schema_def)
  have complete: "finite_value_complete P ?S 3 (finite_registration_value_in \<Xi> P n extension_bound_registration)"
    unfolding finite_value_complete_def
  proof (intro allI impI)
    fix B v
    assume functional: "finite_relation_functional B" and "fBall B (\<lambda>(b,t). finite_term_formed t)"
      and "3 |\<notin>| fimage fst B" and scope: "finite_variable_premises_bound ?S 3 (fimage fst B)"
      and valued: "finite_registration_value_in \<Xi> P n extension_bound_registration B=Some v"
    have "0 |\<in>| fimage fst B"
      by (rule finite_variable_premises_bound_premise[OF scope, where s=2 and e=959 and
        p="Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
          (Finite_Variable 3)) (Finite_Variable 3)"])
        (simp_all add: finite_schema_of_premises_member bounded_closure_schema_def)
    then obtain tx where tx: "(0,tx) |\<in>| B" by (rule fimage_fst_binding)
    have "2 |\<in>| fimage fst B"
      by (rule finite_variable_premises_bound_premise[OF scope, where s=1 and e=47 and
        p="Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3)"])
        (simp_all add: finite_schema_of_premises_member bounded_closure_schema_def)
    then obtain ty where ty: "(2,ty) |\<in>| B" by (rule fimage_fst_binding)
    have binding: "finite_binding_valuation B 0=tx" "finite_binding_valuation B 2=ty"
      by (rule finite_binding_valuation_member[OF functional tx], rule finite_binding_valuation_member[OF functional ty])
    note valued'=valued[unfolded extension_bound_registration_def]
    obtain zs where zs: "decode_finite_term v=data_list_term zs"
      "set zs=least_closure_bound ?M (decode_finite_term tx) (decode_finite_term ty)"
      using closure_witness_registration_value_in(2)[OF exact functional tx ty valued'] by blast
    have formed: "finite_term_formed v" by (rule closure_witness_registration_value_in(1)[OF exact functional tx ty valued'])
    let ?s="decode_finite_term (finite_binding_valuation B 1)"
    have hold: "finite_variable_premises_hold P ?S 3 ((finite_binding_valuation B)(3:=w)) \<longleftrightarrow>
        (47,Pair_Term (decode_finite_term ty) (decode_finite_term w))\<in>positive_meaning data_subset_system \<and>
        (959,Pair_Term (Pair_Term (Pair_Term (decode_finite_term tx) ?s) (decode_finite_term w)) (decode_finite_term w))
          \<in>positive_meaning extension_package_system" for w
      by (simp add: extension_bound_premises_hold binding[simplified] subset members)
    show "(\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 3 ((finite_binding_valuation B)(3:=w))) \<longleftrightarrow>
        finite_variable_premises_hold P ?S 3 ((finite_binding_valuation B)(3:=v))"
    proof
      assume "\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 3 ((finite_binding_valuation B)(3:=w))"
      then obtain w where held: "(47,Pair_Term (decode_finite_term ty) (decode_finite_term w))\<in>positive_meaning data_subset_system"
        "(959,Pair_Term (Pair_Term (Pair_Term (decode_finite_term tx) ?s) (decode_finite_term w)) (decode_finite_term w))
          \<in>positive_meaning extension_package_system"
        by (auto simp: hold)
      have "(47,Pair_Term (decode_finite_term ty) (data_list_term zs))\<in>positive_meaning data_subset_system"
          "(959,Pair_Term (Pair_Term (Pair_Term (decode_finite_term tx) ?s) (data_list_term zs)) (data_list_term zs))
            \<in>positive_meaning extension_package_system"
        by (rule extension_bound_reach_passes[OF selection edges zs(2) held])+
      then show "finite_variable_premises_hold P ?S 3 ((finite_binding_valuation B)(3:=v))" by (simp add: hold zs(1))
    next
      assume "finite_variable_premises_hold P ?S 3 ((finite_binding_valuation B)(3:=v))"
      then show "\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 3 ((finite_binding_valuation B)(3:=w))"
        using formed by blast
    qed
  qed
  show ?thesis unfolding finite_registration_complete_in_def fields using head complete by simp
qed

lemmas extension_bound_registration_complete = extension_bound_registration_complete_in[OF finite_query_exact_plain]

end
