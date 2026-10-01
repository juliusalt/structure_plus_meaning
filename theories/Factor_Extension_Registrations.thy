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

section \<open>The least environment at an added site\<close>

text \<open>
  AX2c of task 928's course (c): the least environment l, 961's premise-only variable 7 at its added-site clause,
  registered in W2's form as a pair of families. The rows: the rows 965 reads at the given, the added rows, the added
  binding rows and the site's use (stored rows at that use or at an endpoint of an added binding row), keyed by their
  use. The binding rows: the added binding rows, selected by 5 and keyed by their source slot. Both are identified by
  equality, so two different rows at one key are a conflict: both are kept, as W2 keeps conflicts, and the pair then
  presents no environment.
\<close>

definition least_row_query :: "(nat,nat,nat) collection_query" where
  "least_row_query=\<lparr>query_equations=[(0,Finite_Variable 0),(1,Finite_Variable 1),(2,Finite_Variable 2),
      (3,Finite_Variable 3)],query_site=965,
    query_goal=Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1))
      (Finite_Pattern_Pair (Finite_Variable 2) (Finite_Variable 3))) (Finite_Variable 4),query_element=4\<rparr>"

lemma least_row_query_answers:
  assumes functional: "finite_relation_functional B"
    and bound: "(0,tg) |\<in>| B" "(1,ta) |\<in>| B" "(2,tb) |\<in>| B" "(3,tu) |\<in>| B"
  shows "decode_finite_term ` {e. finite_query_holds P least_row_query B [] e}=
    {x. (965,Pair_Term (Pair_Term (Pair_Term (decode_finite_term tg) (decode_finite_term ta))
      (Pair_Term (decode_finite_term tb) (decode_finite_term tu))) x) \<in> positive_meaning (decode_finite_system P)}"
    (is "?L=?R")
proof -
  have options: "finite_relation_option B 0=Some tg" "finite_relation_option B 1=Some ta"
      "finite_relation_option B 2=Some tb" "finite_relation_option B 3=Some tu"
    using finite_relation_option_correct[OF functional] bound by blast+
  have inputs: "finite_query_inputs least_row_query B []=
      Some [(tg,Finite_Variable 0),(ta,Finite_Variable 1),(tb,Finite_Variable 2),(tu,Finite_Variable 3)]"
    by (simp add: finite_query_inputs_def least_row_query_def options options[unfolded One_nat_def])
  have holds: "finite_query_holds P least_row_query B [] e \<longleftrightarrow> (\<exists>\<theta>::nat \<Rightarrow> finite_factor_term. \<theta> 4=e \<and> \<theta> 0=tg \<and> \<theta> 1=ta \<and> \<theta> 2=tb \<and>
      \<theta> 3=tu \<and> (965,Pair_Term (Pair_Term (Pair_Term (decode_finite_term (\<theta> 0)) (decode_finite_term (\<theta> 1)))
        (Pair_Term (decode_finite_term (\<theta> 2)) (decode_finite_term (\<theta> 3)))) (decode_finite_term (\<theta> 4)))
        \<in> positive_meaning (decode_finite_system P))" for e
    unfolding finite_query_holds_def inputs by (auto simp: least_row_query_def)
  show ?thesis
  proof
    show "?L \<subseteq> ?R" using holds by auto
    show "?R \<subseteq> ?L"
    proof
      fix x assume "x \<in> ?R"
      then have call: "(965,Pair_Term (Pair_Term (Pair_Term (decode_finite_term tg) (decode_finite_term ta))
          (Pair_Term (decode_finite_term tb) (decode_finite_term tu))) x) \<in> positive_meaning (decode_finite_system P)"
        by simp
      have formed: "term_formed x" using schema_call_formed_target[OF positive_meaning_formed[OF call]] by simp
      define \<theta> :: "nat \<Rightarrow> finite_factor_term" where
        "\<theta>=(\<lambda>v. if v=0 then tg else if v=1 then ta else if v=2 then tb else if v=3 then tu else finite_term_of x)"
      have "finite_query_holds P least_row_query B [] (finite_term_of x)"
        unfolding holds by (rule exI[of _ \<theta>]) (use call formed in \<open>simp add: \<theta>_def decode_finite_term_of\<close>)
      then show "x \<in> ?L" using formed
        by (intro image_eqI[of _ _ "finite_term_of x"]) (simp_all add: decode_finite_term_of)
    qed
  qed
qed

definition least_rows_family :: "(nat,nat,nat) collection_family" where
  "least_rows_family=\<lparr>family_base=[least_row_query],family_step=None,
    family_key=(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),0),family_identity=None\<rparr>"

definition least_bindings_family :: "(nat,nat,nat) collection_family" where
  "least_bindings_family=\<lparr>family_base=[witness_selection_query 2 (Finite_Variable 0) 0],family_step=None,
    family_key=(Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),0),family_identity=None\<rparr>"



subsection \<open>The registration\<close>

definition least_environment_registration :: "(nat,nat,nat,nat) collection_registration" where
  "least_environment_registration=\<lparr>registration_site=961,registration_schema=finite_schema_of extension_added_site_schema,
    registration_variable=7,registration_families=Paired_Families least_rows_family least_bindings_family\<rparr>"

lemma least_environment_registration_value:
  "finite_registration_value_in \<Xi> P n least_environment_registration B=
    (case finite_family_collected_in \<Xi> P n least_rows_family B of None \<Rightarrow> None
      | Some x \<Rightarrow> map_option (Finite_Pair x) (finite_family_collected_in \<Xi> P n least_bindings_family B))"
  by (simp add: least_environment_registration_def finite_registration_value_in_def)

lemma least_environment_premises_hold:
  "finite_variable_premises_hold P (finite_schema_of extension_added_site_schema) 7 \<theta> \<longleftrightarrow>
    (957,Pair_Term (Pair_Term (decode_finite_term (\<theta> 0)) (Pair_Term (decode_finite_term (\<theta> 1)) (decode_finite_term (\<theta> 2))))
      (decode_finite_term (\<theta> 7))) \<in> positive_meaning (decode_finite_system P) \<and>
    (964,Pair_Term (Pair_Term (decode_finite_term (\<theta> 7))
        (source_root_argument (decode_finite_term (\<theta> 0)) (decode_finite_term (\<theta> 5)) (decode_finite_term (\<theta> 6))))
      (Pair_Term (decode_finite_term (\<theta> 3)) (decode_finite_term (\<theta> 4)))) \<in> positive_meaning (decode_finite_system P)"
  by (simp add: finite_variable_premises_hold_def finite_schema_of_premises_member finite_schema_of_materials_member
    extension_added_site_schema_def all_conj_distrib)

subsection \<open>Presentations listed once\<close>

lemma listed_presentation_unique:
  assumes listed: "list_all2 read zs ts" and distinct: "distinct zs"
    and unique: "\<And>z z' x. read z x \<Longrightarrow> read z' x \<Longrightarrow> z=z'"
    and members: "x\<in>set ts" "y\<in>set ts" and reads: "read z x" "read z y"
  shows "x=y"
proof -
  obtain i where i: "i<length ts" "ts!i=x" using members(1) by (auto simp: in_set_conv_nth)
  obtain j where j: "j<length ts" "ts!j=y" using members(2) by (auto simp: in_set_conv_nth)
  have len: "length zs=length ts" using listed by (rule list_all2_lengthD)
  have "read (zs!i) x" "read (zs!j) y" using list_all2_nthD[OF listed] i j len by auto
  then have "zs!i=z" "zs!j=z" using unique reads by blast+
  then have "zs!i=zs!j" by simp
  then have "i=j" using nth_eq_iff_index_eq[OF distinct, of i j] i(1) j(1) len by simp
  then show ?thesis using i j by simp
qed

lemma presented_list_collection:
  assumes unique: "\<And>z z' x. read z x \<Longrightarrow> read z' x \<Longrightarrow> z=z'"
    and covers: "\<And>x. x\<in>set xs \<Longrightarrow> \<exists>z\<in>Z. read z x" and all: "\<And>z. z\<in>Z \<Longrightarrow> \<exists>x\<in>set xs. read z x"
    and distinct: "distinct xs"
    and single: "\<And>x y z. x\<in>set xs \<Longrightarrow> y\<in>set xs \<Longrightarrow> read z x \<Longrightarrow> read z y \<Longrightarrow> x=y"
  shows "data_collection_presents read Z (data_list_term xs)"
proof -
  define f where "f x=(THE z. read z x)" for x
  have f: "f x\<in>Z \<and> read (f x) x" if x: "x\<in>set xs" for x
  proof -
    obtain z where z: "z\<in>Z" "read z x" using covers[OF x] by blast
    have "f x=z" unfolding f_def by (rule the_equality, rule z(2)) (use unique z(2) in blast)
    then show ?thesis using z by simp
  qed
  have inj: "inj_on f (set xs)"
  proof (rule inj_onI)
    fix x y assume x: "x\<in>set xs" and y: "y\<in>set xs" and same: "f x=f y"
    have "read (f x) x" "read (f x) y" using f[OF x] f[OF y] same by simp_all
    then show "x=y" by (rule single[OF x y])
  qed
  have "distinct (map f xs)" using distinct inj by (simp add: distinct_map)
  moreover have "set (map f xs)=Z"
  proof
    show "set (map f xs)\<subseteq>Z" using f by auto
    show "Z\<subseteq>set (map f xs)"
    proof
      fix z assume "z\<in>Z"
      then obtain x where x: "x\<in>set xs" "read z x" using all by blast
      have "f x=z" using f[OF x(1)] x(2) unique by blast
      then show "z\<in>set (map f xs)" using x(1) by force
    qed
  qed
  moreover have "list_all2 read (map f xs) xs" unfolding list_all2_conv_all_nth
  proof (intro conjI allI impI)
    show "length (map f xs)=length xs" by simp
    fix i assume i: "i<length (map f xs)"
    then have "xs!i\<in>set xs" by simp
    then show "read (map f xs!i) (xs!i)" using f[of "xs!i"] i by simp
  qed
  ultimately show ?thesis unfolding data_collection_presents_def by blast
qed

lemma distinct_keys_member:
  assumes "distinct (map answer_key xs)" "x\<in>set xs" "y\<in>set xs" "answer_key x=answer_key y"
  shows "x=y"
  using assms by (auto simp: distinct_map inj_on_def)



lemma entry_presents_key:
  assumes "environment_artifact_entry_presents z x"
  shows "answer_key x=use_data_term (fst z)"
  using assms by (auto simp: environment_artifact_entry_presents_def)



subsection \<open>The rows 965 reads, on the additions' domain\<close>

text \<open>
  On the domain of a candidate's additions (the given an environment value, the additions its rows and bindings,
  the extension formed) a row 965 reads is a listed presentation of an added row or of a given row, and those rows are
  one at each use: two rows 965 reads at one use are one row.
\<close>

lemma least_rows_key_unique:
  assumes gvalue: "environment_value_presents E g" and rows: "environment_rows_presents (A,B) (Pair_Term a b)"
    and additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and x: "(965,Pair_Term (Pair_Term (Pair_Term g a) (Pair_Term b ut)) x)\<in>positive_meaning extension_package_system"
    and y: "(965,Pair_Term (Pair_Term (Pair_Term g a) (Pair_Term b ut)) y)\<in>positive_meaning extension_package_system"
    and key: "answer_key x=answer_key y"
  shows "x=y"
proof -
  obtain txs ts where tenum: "distinct txs" "set txs=A" "list_all2 environment_artifact_entry_presents txs ts"
      "a=data_list_term ts"
    using environment_rows_parts(1)[OF rows] unfolding data_collection_presents_def by blast
  obtain es gs gb where genum: "distinct es" "set es=environment_artifacts E"
      "list_all2 environment_artifact_entry_presents es gs" "g=Pair_Term (data_list_term gs) gb"
    using gvalue[unfolded environment_value_rows environment_rows_presents_def data_collection_presents_def] by auto
  have stored: "z\<in>set ts \<or> z\<in>set gs" if z965: "(965,Pair_Term (Pair_Term (Pair_Term g a) (Pair_Term b ut)) z)
      \<in>positive_meaning extension_package_system" for z
  proof -
    have "\<exists>v R. z=Pair_Term v R \<and> (966,Pair_Term (Pair_Term g a) (Pair_Term v R))\<in>positive_meaning extension_package_system"
      using z965 unfolding least_row_raw by auto
    then obtain v R where zv: "z=Pair_Term v R"
      and row: "(966,Pair_Term (Pair_Term g a) (Pair_Term v R))\<in>positive_meaning extension_package_system" by blast
    show ?thesis using row unfolding zv genum(4) tenum(4) stored_row_at_values[OF gvalue[unfolded genum(4)] tenum(3)] .
  qed
  have functional: "z=z'" if zz: "z\<in>A\<union>environment_artifacts E" "z'\<in>A\<union>environment_artifacts E" "fst z=fst z'"
    for z z'
  proof -
    have "artifact_at (environment_extension E A B) (fst z) (snd z)" using zz(1) by (auto simp: artifact_at_def)
    moreover have "artifact_at (environment_extension E A B) (fst z) (snd z')"
      using zz(2) unfolding zz(3) by (auto simp: artifact_at_def)
    ultimately have "snd z=snd z'" by (rule environment_artifact_unique[OF ff])
    then show ?thesis using zz(3) by (simp add: prod_eq_iff)
  qed
  have presented: "\<exists>z. environment_artifact_entry_presents z t \<and> z\<in>A\<union>environment_artifacts E \<and>
      (t\<in>set ts \<longrightarrow> z\<in>A) \<and> (t\<in>set gs \<longrightarrow> z\<in>environment_artifacts E)" if "t\<in>set ts \<or> t\<in>set gs" for t
  proof -
    from that show ?thesis
    proof
      assume t: "t\<in>set ts"
      then obtain z where z: "z\<in>set txs" "environment_artifact_entry_presents z t"
        using list_all2_members[OF tenum(3)] by blast
      have "t\<in>set gs \<longrightarrow> z\<in>environment_artifacts E"
      proof
        assume "t\<in>set gs"
        then obtain z' where "z'\<in>set es" "environment_artifact_entry_presents z' t"
          using list_all2_members[OF genum(3)] by blast
        then show "z\<in>environment_artifacts E" using environment_artifact_entry_unique[OF z(2)] genum(2) by blast
      qed
      then show ?thesis using z tenum(2) by blast
    next
      assume t: "t\<in>set gs"
      then obtain z where z: "z\<in>set es" "environment_artifact_entry_presents z t"
        using list_all2_members[OF genum(3)] by blast
      have "t\<in>set ts \<longrightarrow> z\<in>A"
      proof
        assume "t\<in>set ts"
        then obtain z' where "z'\<in>set txs" "environment_artifact_entry_presents z' t"
          using list_all2_members[OF tenum(3)] by blast
        then show "z\<in>A" using environment_artifact_entry_unique[OF z(2)] tenum(2) by blast
      qed
      then show ?thesis using z genum(2) by blast
    qed
  qed
  obtain zx where zx: "environment_artifact_entry_presents zx x" "zx\<in>A\<union>environment_artifacts E"
      "x\<in>set ts \<longrightarrow> zx\<in>A" "x\<in>set gs \<longrightarrow> zx\<in>environment_artifacts E"
    using presented[OF stored[OF x]] by blast
  obtain zy where zy: "environment_artifact_entry_presents zy y" "zy\<in>A\<union>environment_artifacts E"
      "y\<in>set ts \<longrightarrow> zy\<in>A" "y\<in>set gs \<longrightarrow> zy\<in>environment_artifacts E"
    using presented[OF stored[OF y]] by blast
  have "use_data_term (fst zx)=use_data_term (fst zy)"
    using key entry_presents_key[OF zx(1)] entry_presents_key[OF zy(1)] by simp
  then have "fst zx=fst zy" by (auto dest: injD[OF use_data_term_injective])
  then have same: "zx=zy" by (rule functional[OF zx(2) zy(2)])
  have apart: "False" if "z\<in>A" "z\<in>environment_artifacts E" for z
  proof -
    have "fst z\<in>rel_dom A" using that(1) rel_domI[of "fst z" "snd z" A] by simp
    moreover have "fst z\<in>environment_uses E"
      using that(2) rel_domI[of "fst z" "snd z" "environment_artifacts E"] by (simp add: environment_uses_def)
    ultimately show False using additions_parts(2)[OF additions] by blast
  qed
  consider "x\<in>set ts" "y\<in>set ts" | "x\<in>set gs" "y\<in>set gs" | "x\<in>set ts" "y\<in>set gs" | "x\<in>set gs" "y\<in>set ts"
    using stored[OF x] stored[OF y] by blast
  then show ?thesis
  proof cases
    case 1
    show ?thesis
    proof (rule listed_presentation_unique[OF tenum(3) tenum(1) _ 1 zx(1)])
      show "z=z'" if "environment_artifact_entry_presents z t" "environment_artifact_entry_presents z' t" for z z' t
        by (rule environment_artifact_entry_unique[OF that])
      show "environment_artifact_entry_presents zx y" using zy(1) by (simp add: same)
    qed
  next
    case 2
    show ?thesis
    proof (rule listed_presentation_unique[OF genum(3) genum(1) _ 2 zx(1)])
      show "z=z'" if "environment_artifact_entry_presents z t" "environment_artifact_entry_presents z' t" for z z' t
        by (rule environment_artifact_entry_unique[OF that])
      show "environment_artifact_entry_presents zx y" using zy(1) by (simp add: same)
    qed
  next
    case 3
    then show ?thesis using zx(3) zy(4) same apart by blast
  next
    case 4
    then show ?thesis using zx(4) zy(3) same apart by blast
  qed
qed

subsection \<open>On the additions' domain, the collected rows and bindings pass wherever an environment does\<close>

text \<open>
  Where some environment w passes 961's added-site premises (957 and 964) at the given's value, the additions and an
  added site, the rows 965 reads with the additions' binding rows, each listed once, pass them too. They present
  w's environment read at the needed uses: the site's use and the endpoints of the added binding rows. That reading
  holds the root family; every member of a bound of w at a needed use is checked there as in w, and the bound's
  members at a needed use form a bound of the reading, since the roots and every callee of a member at a needed use
  stand at a needed use.
\<close>

theorem least_environment_values_pass:
  assumes gvalue: "environment_value_presents E g" and rows: "environment_rows_presents (A,B) (Pair_Term a b)"
    and additions: "environment_additions E A B" and ff: "environment_formed (environment_extension E A B)"
    and least: "(957,Pair_Term (Pair_Term g (Pair_Term a b)) w)\<in>positive_meaning extension_package_system"
    and site: "(964,Pair_Term (Pair_Term w s) (Pair_Term ut rt))\<in>positive_meaning extension_package_system"
    and listed: "set xs={x. (965,Pair_Term (Pair_Term (Pair_Term g a) (Pair_Term b ut)) x)
        \<in>positive_meaning extension_package_system}" "distinct (map answer_key xs)"
    and selected: "set ys=selection_answers (positive_meaning bag_comparison_system) b" "distinct (map answer_key ys)"
  shows "(957,Pair_Term (Pair_Term g (Pair_Term a b)) (Pair_Term (data_list_term xs) (data_list_term ys)))
      \<in>positive_meaning extension_package_system"
    and "(964,Pair_Term (Pair_Term (Pair_Term (data_list_term xs) (data_list_term ys)) s) (Pair_Term ut rt))
      \<in>positive_meaning extension_package_system"
proof -
  let ?M="positive_meaning extension_package_system" and ?v="Pair_Term (data_list_term xs) (data_list_term ys)"
  obtain txs ts where tenum: "distinct txs" "set txs=A" "list_all2 environment_artifact_entry_presents txs ts"
      "a=data_list_term ts"
    using environment_rows_parts(1)[OF rows] unfolding data_collection_presents_def by blast
  obtain zs where zs: "set zs=B" "b=data_list_term (map binding_data zs)"
    by (rule binding_collection_list[OF environment_rows_parts(2)[OF rows]])
  obtain es gs gb where genum: "distinct es" "set es=environment_artifacts E"
      "list_all2 environment_artifact_entry_presents es gs" "g=Pair_Term (data_list_term gs) gb"
    using gvalue[unfolded environment_value_rows environment_rows_presents_def data_collection_presents_def] by auto
  have functional: "z=z'" if zz: "z\<in>A\<union>environment_artifacts E" "z'\<in>A\<union>environment_artifacts E" "fst z=fst z'"
    for z z'
  proof -
    have "artifact_at (environment_extension E A B) (fst z) (snd z)" using zz(1) by (auto simp: artifact_at_def)
    moreover have "artifact_at (environment_extension E A B) (fst z) (snd z')"
      using zz(2) unfolding zz(3) by (auto simp: artifact_at_def)
    ultimately have "snd z=snd z'" by (rule environment_artifact_unique[OF ff])
    then show ?thesis using zz(3) by (simp add: prod_eq_iff)
  qed
  obtain L where L: "environment_value_presents L w" "environment_bindings L=B"
      "environment_artifacts L\<subseteq>A\<union>environment_artifacts E"
    using least_environment_sound[OF gvalue rows least] by blast
  have lf: "environment_formed L" using environment_value_presents_formed[OF L(1)] by blast
  have "\<exists>c. (47,Pair_Term b c)\<in>positive_meaning data_subset_system" using least unfolding least_environment_raw by auto
  then obtain c where sub: "(47,Pair_Term b c)\<in>positive_meaning data_subset_system" by blast
  have bdata: "data_elements (map binding_data zs)"
    using sub unfolding zs(2) data_subset_exact by (auto simp: data_list_term_injective)
  have formation: "(954,Pair_Term g (Pair_Term (Pair_Term a b) (Payload_Term [])))\<in>positive_meaning extension_formation_system"
    using least unfolding least_environment_raw by auto
  have ga_formed: "term_formed g" "term_formed a" "term_formed b"
    using schema_call_formed_target[OF positive_meaning_formed[OF least]] by simp_all
  have "\<exists>q. term_formed q \<and> (79,citation_observation_argument w ut rt q)\<in>positive_meaning root_family_reading_system \<and>
      (960,Pair_Term (Pair_Term w s) q)\<in>?M"
    using site unfolding added_site_raw by auto
  then obtain q where family: "(79,citation_observation_argument w ut rt q)\<in>positive_meaning root_family_reading_system"
    and closure: "(960,Pair_Term (Pair_Term w s) q)\<in>?M" by blast
  have sformed: "term_formed s" "term_formed ut" "term_formed rt"
    using schema_call_formed_target[OF positive_meaning_formed[OF site]] by simp_all
  obtain u0 r0 ds where shape: "ut=use_data_term u0" "rt=Payload_Term r0"
      "q=data_list_term (map (\<lambda>d. definition_site_value d) ds)"
    using family by (simp only: root_family_reading_at_source[OF L(1)]) blast
  obtain Q where Q: "native_root_family_at L u0 r0 Q" "rel_ran Q=set ds"
    using root_family_reading_recovers[OF L(1) family[unfolded shape]] by blast
  define N where "N={u0}\<union>{v. \<exists>k t. ((v,k),t)\<in>B}\<union>{v. \<exists>v' k. ((v',k),v)\<in>B}"
  let ?F="read_environment L N (rel_dom B)"
  have u0L: "u0\<in>environment_uses L"
  proof -
    obtain R where "artifact_at L u0 R" using Q(1) by (auto simp: native_root_family_at_def)
    then show ?thesis using rel_domI[of u0 R] by (simp add: environment_uses_def artifact_at_def)
  qed
  have NL: "N\<subseteq>environment_uses L"
  proof
    fix v assume "v\<in>N"
    then consider "v=u0" | k t where "((v,k),t)\<in>B" | v' k where "((v',k),v)\<in>B" unfolding N_def by blast
    then show "v\<in>environment_uses L"
    proof cases
      case 1
      then show ?thesis using u0L by simp
    next
      case (2 k t)
      have "binds_slot L v k t" using 2 L(2) by (simp add: binds_slot_def)
      then show ?thesis by (rule environment_binding_uses(1)[OF lf])
    next
      case (3 v' k)
      have "binds_slot L v' k v" using 3 L(2) by (simp add: binds_slot_def)
      then show ?thesis by (rule environment_binding_uses(2)[OF lf])
    qed
  qed
  have boundary: "read_boundary_formed L N (rel_dom B)"
    unfolding read_boundary_formed_def using lf NL L(2) by (auto simp: N_def rel_dom_def)
  have Fformed: "environment_formed ?F" by (rule read_environment_formed[OF boundary])
  have Fuses: "read_environment_uses L N (rel_dom B)=N"
    unfolding read_environment_uses_def using L(2) by (auto simp: N_def binds_slot_def rel_dom_def)
  have Fbindings: "environment_bindings ?F=B" using L(2) by (auto simp: read_environment_def rel_dom_def)
  have Farts: "environment_artifacts ?F={z\<in>environment_artifacts L. fst z\<in>N}"
    by (simp add: read_environment_def Fuses)
  have row: "(965,Pair_Term (Pair_Term (Pair_Term g a) (Pair_Term b ut)) x)\<in>?M \<longleftrightarrow>
      (x\<in>set ts \<or> x\<in>set gs) \<and> (\<exists>z. environment_artifact_entry_presents z x \<and>
        (fst z=u0 \<or> (\<exists>k t. ((fst z,k),t)\<in>set zs) \<or> (\<exists>v k. ((v,k),fst z)\<in>set zs)))" for x
    unfolding tenum(4) zs(2) shape(1) by (rule least_row_at_values[OF gvalue genum(4) tenum(3) bdata]) simp
  have ts_rows: "\<exists>z\<in>A. environment_artifact_entry_presents z x" if "x\<in>set ts" for x
    using list_all2_members[OF tenum(3)] that tenum(2) by blast
  have gs_rows: "\<exists>z\<in>environment_artifacts E. environment_artifact_entry_presents z x" if "x\<in>set gs" for x
    using list_all2_members[OF genum(3)] that genum(2) by blast
  have inL: "z\<in>environment_artifacts L" if zz: "z\<in>A\<union>environment_artifacts E" "fst z\<in>N" for z
  proof -
    obtain R where R: "(fst z,R)\<in>environment_artifacts L"
      using NL zz(2) by (auto simp: environment_uses_def rel_dom_def)
    have "(fst z,R)=z" by (rule functional) (use L(3) R zz(1) in auto)
    then show ?thesis using R by simp
  qed
  have C1: "\<exists>z\<in>environment_artifacts ?F. environment_artifact_entry_presents z x" if xs: "x\<in>set xs" for x
  proof -
    have "(965,Pair_Term (Pair_Term (Pair_Term g a) (Pair_Term b ut)) x)\<in>?M" using xs listed(1) by blast
    then have x: "(x\<in>set ts \<or> x\<in>set gs) \<and> (\<exists>z. environment_artifact_entry_presents z x \<and>
        (fst z=u0 \<or> (\<exists>k t. ((fst z,k),t)\<in>set zs) \<or> (\<exists>v k. ((v,k),fst z)\<in>set zs)))" by (simp only: row)
    then obtain z where z: "environment_artifact_entry_presents z x"
      and nd: "fst z=u0 \<or> (\<exists>k t. ((fst z,k),t)\<in>set zs) \<or> (\<exists>v k. ((v,k),fst z)\<in>set zs)" by blast
    have zN: "fst z\<in>N" using nd zs(1) unfolding N_def by blast
    have "\<exists>z'\<in>A\<union>environment_artifacts E. environment_artifact_entry_presents z' x" using x ts_rows gs_rows by blast
    then have zA: "z\<in>A\<union>environment_artifacts E" using environment_artifact_entry_unique z(1) by blast
    show ?thesis by (intro bexI[of _ z]) (use inL[OF zA zN] z zN Farts in auto)
  qed
  have C2: "\<exists>x\<in>set xs. environment_artifact_entry_presents z x" if zF: "z\<in>environment_artifacts ?F" for z
  proof -
    have z: "z\<in>environment_artifacts L" "fst z\<in>N" using zF Farts by auto
    have zA: "z\<in>A\<union>environment_artifacts E" using z(1) L(3) by blast
    have "\<exists>x. (x\<in>set ts \<or> x\<in>set gs) \<and> environment_artifact_entry_presents z x"
      using zA list_all2_members[OF tenum(3)] list_all2_members[OF genum(3)] tenum(2) genum(2) by blast
    then obtain x where x: "x\<in>set ts \<or> x\<in>set gs" "environment_artifact_entry_presents z x" by blast
    have needed: "fst z=u0 \<or> (\<exists>k t. ((fst z,k),t)\<in>set zs) \<or> (\<exists>v k. ((v,k),fst z)\<in>set zs)"
      using z(2) zs(1) by (auto simp: N_def)
    have "(965,Pair_Term (Pair_Term (Pair_Term g a) (Pair_Term b ut)) x)\<in>?M"
      by (simp only: row) (use x needed in blast)
    then have "x\<in>set xs" using listed(1) by blast
    then show ?thesis using x(2) by blast
  qed
  have xs_distinct: "distinct xs" using listed(2) by (simp add: distinct_map)
  have xs_present: "data_collection_presents environment_artifact_entry_presents (environment_artifacts ?F) (data_list_term xs)"
  proof (rule presented_list_collection[OF environment_artifact_entry_unique C1 C2 xs_distinct])
    fix x y z assume "x\<in>set xs" "y\<in>set xs" "environment_artifact_entry_presents z x" "environment_artifact_entry_presents z y"
    then show "x=y" using distinct_keys_member[OF listed(2)] entry_presents_key by metis
  qed
  have bsel: "selection_answers (positive_meaning bag_comparison_system) b=set (map binding_data zs)"
    unfolding zs(2) by (rule selection_answers_exact) (simp_all add: bdata)
  have ys_set: "set ys=binding_data ` B" using selected(1) bsel zs(1) by simp
  have ys_present: "data_collection_presents (\<lambda>z v. v=binding_data z) (environment_bindings ?F) (data_list_term ys)"
  proof (rule presented_list_collection)
    show "z=z'" if "x=binding_data z" "x=binding_data z'" for z z' x using that by (auto dest: injD[OF binding_data_injective])
    show "\<exists>z\<in>environment_bindings ?F. x=binding_data z" if "x\<in>set ys" for x using that ys_set Fbindings by auto
    show "\<exists>x\<in>set ys. x=binding_data z" if "z\<in>environment_bindings ?F" for z using that ys_set Fbindings by auto
    show "distinct ys" using selected(2) by (simp add: distinct_map)
    show "x=y" if "x\<in>set ys" "y\<in>set ys" "x=binding_data z" "y=binding_data z" for x y z using that by simp
  qed
  have vpresent: "environment_value_presents ?F ?v"
    unfolding environment_value_rows environment_rows_presents_def using Fformed xs_present ys_present by auto
  have vformed: "term_formed ?v" "self_contained_term ?v" using environment_value_presents_formed[OF vpresent] by blast+
  have xdata: "data_elements xs" using vformed by (intro data_list_elements) simp_all
  have ydata: "data_elements ys" using bdata ys_set zs(1) by auto
  have xs_rows: "(955,Pair_Term (Pair_Term g a) x)\<in>?M" if xs: "x\<in>set xs" for x
  proof -
    have "(965,Pair_Term (Pair_Term (Pair_Term g a) (Pair_Term b ut)) x)\<in>?M" using xs listed(1) by blast
    then have "x\<in>set ts \<or> x\<in>set gs" by (simp only: row)
    then have "x\<in>set ts \<or> (\<exists>z\<in>environment_artifacts E. environment_artifact_entry_presents z x)" using gs_rows by blast
    then show ?thesis unfolding tenum(4) by (simp only: extension_row_at_values[OF gvalue tenum(3)])
  qed
  have rowsv: "(956,Pair_Term (Pair_Term g a) (data_list_term xs))\<in>?M"
    unfolding extension_rows_lists.lists using ga_formed xs_rows by simp
  have bset: "set (map binding_data zs)=set ys" using ys_set zs(1) by simp
  have subs: "(47,Pair_Term b (data_list_term ys))\<in>positive_meaning data_subset_system"
      "(47,Pair_Term (data_list_term ys) b)\<in>positive_meaning data_subset_system"
    unfolding data_subset_exact zs(2)
    by (rule exI[of _ "map binding_data zs"], rule exI[of _ ys]; use bdata ydata bset in auto)
      (rule exI[of _ ys], rule exI[of _ "map binding_data zs"]; use bdata ydata bset in auto)
  show "(957,Pair_Term (Pair_Term g (Pair_Term a b)) ?v)\<in>?M"
    unfolding least_environment_raw using ga_formed vformed vpresent rowsv subs formation by fastforce
  have slots: "requested_slots L ({u0}\<times>family_endpoints L u0 r0)\<subseteq>rel_dom B"
    using requested_slots_subset[OF native_root_requests_formed[OF Q(1)]] L(2) by (simp add: native_root_requests_def)
  have familyF: "native_root_family_at ?F u0 r0 Q"
    by (rule native_root_family_read_environment[OF Q(1) boundary _ slots]) (simp add: N_def)
  obtain ds' where read': "(79,citation_observation_argument ?v (use_data_term u0) (Payload_Term r0)
      (data_list_term (map (\<lambda>d. definition_site_value d) ds')))\<in>positive_meaning root_family_reading_system"
    and range': "rel_ran Q=set ds'" using root_family_reading_total[OF vpresent familyF] by blast
  have "\<exists>k. term_formed k \<and> (47,Pair_Term q k)\<in>positive_meaning data_subset_system \<and>
      (959,Pair_Term (Pair_Term (Pair_Term w s) k) k)\<in>?M"
    using closure unfolding bounded_closure_raw by auto
  then obtain k where roots: "(47,Pair_Term q k)\<in>positive_meaning data_subset_system"
      and checked: "(959,Pair_Term (Pair_Term (Pair_Term w s) k) k)\<in>?M" by blast
  obtain qs ks where klists: "q=data_list_term qs" "k=data_list_term ks" "data_elements qs" "data_elements ks"
      "set qs\<subseteq>set ks"
    using roots by (auto simp: data_subset_exact)
  have members: "\<forall>x\<in>set ks. (958,Pair_Term (Pair_Term (Pair_Term w s) k) x)\<in>?M"
    using checked unfolding klists(2) bounded_members_lists.lists by blast
  have qs: "qs=map (\<lambda>d. definition_site_value d) ds" using klists(1) shape(3) by (simp add: data_list_term_injective)
  have edgeN: "fst e\<in>N" if "fst d\<in>N" "(d,e)\<in>native_definition_edges L" for d e
  proof -
    have "fst d=fst e \<or> (fst d,fst e)\<in>environment_edges L" by (rule native_definition_edge_uses[OF that(2)])
    then show ?thesis
    proof
      assume "fst d=fst e"
      then show ?thesis using that(1) by simp
    next
      assume "(fst d,fst e)\<in>environment_edges L"
      then obtain kk where "binds_slot L (fst d) kk (fst e)" by (auto simp: environment_edges_def)
      then show ?thesis using L(2) by (auto simp: N_def binds_slot_def)
    qed
  qed
  have rootN: "fst d\<in>N" if dQ: "d\<in>rel_ran Q" for d
  proof -
    obtain sk where "(sk,d)\<in>Q" using dQ by (auto simp: rel_ran_def)
    then obtain aa where "located_at L u0 aa (fst d) (snd d)" using native_root_family_origin[OF Q(1)] by blast
    then have "u0=fst d \<or> (u0,fst d)\<in>environment_edges L" by (rule located_at_use_edge)
    then show ?thesis
    proof
      assume "u0=fst d"
      then show ?thesis by (simp add: N_def)
    next
      assume "(u0,fst d)\<in>environment_edges L"
      then obtain kk where "binds_slot L u0 kk (fst d)" by (auto simp: environment_edges_def)
      then show ?thesis using L(2) by (auto simp: N_def binds_slot_def)
    qed
  qed
  define keyed_N where "keyed_N x \<longleftrightarrow> (\<exists>v\<in>N. \<exists>t. x=Pair_Term (use_data_term v) t)" for x
  define ks' where "ks'=filter keyed_N ks"
  have site_keyed: "keyed_N (definition_site_value d)" if "fst d\<in>N" for d
    using that by (auto simp: keyed_N_def site_data_term_def)
  have kdata: "data_elements ks'" using klists(4) by (simp add: ks'_def)
  have kf': "term_formed (data_list_term ks')" using kdata by (simp add: data_list_term_formed)
  have roots': "(47,Pair_Term (data_list_term (map (\<lambda>d. definition_site_value d) ds')) (data_list_term ks'))
      \<in>positive_meaning data_subset_system"
  proof -
    have sub: "set (map (\<lambda>d. definition_site_value d) ds')\<subseteq>set ks'"
    proof
      fix y assume "y\<in>set (map (\<lambda>d. definition_site_value d) ds')"
      then obtain d where d: "d\<in>set ds'" "y=definition_site_value d" by auto
      have dQ: "d\<in>rel_ran Q" using d(1) range' by simp
      have "y\<in>set qs" using d(2) dQ Q(2) qs by auto
      then have "y\<in>set ks" using klists(5) by blast
      then show "y\<in>set ks'" using site_keyed[OF rootN[OF dQ]] d(2) by (simp add: ks'_def)
    qed
    have "data_elements (map (\<lambda>d. definition_site_value d) ds')" using sub kdata by blast
    then show ?thesis unfolding data_subset_exact using sub kdata by blast
  qed
  have members': "(958,Pair_Term (Pair_Term (Pair_Term ?v s) (data_list_term ks')) x)\<in>?M" if xk: "x\<in>set ks'" for x
  proof -
    have xks: "x\<in>set ks" and xN: "keyed_N x" using xk by (auto simp: ks'_def)
    have raw: "(958,Pair_Term (Pair_Term (Pair_Term w s) k) x)\<in>?M" using members xks by blast
    obtain l' g' gu gr k' x' where eq: "Pair_Term (Pair_Term (Pair_Term w s) k) x=
        Pair_Term (Pair_Term (Pair_Term l' (source_root_argument g' gu gr)) k') x'"
      and fs: "term_formed l'" "term_formed g'" "term_formed gu" "term_formed gr" "term_formed k'" "term_formed x'"
      and alt: "(76,Pair_Term (Pair_Term l' k') (Pair_Term x' (Payload_Term [])))\<in>positive_meaning definition_callee_list_system \<or>
        (\<exists>lw lb du dr R rest. l'=Pair_Term lw lb \<and> x'=Pair_Term du dr \<and> term_formed R \<and> term_formed rest \<and>
         (963,Pair_Term du lb)\<in>?M \<and> (5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system \<and>
         (37,Pair_Term g' (Pair_Term du R))\<in>positive_meaning artifact_lookup_system \<and>
         ((83,package_subject_argument g' gu gr x')\<in>positive_meaning package_membership_system \<or>
          (77,Pair_Term g' (Pair_Term x' (Payload_Term [])))\<in>positive_meaning package_closure_admission_system))"
      using raw unfolding bounded_member_raw by blast
    have eqs: "l'=w" "k'=k" "x'=x" and s: "s=source_root_argument g' gu gr" using eq by simp_all
    note alt=alt[unfolded eqs]
    have new: "(76,Pair_Term (Pair_Term ?v (data_list_term ks')) (Pair_Term x (Payload_Term [])))
        \<in>positive_meaning definition_callee_list_system \<or>
      (\<exists>lw lb du dr R rest. ?v=Pair_Term lw lb \<and> x=Pair_Term du dr \<and> term_formed R \<and> term_formed rest \<and>
         (963,Pair_Term du lb)\<in>?M \<and> (5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system \<and>
         (37,Pair_Term g' (Pair_Term du R))\<in>positive_meaning artifact_lookup_system \<and>
         ((83,package_subject_argument g' gu gr x)\<in>positive_meaning package_membership_system \<or>
          (77,Pair_Term g' (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system))"
      using alt
    proof
      assume "(76,Pair_Term (Pair_Term w k) (Pair_Term x (Payload_Term [])))\<in>positive_meaning definition_callee_list_system"
      then have "(76,Pair_Term (Pair_Term w (data_list_term ks)) (data_list_term [x]))
          \<in>positive_meaning definition_callee_list_system" using klists(2) by simp
      then obtain u r p C where defn: "x=site_data_term u r" "native_definition_at L u r p C"
          "\<forall>c S. (c,S)\<in>C \<longrightarrow> (\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ks"
        unfolding definition_callee_list_on_values[OF L(1) klists(4)] by auto
      have uN: "u\<in>N" using xN defn(1) by (auto simp: keyed_N_def site_data_term_def dest: injD[OF use_data_term_injective])
      have slotsd: "\<forall>kk\<in>native_definition_slots L u r. (u,kk)\<in>rel_dom B"
        using native_definition_slots_bound[of _ L u r] L(2) by simp
      have defnF: "native_definition_at ?F u r p C"
        by (rule native_definition_read_environment(1)[OF defn(2) boundary uN slotsd])
      have callees: "(\<lambda>d. definition_site_value d) ` schema_dependencies S\<subseteq>set ks'" if cS: "(c,S)\<in>C" for c S
      proof
        fix y assume "y\<in>(\<lambda>d. definition_site_value d) ` schema_dependencies S"
        then obtain d where dd: "y=definition_site_value d" "d\<in>schema_dependencies S" by blast
        have "((u,r),d)\<in>native_definition_edges L" using defn(2) cS dd(2) by (auto simp: native_definition_edges_def)
        then have "fst d\<in>N" using edgeN[of "(u,r)" d] uN by simp
        moreover have "y\<in>set ks" using defn(3) cS dd by blast
        ultimately show "y\<in>set ks'" using site_keyed dd(1) by (simp add: ks'_def)
      qed
      have "(76,Pair_Term (Pair_Term ?v (data_list_term ks')) (data_list_term [x]))\<in>positive_meaning definition_callee_list_system"
        unfolding definition_callee_list_on_values[OF vpresent kdata] using defn(1) defnF callees by auto
      then show ?thesis by simp
    next
      assume "\<exists>lw lb du dr R rest. w=Pair_Term lw lb \<and> x=Pair_Term du dr \<and> term_formed R \<and> term_formed rest \<and>
         (963,Pair_Term du lb)\<in>?M \<and> (5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system \<and>
         (37,Pair_Term g' (Pair_Term du R))\<in>positive_meaning artifact_lookup_system \<and>
         ((83,package_subject_argument g' gu gr x)\<in>positive_meaning package_membership_system \<or>
          (77,Pair_Term g' (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system)"
      then obtain lw lb du dr R rest where parts: "w=Pair_Term lw lb" "x=Pair_Term du dr"
          "(963,Pair_Term du lb)\<in>?M" "(5,Pair_Term (Pair_Term du R) (Pair_Term lw rest))\<in>positive_meaning bag_comparison_system"
          "(37,Pair_Term g' (Pair_Term du R))\<in>positive_meaning artifact_lookup_system"
        and calls: "(83,package_subject_argument g' gu gr x)\<in>positive_meaning package_membership_system \<or>
          (77,Pair_Term g' (Pair_Term x (Payload_Term [])))\<in>positive_meaning package_closure_admission_system"
        by blast
      obtain v0 t0 where v0: "v0\<in>N" "x=Pair_Term (use_data_term v0) t0" using xN by (auto simp: keyed_N_def)
      have du: "du=use_data_term v0" using parts(2) v0(2) by simp
      have "selected_data_member (Pair_Term du R) lw" using parts(4) by blast
      then obtain wrs where lwl: "lw=data_list_term wrs" "Pair_Term du R\<in>set wrs"
        unfolding selected_data_member_exact by blast
      obtain lzs lts lb' where lenum: "set lzs=environment_artifacts L"
          "list_all2 environment_artifact_entry_presents lzs lts" "w=Pair_Term (data_list_term lts) lb'"
        using L(1)[unfolded environment_value_rows environment_rows_presents_def data_collection_presents_def] by auto
      have "lts=wrs" using lenum(3) parts(1) lwl(1) by (simp add: data_list_term_injective)
      then obtain zL where zL: "zL\<in>environment_artifacts L" "environment_artifact_entry_presents zL (Pair_Term du R)"
        using list_all2_members[OF lenum(2)] lwl(2) lenum(1) by blast
      have fz: "fst zL=v0" using entry_presents_key[OF zL(2)] du by (auto dest: injD[OF use_data_term_injective])
      have zF: "zL\<in>environment_artifacts ?F" using zL(1) fz v0(1) Farts by simp
      obtain x' where x': "x'\<in>set xs" "environment_artifact_entry_presents zL x'" using C2[OF zF] by blast
      obtain R' where R': "artifact_value_presents (snd zL) R'" "x'=Pair_Term (use_data_term (fst zL)) R'"
        using x'(2) by (auto simp: environment_artifact_entry_presents_def)
      have "selected_data_member x' (data_list_term xs)" using x'(1) xdata by (auto simp: selected_data_member_exact)
      then obtain rest' where rest': "(5,Pair_Term x' (Pair_Term (data_list_term xs) rest'))\<in>positive_meaning bag_comparison_system"
        by blast
      have restf: "term_formed rest'" using schema_call_formed_target[OF positive_meaning_formed[OF rest']] by simp
      have R'f: "term_formed R'" using environment_artifact_entry_formed[OF x'(2)] R'(2) by simp
      have key: "term_formed (use_data_term v0)" "self_contained_term (use_data_term v0)" by simp_all
      have absent: "\<forall>u k t. binds_slot L u k t \<longrightarrow> u\<noteq>v0"
        using source_absences_at_values[OF L(1)[unfolded parts(1)] key] parts(3) du by simp
      have absent': "(963,Pair_Term du (data_list_term ys))\<in>?M"
        using source_absences_at_values[OF vpresent key] absent L(2) Fbindings du by (simp add: binds_slot_def)
      obtain E0 e0 u1 R2 a1 where lk: "Pair_Term g' (Pair_Term du R)=artifact_lookup_argument e0 (use_data_term u1) a1"
          "environment_value_presents E0 e0" "artifact_at E0 u1 R2" "artifact_value_presents R2 a1"
        using parts(5) unfolding artifact_lookup_exact by blast
      have lkeq: "e0=g'" "use_data_term u1=du" "a1=R" using lk(1) by simp_all
      have "artifact_value_presents (snd zL) R" using zL(2) by (auto simp: environment_artifact_entry_presents_def)
      then have "snd zL=R2" using artifact_value_presents_unique lk(4) lkeq(3) by blast
      then have "(37,Pair_Term g' (Pair_Term du R'))\<in>positive_meaning artifact_lookup_system"
        unfolding artifact_lookup_exact using lk(2,3) R'(1) lkeq by blast
      moreover have "(5,Pair_Term (Pair_Term du R') (Pair_Term (data_list_term xs) rest'))\<in>positive_meaning bag_comparison_system"
        using rest' R'(2) fz du by simp
      ultimately show ?thesis using parts(2) R'f restf absent' calls by blast
    qed
    show ?thesis unfolding bounded_member_raw s using vformed(1) fs[unfolded eqs] kf' new by blast
  qed
  have checked': "(959,Pair_Term (Pair_Term (Pair_Term ?v s) (data_list_term ks')) (data_list_term ks'))\<in>?M"
    unfolding bounded_members_lists.lists using vformed(1) sformed kf' members' by simp
  have qf': "term_formed (data_list_term (map (\<lambda>d. definition_site_value d) ds'))"
    using schema_call_formed_target[OF positive_meaning_formed[OF read']] by simp
  have closure': "(960,Pair_Term (Pair_Term ?v s) (data_list_term (map (\<lambda>d. definition_site_value d) ds')))\<in>?M"
    unfolding bounded_closure_raw using vformed(1) sformed qf' kf' vpresent roots' checked' by blast
  show "(964,Pair_Term (Pair_Term ?v s) (Pair_Term ut rt))\<in>?M"
    unfolding added_site_raw
    by (rule exI[of _ ?v], rule exI[of _ s], rule exI[of _ ut], rule exI[of _ rt],
      intro conjI refl vformed(1) sformed exI[of _ "data_list_term (map (\<lambda>d. definition_site_value d) ds')"] qf' closure')
      (simp only: shape read')
qed

subsection \<open>The registration is complete\<close>

text \<open>
  Where some environment passes 961's added-site premises, 957's formation premise (954) puts the bindings in the
  additions' domain: the given an environment value, the additions its rows and bindings, the extension formed.
  There a row 965 reads and a binding row of the additions are each one at its key, so the pair of families
  collects no conflict and, collected, passes the premises (@{text least_environment_values_pass}).
\<close>

theorem least_environment_registration_complete_in:
  fixes P :: "(nat,nat,nat,'c) finite_schema_system"
  assumes exact: "finite_query_exact \<Xi> P n"
    and selection: "\<And>t. (5,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and least: "\<And>t. (957,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (957,t)\<in>positive_meaning extension_package_system"
    and site: "\<And>t. (964,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (964,t)\<in>positive_meaning extension_package_system"
    and rows: "\<And>t. (965,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (965,t)\<in>positive_meaning extension_package_system"
  shows "finite_registration_complete_in \<Xi> P n least_environment_registration"
proof -
  let ?S="finite_schema_of extension_added_site_schema" and ?M="positive_meaning extension_package_system"
  have fields: "registration_schema least_environment_registration=?S" "registration_variable least_environment_registration=7"
    by (simp_all add: least_environment_registration_def)
  have head: "7 |\<notin>| finite_pattern_variables (finite_schema_conclusion ?S)"
    by (simp add: finite_schema_of_def extension_added_site_schema_def)
  have complete: "finite_value_complete P ?S 7 (finite_registration_value_in \<Xi> P n least_environment_registration)"
    unfolding finite_value_complete_def
  proof (intro allI impI)
    fix B v
    assume functional: "finite_relation_functional B" and "fBall B (\<lambda>(b,t). finite_term_formed t)"
      and "7 |\<notin>| fimage fst B" and scope: "finite_variable_premises_bound ?S 7 (fimage fst B)"
      and valued: "finite_registration_value_in \<Xi> P n least_environment_registration B=Some v"
    let ?p957="Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Pattern_Pair (Finite_Variable 1)
      (Finite_Variable 2))) (Finite_Variable (7::nat))"
    let ?p964="Finite_Pattern_Pair (Finite_Pattern_Pair (Finite_Variable 7) (Finite_Pattern_Pair
      (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 5)) (Finite_Variable 6))) (Finite_Pattern_Pair
      (Finite_Variable 3) (Finite_Variable (4::nat)))"
    have p957: "(0,957,?p957) |\<in>| finite_schema_premises ?S"
      by (simp add: finite_schema_of_premises_member extension_added_site_schema_def)
    have p964: "(1,964,?p964) |\<in>| finite_schema_premises ?S"
      by (simp add: finite_schema_of_premises_member extension_added_site_schema_def)
    have bound: "x |\<in>| fimage fst B" if "x\<in>{0,1,2}" for x
      by (rule finite_variable_premises_bound_premise[OF scope p957]) (use that in auto)
    have bound3: "3 |\<in>| fimage fst B"
      by (rule finite_variable_premises_bound_premise[OF scope p964]) auto
    obtain t0 where t0: "(0,t0) |\<in>| B" using bound[of 0] by (auto elim: fimage_fst_binding)
    obtain t1 where t1: "(1,t1) |\<in>| B" using bound[of 1] by (auto elim: fimage_fst_binding)
    obtain t2 where t2: "(2,t2) |\<in>| B" using bound[of 2] by (auto elim: fimage_fst_binding)
    obtain t3 where t3: "(3,t3) |\<in>| B" using bound3 by (auto elim: fimage_fst_binding)
    let ?\<theta>="finite_binding_valuation B"
    have vals: "?\<theta> 0=t0" "?\<theta> 1=t1" "?\<theta> 2=t2" "?\<theta> 3=t3"
      by (rule finite_binding_valuation_member[OF functional t0], rule finite_binding_valuation_member[OF functional t1],
        rule finite_binding_valuation_member[OF functional t2], rule finite_binding_valuation_member[OF functional t3])
    let ?g="decode_finite_term t0" and ?a="decode_finite_term t1" and ?b="decode_finite_term t2"
      and ?u="decode_finite_term t3" and ?r="decode_finite_term (?\<theta> 4)"
      and ?s="source_root_argument (decode_finite_term t0) (decode_finite_term (?\<theta> 5)) (decode_finite_term (?\<theta> 6))"
    have hold: "finite_variable_premises_hold P ?S 7 (?\<theta>(7:=w)) \<longleftrightarrow>
        (957,Pair_Term (Pair_Term ?g (Pair_Term ?a ?b)) (decode_finite_term w))\<in>?M \<and>
        (964,Pair_Term (Pair_Term (decode_finite_term w) ?s) (Pair_Term ?u ?r))\<in>?M" for w
      by (simp add: least_environment_premises_hold vals vals[unfolded One_nat_def] least site)
    obtain x y where xy: "finite_family_collected_in \<Xi> P n least_rows_family B=Some x"
        "finite_family_collected_in \<Xi> P n least_bindings_family B=Some y" "v=Finite_Pair x y"
      using valued unfolding least_environment_registration_value by (auto split: option.splits)
    obtain es cs where es: "finite_family_collection_in \<Xi> P n least_rows_family B=Some (es,cs)"
        "x=finite_family_value es"
      using xy(1) unfolding finite_family_collected_some by blast
    obtain es' cs' where es': "finite_family_collection_in \<Xi> P n least_bindings_family B=Some (es',cs')"
        "y=finite_family_value es'"
      using xy(2) unfolding finite_family_collected_some by blast
    have vformed: "finite_term_formed v" by (rule finite_registration_value_formed[OF valued])
    show "(\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 7 (?\<theta>(7:=w))) \<longleftrightarrow>
        finite_variable_premises_hold P ?S 7 (?\<theta>(7:=v))"
    proof
      assume "\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 7 (?\<theta>(7:=w))"
      then obtain w where w957: "(957,Pair_Term (Pair_Term ?g (Pair_Term ?a ?b)) (decode_finite_term w))\<in>?M"
          and w964: "(964,Pair_Term (Pair_Term (decode_finite_term w) ?s) (Pair_Term ?u ?r))\<in>?M"
        by (auto simp: hold)
      have "(954,Pair_Term ?g (Pair_Term (Pair_Term ?a ?b) (Payload_Term [])))\<in>positive_meaning extension_formation_system"
        using w957 unfolding least_environment_raw by auto
      then obtain E A Bs where gvalue: "environment_value_presents E ?g"
          and rowsp: "environment_rows_presents (A,Bs) (Pair_Term ?a ?b)"
          and additions: "environment_additions E A Bs" and ff: "environment_formed (environment_extension E A Bs)"
        unfolding extension_formation_exact by auto
      have "\<exists>c. (47,Pair_Term ?b c)\<in>positive_meaning data_subset_system" using w957 unfolding least_environment_raw by auto
      then obtain c where sub: "(47,Pair_Term ?b c)\<in>positive_meaning data_subset_system" by blast
      obtain zs where zs: "set zs=Bs" "?b=data_list_term (map binding_data zs)"
        by (rule binding_collection_list[OF environment_rows_parts(2)[OF rowsp]])
      have bdata: "data_elements (map binding_data zs)"
        using sub unfolding zs(2) data_subset_exact by (auto simp: data_list_term_injective)
      let ?R="{z. (965,Pair_Term (Pair_Term (Pair_Term ?g ?a) (Pair_Term ?b ?u)) z)\<in>?M}"
      have rbase: "decode_finite_term ` finite_family_base_answers P least_rows_family B=?R"
        using least_row_query_answers[OF functional t0 t1 t2 t3, of P] rows
        by (simp add: finite_family_base_answers_def least_rows_family_def)
      have rpairs: "\<forall>z\<in>?R. \<exists>k a. z=Pair_Term k a" unfolding least_row_raw by auto
      have rstep: "family_step least_rows_family=None" and rkey: "family_key least_rows_family=
          (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),0)"
        by (simp_all add: least_rows_family_def)
      note rinfo=keyed_family_rows_in[OF exact rstep rkey es(1) rbase rpairs]
      have runique: "z=z'" if "z\<in>?R" "z'\<in>?R" "answer_key z=answer_key z'" for z z'
        using least_rows_key_unique[OF gvalue rowsp additions ff] that by blast
      have rnone: "cs=[]"
      proof (rule ccontr)
        assume "cs\<noteq>[]"
        then obtain p q where "(p,q)\<in>set cs" by (cases cs) auto
        then obtain k a b where pq: "p=Finite_Pair k a" "q=Finite_Pair k b" "a\<noteq>b"
            "decode_finite_term p\<in>?R" "decode_finite_term q\<in>?R"
          using rinfo(4) by blast
        have "decode_finite_term p=decode_finite_term q" by (rule runique[OF pq(4,5)]) (simp add: pq(1,2))
        then show False using pq(1-3) by simp
      qed
      let ?xs="map (decode_finite_term \<circ> fst) es"
      have xs_keys: "distinct (map answer_key ?xs)" using rinfo(3) rnone by simp
      have xs_set: "set ?xs=?R"
      proof
        show "set ?xs\<subseteq>?R" by (rule rinfo(1))
        show "?R\<subseteq>set ?xs"
        proof
          fix z assume z: "z\<in>?R"
          then obtain z' where z': "z'\<in>set ?xs" "answer_key z'=answer_key z" using rinfo(2) by blast
          have "z'=z" by (rule runique[OF subsetD[OF rinfo(1) z'(1)] z z'(2)])
          then show "z\<in>set ?xs" using z'(1) by simp
        qed
      qed
      let ?Q="selection_answers (positive_meaning bag_comparison_system) ?b"
      have bsel: "?Q=set (map binding_data zs)" unfolding zs(2) by (rule selection_answers_exact) (simp_all add: bdata)
      have bbase: "decode_finite_term ` finite_family_base_answers P least_bindings_family B=?Q"
      proof -
        have "decode_finite_term ` finite_family_base_answers P least_bindings_family B=
            decode_finite_term ` {e. finite_query_holds P (witness_selection_query 2 (Finite_Variable 0) 0) B [] e}"
          by (simp add: finite_family_base_answers_def least_bindings_family_def)
        also have "\<dots>={d. \<exists>\<sigma>::nat \<Rightarrow> finite_factor_term. resolution_value \<sigma> (Finite_Variable 0)=t2 \<and>
              d\<in>selection_answers (positive_meaning (decode_finite_system P)) (decode_finite_term (\<sigma> 0))}"
          by (rule witness_selection_query_answers[OF functional t2]) auto
        also have "\<dots>=?Q" (is "?A=_")
        proof (rule set_eqI, rule iffI)
          fix d assume "d\<in>?A"
          then show "d\<in>?Q" using selection by auto
        next
          fix d assume "d\<in>?Q"
          then show "d\<in>?A" using selection by (intro CollectI exI[of _ "\<lambda>_::nat. t2"]) auto
        qed
        finally show ?thesis .
      qed
      have bpairs: "\<forall>z\<in>?Q. \<exists>k a. z=Pair_Term k a" unfolding bsel by (auto simp: binding_data_def)
      have bstep: "family_step least_bindings_family=None" and bkey: "family_key least_bindings_family=
          (Finite_Pattern_Pair (Finite_Variable 0) (Finite_Variable 1),0)"
        by (simp_all add: least_bindings_family_def)
      note binfo=keyed_family_rows_in[OF exact bstep bkey es'(1) bbase bpairs]
      have bunique: "z=z'" if zq: "z\<in>?Q" "z'\<in>?Q" "answer_key z=answer_key z'" for z z'
      proof -
        obtain q1 where q1: "q1\<in>Bs" "z=binding_data q1" using zq(1) bsel zs(1) by auto
        obtain q2 where q2: "q2\<in>Bs" "z'=binding_data q2" using zq(2) bsel zs(1) by auto
        have "use_data_term (fst (fst q1))=use_data_term (fst (fst q2))" "snd (fst q1)=snd (fst q2)"
          using zq(3) q1(2) q2(2) by (simp_all add: binding_data_def)
        then have key: "fst q1=fst q2" by (auto simp: prod_eq_iff dest: injD[OF use_data_term_injective])
        have "binds_slot (environment_extension E A Bs) (fst (fst q1)) (snd (fst q1)) (snd q1)"
          using q1(1) by (auto simp: binds_slot_def environment_extension_def merge_environment_def)
        moreover have "binds_slot (environment_extension E A Bs) (fst (fst q2)) (snd (fst q2)) (snd q2)"
          using q2(1) by (auto simp: binds_slot_def environment_extension_def merge_environment_def)
        ultimately have "snd q1=snd q2" unfolding key by (rule environment_binding_unique[OF ff])
        then have "q1=q2" using key by (simp add: prod_eq_iff)
        then show ?thesis using q1(2) q2(2) by simp
      qed
      have bnone: "cs'=[]"
      proof (rule ccontr)
        assume "cs'\<noteq>[]"
        then obtain p q where "(p,q)\<in>set cs'" by (cases cs') auto
        then obtain k a b where pq: "p=Finite_Pair k a" "q=Finite_Pair k b" "a\<noteq>b"
            "decode_finite_term p\<in>?Q" "decode_finite_term q\<in>?Q"
          using binfo(4) by blast
        have "decode_finite_term p=decode_finite_term q" by (rule bunique[OF pq(4,5)]) (simp add: pq(1,2))
        then show False using pq(1-3) by simp
      qed
      let ?ys="map (decode_finite_term \<circ> fst) es'"
      have ys_keys: "distinct (map answer_key ?ys)" using binfo(3) bnone by simp
      have ys_set: "set ?ys=?Q"
      proof
        show "set ?ys\<subseteq>?Q" by (rule binfo(1))
        show "?Q\<subseteq>set ?ys"
        proof
          fix z assume z: "z\<in>?Q"
          then obtain z' where z': "z'\<in>set ?ys" "answer_key z'=answer_key z" using binfo(2) by blast
          have "z'=z" by (rule bunique[OF subsetD[OF binfo(1) z'(1)] z z'(2)])
          then show "z\<in>set ?ys" using z'(1) by simp
        qed
      qed
      note pass=least_environment_values_pass[OF gvalue rowsp additions ff w957 w964 xs_set xs_keys ys_set ys_keys]
      have dv: "decode_finite_term v=Pair_Term (data_list_term ?xs) (data_list_term ?ys)"
        using xy(3) es(2) es'(2) by (simp add: finite_family_value_decode)
      show "finite_variable_premises_hold P ?S 7 (?\<theta>(7:=v))" unfolding hold dv using pass by blast
    next
      assume "finite_variable_premises_hold P ?S 7 (?\<theta>(7:=v))"
      then show "\<exists>w. finite_term_formed w \<and> finite_variable_premises_hold P ?S 7 (?\<theta>(7:=w))"
        using vformed by blast
    qed
  qed
  show ?thesis unfolding finite_registration_complete_in_def fields using head complete by simp
qed

lemmas least_environment_registration_complete = least_environment_registration_complete_in[OF finite_query_exact_plain]

section \<open>The given's registrations with the additions' two\<close>

text \<open>
  The construction the guard over additions reads its refusal-side witnesses from: the given's four registrations
  (@{const given_witness_registrations}), 960's bound and 961's least environment. Each is complete wherever the read
  sites mean what the given's readers and the extension's readers mean, so the construction is complete there. The
  witnesses of G3's and G4's members clauses (985, 989, read through their views 991 and 992) are not yet registered.
\<close>

definition extension_witness_registrations :: "(nat,nat,nat,nat) collection_registration list" where
  "extension_witness_registrations=given_witness_registrations@[extension_bound_registration,least_environment_registration]"

lemma extension_witness_registrations_distinct: "finite_registrations_distinct extension_witness_registrations"
  by (simp add: finite_registrations_distinct_def finite_registration_key_def extension_witness_registrations_def
    given_witness_registrations_def bound_witness_registration_def additions_witness_registration_def
    merge_witness_registration_def closure_witness_registration_def extension_bound_registration_def
    least_environment_registration_def)

theorem extension_witness_registrations_complete_in:
  fixes P :: "(nat,nat,nat,'c) finite_schema_system"
  assumes exact: "finite_query_exact \<Xi> P n"
    and selection: "\<And>t. (5,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (5,t)\<in>positive_meaning bag_comparison_system"
    and identity: "\<And>t. (12,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (12,t)\<in>positive_meaning artifact_identity_system"
    and subset: "\<And>t. (47,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow> (47,t)\<in>positive_meaning data_subset_system"
    and bound: "\<And>t. (76,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (76,t)\<in>positive_meaning definition_callee_list_system"
    and edges: "\<And>t. (82,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (82,t)\<in>positive_meaning definition_edge_reading_system"
    and inclusion: "\<And>t. (113,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (113,t)\<in>positive_meaning environment_inclusion_system"
    and listing: "context_list_rule_relation (positive_meaning (decode_finite_system P)) element_391 391"
      "context_list_rule_relation (positive_meaning (decode_finite_system P)) element_524 524"
    and least: "\<And>t. (957,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (957,t)\<in>positive_meaning extension_package_system"
    and members: "\<And>t. (959,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (959,t)\<in>positive_meaning extension_package_system"
    and site: "\<And>t. (964,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (964,t)\<in>positive_meaning extension_package_system"
    and rows: "\<And>t. (965,t)\<in>positive_meaning (decode_finite_system P) \<longleftrightarrow>
      (965,t)\<in>positive_meaning extension_package_system"
  shows "\<And>R. R \<in> set extension_witness_registrations \<Longrightarrow> finite_registration_complete_in \<Xi> P n R"
    and "finite_construction_complete (finite_collection_construction_in \<Xi> extension_witness_registrations n) P"
proof -
  show each: "finite_registration_complete_in \<Xi> P n R" if "R \<in> set extension_witness_registrations" for R
    using that given_witness_registrations_complete_in(1)[OF exact selection identity subset bound edges inclusion listing]
      extension_bound_registration_complete_in[OF exact selection edges subset members]
      least_environment_registration_complete_in[OF exact selection least site rows]
    by (auto simp: extension_witness_registrations_def)
  show "finite_construction_complete (finite_collection_construction_in \<Xi> extension_witness_registrations n) P"
    by (rule finite_collection_construction_complete[OF each])
qed

lemmas extension_witness_registrations_complete =
  extension_witness_registrations_complete_in[OF finite_query_exact_plain]

end
