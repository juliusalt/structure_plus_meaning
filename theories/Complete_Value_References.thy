theory Complete_Value_References
  imports Main
begin

fun value_reference_index :: "'a \<Rightarrow> 'a list \<Rightarrow> nat option" where
  "value_reference_index x []=None"
| "value_reference_index x (y#ys)=(if x=y then Some 0 else map_option Suc (value_reference_index x ys))"

lemma value_reference_index_read:
  "value_reference_index x xs=Some i \<Longrightarrow> i<length xs \<and> xs!i=x"
  by (induction xs arbitrary: i) (auto split: option.splits if_splits)

lemma value_reference_index_absent:
  "value_reference_index x xs=None \<longleftrightarrow> x\<notin>set xs"
  by (induction xs) auto

lemma value_reference_index_append_member:
  "x\<in>set xs \<Longrightarrow> value_reference_index x (xs@ys)=value_reference_index x xs"
  by (induction xs) auto

definition value_reference_read :: "'a list \<Rightarrow> nat \<Rightarrow> 'a option" where
  "value_reference_read table i=(if i<length table then Some (table!i) else None)"

definition value_reference_step :: "'a \<Rightarrow> 'a list \<Rightarrow> nat \<times> 'a list" where
  "value_reference_step x table=(case value_reference_index x table of
    None \<Rightarrow> (length table,table@[x]) | Some i \<Rightarrow> (i,table))"

theorem value_reference_step_exact:
  "value_reference_read (snd (value_reference_step x table)) (fst (value_reference_step x table))=Some x"
  by (auto simp: value_reference_step_def value_reference_read_def nth_append
      dest: value_reference_index_read split: option.splits)

theorem value_reference_step_prefix:
  "take (length table) (snd (value_reference_step x table))=table"
  by (auto simp: value_reference_step_def split: option.splits)

theorem value_reference_step_preserves:
  assumes "value_reference_read table i=Some y"
  shows "value_reference_read (snd (value_reference_step x table)) i=Some y"
  using assms by (auto simp: value_reference_read_def value_reference_step_def nth_append
      split: option.splits if_splits)

fun value_reference_sequence :: "'a list \<Rightarrow> 'a list \<Rightarrow> nat list \<times> 'a list" where
  "value_reference_sequence [] table=([],table)"
| "value_reference_sequence (x#xs) table=(let (i,next)=value_reference_step x table;
      (indices,last)=value_reference_sequence xs next in (i#indices,last))"

lemma value_reference_sequence_preserves:
  "value_reference_read table i=Some y \<Longrightarrow>
    value_reference_read (snd (value_reference_sequence xs table)) i=Some y"
proof (induction xs arbitrary: table)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain j next_table where step: "value_reference_step x table=(j,next_table)" by (cases "value_reference_step x table") auto
  have kept: "value_reference_read next_table i=Some y"
    using value_reference_step_preserves[OF Cons.prems, of x] by (simp only: step snd_conv)
  have last: "value_reference_read (snd (value_reference_sequence xs next_table)) i=Some y"
    by (rule Cons.IH[OF kept])
  show ?case using last by (simp add: step case_prod_unfold Let_def)
qed

theorem value_reference_sequence_exact:
  "map (value_reference_read (snd (value_reference_sequence xs table)))
    (fst (value_reference_sequence xs table))=map Some xs"
proof (induction xs arbitrary: table)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  obtain i next_table where step: "value_reference_step x table=(i,next_table)" by (cases "value_reference_step x table") auto
  have first: "value_reference_read next_table i=Some x"
    using value_reference_step_exact[of x table] by (simp only: step fst_conv snd_conv)
  have kept: "value_reference_read (snd (value_reference_sequence xs next_table)) i=Some x"
    by (rule value_reference_sequence_preserves[OF first])
  show ?case using Cons.IH[of next_table] kept by (simp add: step case_prod_unfold Let_def)
qed

lemma value_reference_sequence_append:
  "value_reference_sequence (xs@ys) T=(let (is,U)=value_reference_sequence xs T;
    (js,V)=value_reference_sequence ys U in (is@js,V))"
  by (induction xs arbitrary: T) (simp_all add: case_prod_unfold Let_def)

lemma value_reference_step_distinct:
  "distinct T \<Longrightarrow> distinct (snd (value_reference_step x T))"
  by (auto simp: value_reference_step_def value_reference_index_absent split: option.splits)

lemma value_reference_sequence_distinct:
  "distinct T \<Longrightarrow> distinct (snd (value_reference_sequence xs T))"
proof (induction xs arbitrary: T)
  case (Cons x xs)
  show ?case
    using Cons.IH[OF value_reference_step_distinct[OF Cons.prems, of x]]
    by (simp add: case_prod_unfold Let_def)
qed simp

lemma value_reference_index_distinct_read:
  assumes distinct: "distinct T" and read: "value_reference_read T i=Some x"
  shows "value_reference_index x T=Some i"
proof -
  have bound: "i<length T" and at: "T!i=x" using read by (auto simp: value_reference_read_def split: if_splits)
  obtain j where found: "value_reference_index x T=Some j"
    using value_reference_index_absent[of x T] at bound nth_mem by (cases "value_reference_index x T") auto
  have jj: "j<length T" "T!j=x" using value_reference_index_read[OF found] by simp_all
  have "j=i" using nth_eq_iff_index_eq[OF distinct jj(1) bound] jj(2) at by simp
  then show ?thesis using found by simp
qed

text \<open>Each reference recovers the complete supplied value. Later insertions
  preserve every earlier reference, and decoding an entire reference sequence
  recovers the original ordered sequence exactly. The table may start with
  arbitrary values or duplicates; no cache-supplied assertion is trusted.
  Sequences compose over appended values, a table built from distinct values
  stays distinct, and in such a table every returned index is the first one.\<close>

section \<open>A reference sequence is computed segment by segment\<close>

text \<open>
  The table a sequence leaves is the supplied table extended by each value it does not yet hold,
  in the order of first occurrence, and every index is the one its value has in that final table
  when the supplied table is distinct. Hence the references of disjoint segments of a sequence can
  be computed each against an empty table, and only the segments' own distinct values are then
  referenced against the supplied table: the indices and the table are exactly those of the one
  sequential run. The segments are independent of each other, so they can be computed in parallel.
\<close>

definition value_reference_add :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "value_reference_add x T=(if x\<in>set T then T else T@[x])"

lemma value_reference_index_member: "value_reference_index x T\<noteq>None \<longleftrightarrow> x\<in>set T"
  using value_reference_index_absent[of x T] by simp

lemma value_reference_step_table: "snd (value_reference_step x T)=value_reference_add x T"
proof (cases "value_reference_index x T")
  case None
  then have "x\<notin>set T" using value_reference_index_absent[of x T] by simp
  then show ?thesis using None by (simp add: value_reference_step_def value_reference_add_def)
next
  case (Some i)
  then have "x\<in>set T" using value_reference_index_member[of x T] by simp
  then show ?thesis using Some by (simp add: value_reference_step_def value_reference_add_def)
qed

lemma value_reference_sequence_table:
  "snd (value_reference_sequence xs T)=fold value_reference_add xs T"
  by (induction xs arbitrary: T) (simp_all add: case_prod_unfold Let_def value_reference_step_table)

lemma value_reference_sequence_length: "length (fst (value_reference_sequence xs T))=length xs"
  by (induction xs arbitrary: T) (simp_all add: case_prod_unfold Let_def)

lemma value_reference_sequence_indices:
  assumes distinct: "distinct T"
  shows "fst (value_reference_sequence xs T)=
    map (\<lambda>y. the (value_reference_index y (snd (value_reference_sequence xs T)))) xs"
proof -
  let ?U="snd (value_reference_sequence xs T)"
  let ?I="fst (value_reference_sequence xs T)"
  have reads: "map (value_reference_read ?U) ?I=map Some xs" by (rule value_reference_sequence_exact)
  have len: "length ?I=length xs" by (rule value_reference_sequence_length)
  have kept: "distinct ?U" by (rule value_reference_sequence_distinct[OF distinct])
  show ?thesis
  proof (rule nth_equalityI)
    show "length ?I=length (map (\<lambda>y. the (value_reference_index y ?U)) xs)" using len by simp
  next
    fix k assume k: "k<length ?I"
    have "value_reference_read ?U (?I!k)=Some (xs!k)"
      using arg_cong[OF reads, of "\<lambda>ys. ys!k"] k len by simp
    then have "value_reference_index (xs!k) ?U=Some (?I!k)" by (rule value_reference_index_distinct_read[OF kept])
    then show "?I!k=map (\<lambda>y. the (value_reference_index y ?U)) xs!k" using k len by simp
  qed
qed

lemma value_reference_add_set: "set (value_reference_add x T)=insert x (set T)"
  by (auto simp: value_reference_add_def)

lemma value_reference_fold_set: "set (fold value_reference_add xs T)=set xs\<union>set T"
  by (induction xs arbitrary: T) (auto simp: value_reference_add_set)

lemma value_reference_fold_first:
  "fold value_reference_add (fold value_reference_add xs []) T=fold value_reference_add xs T"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  let ?D="fold value_reference_add xs []"
  have members: "set ?D=set xs" using value_reference_fold_set[of xs "[]"] by simp
  show ?case
  proof (cases "x\<in>set ?D")
    case True
    have inside: "x\<in>set (fold value_reference_add xs T)" using True members value_reference_fold_set[of xs T] by auto
    have local_step: "fold value_reference_add (xs@[x]) []=?D" using True by (simp add: value_reference_add_def)
    have whole_step: "fold value_reference_add (xs@[x]) T=fold value_reference_add xs T"
      using inside by (simp add: value_reference_add_def)
    show ?thesis by (simp only: local_step whole_step snoc.IH)
  next
    case False
    have local_step: "value_reference_add x ?D=?D@[x]" using False by (simp add: value_reference_add_def)
    show ?thesis using snoc.IH by (simp add: local_step)
  qed
qed

theorem value_reference_sequence_segment:
  assumes distinct: "distinct T"
  and local_run: "value_reference_sequence xs []=(L,D)" and merged_run: "value_reference_sequence D T=(G,U)"
  shows "value_reference_sequence xs T=(map (nth G) L,U)"
proof -
  have D_table: "D=fold value_reference_add xs []"
    using value_reference_sequence_table[of xs "[]"] local_run by simp
  have U_table: "U=fold value_reference_add xs T"
    using value_reference_sequence_table[of D T] merged_run D_table value_reference_fold_first by simp
  have whole: "snd (value_reference_sequence xs T)=U" using value_reference_sequence_table[of xs T] U_table by simp
  have L_indices: "L=map (\<lambda>y. the (value_reference_index y D)) xs"
    using value_reference_sequence_indices[of "[]" xs] local_run by simp
  have G_indices: "G=map (\<lambda>y. the (value_reference_index y U)) D"
    using value_reference_sequence_indices[OF distinct, of D] merged_run by simp
  have I_indices: "fst (value_reference_sequence xs T)=map (\<lambda>y. the (value_reference_index y U)) xs"
    using value_reference_sequence_indices[OF distinct, of xs] whole by simp
  have members: "set xs=set D" using D_table value_reference_fold_set[of xs "[]"] by simp
  have at: "G!the (value_reference_index y D)=the (value_reference_index y U)" if y: "y\<in>set xs" for y
  proof -
    obtain i where found: "value_reference_index y D=Some i"
      using y members value_reference_index_member[of y D] by auto
    have i: "i<length D" "D!i=y" using value_reference_index_read[OF found] by simp_all
    show ?thesis using found i G_indices by simp
  qed
  have indices: "map (nth G) L=map (\<lambda>y. the (value_reference_index y U)) xs"
    unfolding L_indices map_map comp_def by (rule map_cong) (simp_all add: at)
  show ?thesis using I_indices whole indices by (simp add: prod_eq_iff)
qed

text \<open>
  A sequence of mapped values factors in the same way through the map, which need not be injective:
  the first-occurrence sequence of the values, then the sequence of their distinct values mapped, and
  every index is composed. Two values with one image meet in the second sequence.
\<close>

lemma value_reference_fold_map_first:
  "fold value_reference_add (map f (fold value_reference_add xs [])) T=fold value_reference_add (map f xs) T"
proof (induction xs rule: rev_induct)
  case Nil
  then show ?case by simp
next
  case (snoc x xs)
  let ?D="fold value_reference_add xs []"
  have members: "set ?D=set xs" using value_reference_fold_set[of xs "[]"] by simp
  show ?case
  proof (cases "x\<in>set ?D")
    case True
    have inside: "f x\<in>set (fold value_reference_add (map f xs) T)"
      using True members value_reference_fold_set[of "map f xs" T] by auto
    have local_step: "fold value_reference_add (xs@[x]) []=?D" using True by (simp add: value_reference_add_def)
    have whole_step: "fold value_reference_add (map f (xs@[x])) T=fold value_reference_add (map f xs) T"
      using inside by (simp add: value_reference_add_def)
    show ?thesis by (simp only: local_step whole_step snoc.IH)
  next
    case False
    have local_step: "value_reference_add x ?D=?D@[x]" using False by (simp add: value_reference_add_def)
    show ?thesis using snoc.IH by (simp add: local_step)
  qed
qed

theorem value_reference_sequence_map:
  assumes distinct: "distinct T"
  and local_run: "value_reference_sequence xs []=(L,D)" and mapped_run: "value_reference_sequence (map f D) T=(G,U)"
  shows "value_reference_sequence (map f xs) T=(map (nth G) L,U)"
proof -
  have D_table: "D=fold value_reference_add xs []"
    using value_reference_sequence_table[of xs "[]"] local_run by simp
  have U_table: "U=fold value_reference_add (map f xs) T"
    using value_reference_sequence_table[of "map f D" T] mapped_run D_table value_reference_fold_map_first by simp
  have whole: "snd (value_reference_sequence (map f xs) T)=U"
    using value_reference_sequence_table[of "map f xs" T] U_table by simp
  have L_indices: "L=map (\<lambda>y. the (value_reference_index y D)) xs"
    using value_reference_sequence_indices[of "[]" xs] local_run by simp
  have G_indices: "G=map (\<lambda>y. the (value_reference_index y U)) (map f D)"
    using value_reference_sequence_indices[OF distinct, of "map f D"] mapped_run by simp
  have I_indices: "fst (value_reference_sequence (map f xs) T)=map (\<lambda>y. the (value_reference_index y U)) (map f xs)"
    using value_reference_sequence_indices[OF distinct, of "map f xs"] whole by simp
  have members: "set xs=set D" using D_table value_reference_fold_set[of xs "[]"] by simp
  have at: "G!the (value_reference_index y D)=the (value_reference_index (f y) U)" if y: "y\<in>set xs" for y
  proof -
    obtain i where found: "value_reference_index y D=Some i"
      using y members value_reference_index_member[of y D] by auto
    have i: "i<length D" "D!i=y" using value_reference_index_read[OF found] by simp_all
    show ?thesis using found i G_indices by simp
  qed
  have indices: "map (nth G) L=map (\<lambda>y. the (value_reference_index y U)) (map f xs)"
    unfolding L_indices map_map comp_def by (rule map_cong) (simp_all add: at)
  show ?thesis using I_indices whole indices by (simp add: prod_eq_iff)
qed

fun value_reference_merged :: "(nat list\<times>'a list) list \<Rightarrow> nat list \<Rightarrow> nat list" where
  "value_reference_merged [] G=[]"
| "value_reference_merged ((L,D)#ls) G=map (nth (take (length D) G)) L@value_reference_merged ls (drop (length D) G)"

theorem value_reference_sequence_concat:
  assumes distinct: "distinct T"
  shows "value_reference_sequence (concat cs) T=(let locals=map (\<lambda>c. value_reference_sequence c []) cs;
    (G,U)=value_reference_sequence (concat (map snd locals)) T in (value_reference_merged locals G,U))"
  using distinct
proof (induction cs arbitrary: T)
  case Nil
  then show ?case by simp
next
  case (Cons c cs)
  obtain L D where local_run: "value_reference_sequence c []=(L,D)" by (cases "value_reference_sequence c []")
  obtain G1 U1 where first: "value_reference_sequence D (T::'a list)=(G1,U1)"
    by (cases "value_reference_sequence D T")
  obtain G' V where rest: "value_reference_sequence (concat (map snd (map (\<lambda>c. value_reference_sequence c []) cs))) U1=(G',V)"
    by (cases "value_reference_sequence (concat (map snd (map (\<lambda>c. value_reference_sequence c []) cs))) U1")
  have kept: "distinct U1" using value_reference_sequence_distinct[OF Cons.prems, of D] first by simp
  have head: "value_reference_sequence c T=(map (nth G1) L,U1)"
    by (rule value_reference_sequence_segment[OF Cons.prems local_run first])
  have tail: "value_reference_sequence (concat cs) U1=(value_reference_merged (map (\<lambda>c. value_reference_sequence c []) cs) G',V)"
    using Cons.IH[OF kept] rest by (simp add: Let_def)
  have lengths: "length D=length G1" using value_reference_sequence_length[of D T] first by simp
  have whole: "value_reference_sequence (D@concat (map snd (map (\<lambda>c. value_reference_sequence c []) cs))) T=(G1@G',V)"
    using first rest by (simp add: value_reference_sequence_append)
  show ?case using head tail whole local_run
    by (simp add: value_reference_sequence_append lengths Let_def)
qed

fun value_reference_chunks :: "nat \<Rightarrow> 'a list \<Rightarrow> 'a list list" where
  "value_reference_chunks n []=[]"
| "value_reference_chunks n (x#xs)=(x#take (n-1) xs)#value_reference_chunks n (drop (n-1) xs)"

lemma value_reference_chunks_concat: "concat (value_reference_chunks n xs)=xs"
  by (induction n xs rule: value_reference_chunks.induct) simp_all

text \<open>
  A list of references reads a list of values positionally: each value is read at the reference of its
  position. A reading of a concatenation is the readings of its parts, the second at the references after
  the first's; the references of a sequence read it in the sequence's table, and a reading holds in every
  table that keeps the values read.
\<close>

definition value_reference_reads :: "'a list \<Rightarrow> nat list \<Rightarrow> 'a list \<Rightarrow> bool" where
  "value_reference_reads T ns xs \<longleftrightarrow> length xs\<le>length ns \<and> (\<forall>i<length xs. value_reference_read T (ns!i)=Some (xs!i))"

lemma value_reference_reads_append:
  "value_reference_reads T ns (xs@ys) \<longleftrightarrow> value_reference_reads T ns xs \<and> value_reference_reads T (drop (length xs) ns) ys"
proof
  assume whole: "value_reference_reads T ns (xs@ys)"
  show "value_reference_reads T ns xs \<and> value_reference_reads T (drop (length xs) ns) ys"
  proof
    show "value_reference_reads T ns xs" unfolding value_reference_reads_def
    proof (intro conjI allI impI)
      show "length xs\<le>length ns" using whole by (simp add: value_reference_reads_def)
      fix i
      assume i: "i<length xs"
      have "value_reference_read T (ns!i)=Some ((xs@ys)!i)" using whole i by (simp add: value_reference_reads_def)
      then show "value_reference_read T (ns!i)=Some (xs!i)" using i by (simp add: nth_append)
    qed
    show "value_reference_reads T (drop (length xs) ns) ys" unfolding value_reference_reads_def
    proof (intro conjI allI impI)
      show "length ys\<le>length (drop (length xs) ns)" using whole by (auto simp: value_reference_reads_def)
      fix i
      assume i: "i<length ys"
      have bound: "length xs\<le>length ns" using whole by (simp add: value_reference_reads_def)
      have "value_reference_read T (ns!(length xs+i))=Some ((xs@ys)!(length xs+i))"
        using whole i by (simp add: value_reference_reads_def)
      then show "value_reference_read T (drop (length xs) ns!i)=Some (ys!i)" using bound by (simp add: nth_append)
    qed
  qed
next
  assume parts: "value_reference_reads T ns xs \<and> value_reference_reads T (drop (length xs) ns) ys"
  show "value_reference_reads T ns (xs@ys)" unfolding value_reference_reads_def
  proof (intro conjI allI impI)
    show "length (xs@ys)\<le>length ns" using parts by (auto simp: value_reference_reads_def)
    fix i
    assume i: "i<length (xs@ys)"
    show "value_reference_read T (ns!i)=Some ((xs@ys)!i)"
    proof (cases "i<length xs")
      case True
      then show ?thesis using parts by (simp add: value_reference_reads_def nth_append)
    next
      case False
      then obtain k where k: "i=length xs+k" by (metis le_add_diff_inverse not_less)
      have "k<length ys" using i k by simp
      then have "value_reference_read T (drop (length xs) ns!k)=Some (ys!k)" using parts unfolding value_reference_reads_def by blast
      moreover have "length xs\<le>length ns" using parts by (simp add: value_reference_reads_def)
      ultimately show ?thesis using k by (simp add: nth_append)
    qed
  qed
qed

lemma value_reference_reads_cons:
  "value_reference_reads T ns (x#xs) \<longleftrightarrow> ns\<noteq>[] \<and> value_reference_read T (ns!0)=Some x \<and> value_reference_reads T (drop 1 ns) xs"
proof -
  have "value_reference_reads T ns ([x]@xs) \<longleftrightarrow> value_reference_reads T ns [x] \<and> value_reference_reads T (drop 1 ns) xs"
    by (simp only: value_reference_reads_append) simp
  moreover have "value_reference_reads T ns [x] \<longleftrightarrow> ns\<noteq>[] \<and> value_reference_read T (ns!0)=Some x"
    by (cases ns) (auto simp: value_reference_reads_def)
  ultimately show ?thesis by simp
qed

lemma value_reference_reads_sequence:
  "value_reference_reads (snd (value_reference_sequence xs T)) (fst (value_reference_sequence xs T)) xs"
proof -
  have exact: "map (value_reference_read (snd (value_reference_sequence xs T))) (fst (value_reference_sequence xs T))=map Some xs"
    by (rule value_reference_sequence_exact)
  then have length: "length (fst (value_reference_sequence xs T))=length xs" by (metis length_map)
  show ?thesis unfolding value_reference_reads_def
  proof (intro conjI allI impI)
    show "length xs\<le>length (fst (value_reference_sequence xs T))" using length by simp
    fix i
    assume "i<length xs"
    then show "value_reference_read (snd (value_reference_sequence xs T)) (fst (value_reference_sequence xs T)!i)=Some (xs!i)"
      using arg_cong[OF exact, of "\<lambda>l. l!i"] length by simp
  qed
qed

lemma value_reference_reads_preserved:
  assumes reads: "value_reference_reads T ns xs"
    and kept: "\<And>i y. value_reference_read T i=Some y \<Longrightarrow> value_reference_read T' i=Some y"
  shows "value_reference_reads T' ns xs"
  using reads kept by (simp add: value_reference_reads_def)

end
