theory IsaSAT_EVSIDS
  imports IsaSAT_Literals
    Pairing_Heap_LLVM.Heaps_Abs
    Watched_Literals_VMTF
    IsaSAT_EVSIDS_double
begin

section \<open>EVSIDS\<close>

type_synonym ('a, 'v) evsids = \<open>('a multiset \<times> 'a multiset \<times> ('a \<Rightarrow> 'v)) \<times> 'v\<close>
definition evsids :: \<open>'a multiset \<Rightarrow> ('a, 'ann) ann_lits \<Rightarrow> ('a, double\<^sub>p) evsids set\<close> where
\<open>evsids \<A> M = {((\<B>, b, w), inc). set_mset \<B> = set_mset \<A> \<and> b \<subseteq># \<A> \<and> (inc \<le> evsids_limit) \<and> (\<forall>L\<in>#\<A>. w L \<le> evsids_limit) \<and> (\<forall>L \<in>#\<A>. L \<notin># b \<longrightarrow> defined_lit M (Pos L)) \<and> distinct_mset b}\<close>

lemma evsids_prepend: \<open>vc \<in> evsids \<A> M \<Longrightarrow> vc \<in> evsids \<A> (L # M)\<close>
  unfolding evsids_def by (auto simp: defined_lit_map)

interpretation EVSIDS: hmstruct_with_prio where
  le = \<open>(\<ge>) :: double\<^sub>p \<Rightarrow> double\<^sub>p \<Rightarrow> bool\<close> and
  lt = \<open>(>)\<close>
  apply unfold_locales
  subgoal by auto
  subgoal by auto
  subgoal by auto
  subgoal by auto
  done

definition evsids_tl_pre :: \<open>'a \<Rightarrow> ('a, 'v) evsids \<Rightarrow> bool\<close> where
  \<open>evsids_tl_pre L = (\<lambda>(vc, m). L \<in># fst vc)\<close>

definition evsids_tl :: \<open>'a \<Rightarrow> ('a, double\<^sub>p) evsids \<Rightarrow> ('a, double\<^sub>p) evsids nres\<close> where
  \<open>evsids_tl L = (\<lambda>(vc, inc). do {
    ASSERT (evsids_tl_pre L (vc, inc));
    b \<leftarrow> EVSIDS.mop_prio_is_in L vc;
    if \<not>b then do {
      w \<leftarrow> EVSIDS.mop_prio_old_weight L vc;
      let w = (if w \<le> evsids_limit then w else evsids_limit);
      vc \<leftarrow> EVSIDS.mop_prio_insert L w vc;
      RETURN (vc, inc)
    } else RETURN (vc, inc)
  })\<close>

lemma evsids_tl:
  \<open>vc \<in> evsids \<A> M \<Longrightarrow> L \<in># \<A> \<Longrightarrow> M \<noteq> [] \<Longrightarrow> L = atm_of (lit_of (hd M)) \<Longrightarrow> evsids_tl L vc \<le> RES (evsids \<A> (tl M))\<close>
  unfolding evsids_tl_def EVSIDS.mop_prio_insert_unchanged_def
    EVSIDS.mop_prio_insert_raw_unchanged_def nres_monad3
    EVSIDS.mop_prio_is_in_def
    EVSIDS.mop_prio_old_weight_def
    EVSIDS.mop_prio_insert_def RES_RES_RETURN_RES RETURN_def
    EVSIDS.mop_prio_old_weight_def case_prod_beta nres_monad1
  apply (refine_vcg lhs_step_If)
  subgoal
    by (cases M) (auto simp: evsids_def EVSIDS.mop_prio_insert_unchanged_def insert_subset_eq_iff
        evsids_tl_pre_def
      intro!: subset_add_mset_notin_subset)
  subgoal
    by (auto simp: evsids_def EVSIDS.mop_prio_insert_unchanged_def insert_subset_eq_iff
        evsids_tl_pre_def
      intro!: subset_add_mset_notin_subset)
  subgoal
    apply (auto simp: evsids_def EVSIDS.mop_prio_insert_unchanged_def RES_RES_RETURN_RES
      defined_lit_map evsids_tl_pre_def dest: subset_add_mset_notin_subset
      dest: multi_member_split)
    apply (smt (verit, best) image_iff not_hd_in_tl)
      apply (metis mset_add mset_subset_eq_add_mset_cancel subset_add_mset_notin_subset)
    by (smt (verit, ccfv_threshold) image_iff in_hd_or_tl_conv)
  done

definition evsids_get_min :: \<open>('a, double\<^sub>p) evsids \<Rightarrow> 'a nres\<close> where
  \<open>evsids_get_min = (\<lambda>(vc, m). do {
    L \<leftarrow> EVSIDS.mop_prio_peek_min vc;
    RETURN L
  })\<close>

definition evsids_mset :: \<open>('a, 'v) evsids \<Rightarrow> _\<close> where
  \<open>evsids_mset x = fst (snd (fst x))\<close>

lemma evsids_get_min:
  \<open>evsids_mset x \<noteq> {#} \<Longrightarrow> evsids_get_min x \<le> SPEC (\<lambda>v. EVSIDS.prio_peek_min (fst x) v)\<close>
  unfolding evsids_get_min_def EVSIDS.mop_prio_peek_min_def evsids_mset_def
  by refine_vcg (auto simp: EVSIDS.prio_peek_min_def)

definition evsids_pop_min :: \<open>('a, double\<^sub>p) evsids \<Rightarrow> ('a \<times> ('a, double\<^sub>p) evsids) nres\<close> where
  \<open>evsids_pop_min = (\<lambda>(vc, inc). do {
    (v, vc) \<leftarrow> EVSIDS.mop_prio_pop_min vc;
    RETURN (v, (vc, inc))
  })\<close>

definition evsids_find_next_undef :: \<open>nat multiset \<Rightarrow> (nat, double\<^sub>p) evsids \<Rightarrow> (nat, nat) ann_lits \<Rightarrow> (nat option \<times> (nat, double\<^sub>p) evsids) nres\<close> where
\<open>evsids_find_next_undef \<A> = (\<lambda>vc M. do {
  WHILE\<^sub>T\<^bsup>(\<lambda>(L, vc).
        (L = None \<longrightarrow> vc \<in> evsids \<A> M) \<and>
        (L \<noteq> None \<longrightarrow> vc \<in> evsids \<A> (Decided (Pos (the L)) # M) \<and> Pos (the L) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> undefined_lit M (Pos (the L))))
  \<^esup>
      (\<lambda>(nxt, vc). nxt = None \<and> evsids_mset vc \<noteq> {#})
      (\<lambda>(a, vc). do {
         ASSERT (a = None);
         (L, vc) \<leftarrow> evsids_pop_min vc;
         ASSERT(Pos L \<in># \<L>\<^sub>a\<^sub>l\<^sub>l  \<A>);
         if defined_lit M (Pos L) then RETURN (None, vc)
         else RETURN (Some L, vc)
        }
      )
      (None, vc)
  })\<close>

lemma evsids_pop_min:
  \<open>evsids_mset x \<noteq> {#} \<Longrightarrow> x \<in> evsids \<A> M \<Longrightarrow>
  evsids_pop_min x \<le> SPEC (\<lambda>(v, vc). evsids_mset vc = evsids_mset x - {#v#} \<and> v \<in># evsids_mset x \<and>
    EVSIDS.prio_peek_min (fst x) v \<and>
    (defined_lit M (Pos v) \<longrightarrow> vc \<in> evsids \<A> M) \<and>
    (undefined_lit M (Pos v) \<longrightarrow> vc \<in> evsids \<A> (Decided (Pos v) # M)))\<close>
  unfolding EVSIDS.mop_prio_pop_min_def evsids_pop_min_def
    EVSIDS.mop_prio_peek_min_def EVSIDS.mop_prio_del_def
  by refine_vcg
   (auto simp: evsids_def EVSIDS.prio_peek_min_def distinct_mset_remove1_All EVSIDS.prio_del_def
      defined_lit_map evsids_mset_def dest: in_diffD)

lemma evsids_find_next_undef:
  assumes
    vmtf: \<open>vc \<in> evsids \<A> M\<close>
  shows \<open>evsids_find_next_undef \<A> vc M
     \<le> \<Down> Id (SPEC (\<lambda>(L, vc).
        (L = None \<longrightarrow> vc \<in> evsids \<A> M \<and> (\<forall>L\<in>#\<L>\<^sub>a\<^sub>l\<^sub>l \<A>. defined_lit M L)) \<and>
        (L \<noteq> None \<longrightarrow> vc \<in> evsids \<A> (Decided (Pos (the L)) # M) \<and> Pos (the L) \<in># \<L>\<^sub>a\<^sub>l\<^sub>l \<A> \<and> undefined_lit M (Pos (the L)))))\<close>
proof -
  have [refine0]: \<open>wf (measure (\<lambda>(_, vc). size (evsids_mset vc)))\<close>
    by auto
  show ?thesis
    unfolding evsids_find_next_undef_def
    apply (refine_vcg evsids_pop_min[of _ \<A> M, THEN order_trans])
    subgoal using assms by auto
    subgoal by auto
    subgoal by (auto simp: EVSIDS.prio_peek_min_def evsids_def evsids_mset_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: evsids_def EVSIDS.prio_peek_min_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: EVSIDS.prio_peek_min_def evsids_mset_def dest: multi_member_split)
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by auto
    subgoal by (auto simp: EVSIDS.prio_peek_min_def evsids_mset_def dest: multi_member_split)
    subgoal by auto
    subgoal by (auto simp: EVSIDS.prio_peek_min_def evsids_mset_def evsids_def
      in_\<L>\<^sub>a\<^sub>l\<^sub>l_atm_of_\<A>\<^sub>i\<^sub>n dest!: multi_member_split[of \<open>_ :: nat\<close>])
    subgoal by auto
    subgoal by auto
    subgoal by auto
    done
qed

(*TODO: Rescaling*)
definition evsids_rescale :: \<open>('a, double\<^sub>p) evsids \<Rightarrow> ('a, double\<^sub>p) evsids\<close> where
  \<open>evsids_rescale = (\<lambda>((\<B>, b, w), inc).
     ((\<B>, b, \<lambda>L. let x = w L * evsids_rescale_factor in if x \<le> evsids_limit then x else evsids_limit),
      (let i = inc * evsids_rescale_factor in if i \<le> evsids_limit then i else evsids_limit)))\<close>

lemma evsids_rescale_in_evsids:
  assumes "set_mset \<B> = set_mset \<A>" and "b \<subseteq># \<A>"
    and "\<forall>L \<in>#\<A>. L \<notin># b \<longrightarrow> defined_lit M (Pos L)" and "distinct_mset b"
  shows \<open>evsids_rescale ((\<B>, b, w), inc) \<in> evsids \<A> M\<close>
  using assms unfolding evsids_rescale_def evsids_def apply (auto simp: Let_def) done

definition evsids_push_literal_pre where
  \<open>evsids_push_literal_pre \<A> L = (\<lambda>vc. L \<in># \<A>)\<close>

definition evsids_push_literal :: \<open>nat \<Rightarrow> (nat, double\<^sub>p) evsids \<Rightarrow> (nat, double\<^sub>p) evsids nres\<close> where
  \<open>evsids_push_literal L = (\<lambda>(vc, inc). do {
    ASSERT (L \<in># fst vc);
    w \<leftarrow> EVSIDS.mop_prio_old_weight L vc;
    let w = (if w \<le> evsids_limit then w else evsids_limit);
    let w' = w + inc;
    vc \<leftarrow> EVSIDS.mop_prio_insert_maybe L w' vc;
    if evsids_limit < w' then RETURN (evsids_rescale (vc, inc))
    else RETURN (vc, inc)
  })\<close>

lemma evsids_push_literal:
  \<open>vc \<in> evsids \<A> M \<Longrightarrow> evsids_push_literal_pre \<A> L vc \<Longrightarrow> evsids_push_literal L vc \<le> SPEC (\<lambda>vc. vc \<in> evsids \<A> M)\<close>
  unfolding evsids_push_literal_def EVSIDS.mop_prio_insert_maybe_def
    EVSIDS.mop_prio_old_weight_def evsids_push_literal_pre_def
    EVSIDS.mop_prio_insert_def EVSIDS.mop_prio_change_weight_def
    EVSIDS.mop_prio_is_in_def
  apply refine_vcg
  subgoal by (auto simp: evsids_def evsids_mset_def)
  subgoal by (auto simp: evsids_def dest!: multi_member_split)
  subgoal by (auto simp: EVSIDS.mop_prio_change_weight_def evsids_def
    dest!: multi_member_split)
  subgoal by (auto simp: evsids_def dest!: multi_member_split)
  subgoal by (auto simp: evsids_def evsids_mset_def)
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal using double_plus\<^sub>p_mono by (auto split: if_splits; simp add: evsids_def)
  subgoal
  by (rule evsids_rescale_in_evsids;
      auto simp: evsids_def evsids_mset_def dest!: multi_member_split
        dest: subset_add_mset_notin_subset) 
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal
          by (rule evsids_rescale_in_evsids;
            auto simp: evsids_def evsids_mset_def dest!: multi_member_split
              dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  subgoal by (auto simp: evsids_def evsids_mset_def dest!: multi_member_split
    dest: subset_add_mset_notin_subset)
  done

definition evsids_flush_int :: \<open>nat multiset \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> (nat, double\<^sub>p) evsids \<Rightarrow> _ \<Rightarrow> ((nat, double\<^sub>p) evsids \<times> _)nres\<close> where
\<open>evsids_flush_int \<A>\<^sub>i\<^sub>n = (\<lambda>M vm (to_remove, h). do {
    ASSERT(length to_remove \<le> unat32_max);
    (_, vm, h) \<leftarrow> WHILE\<^sub>T\<^bsup>\<lambda>(i, vm', h). i \<le> length to_remove \<and>
          (i < length to_remove \<longrightarrow> evsids_push_literal_pre \<A>\<^sub>i\<^sub>n (to_remove!i) (vm'))\<^esup>
      (\<lambda>(i, vm, h). i < length to_remove)
      (\<lambda>(i, vm, h). do {
         ASSERT(i < length to_remove);
         ASSERT(to_remove!i \<in># \<A>\<^sub>i\<^sub>n);
         ASSERT(atoms_hash_del_pre (to_remove!i) h);
         vm \<leftarrow> evsids_push_literal (to_remove!i) vm;
         RETURN (i+1, vm, atoms_hash_del (to_remove!i) h)})
      (0, vm, h);
    RETURN (vm, (emptied_list to_remove, h))
  })\<close>


definition evsids_flush
   :: \<open>nat multiset \<Rightarrow> (nat,nat) ann_lits \<Rightarrow> (nat, double\<^sub>p) evsids \<Rightarrow> nat set \<Rightarrow> ((nat, double\<^sub>p) evsids \<times> nat set) nres\<close>
where
  \<open>evsids_flush \<A>\<^sub>i\<^sub>n = (\<lambda>M vm remove_int. SPEC (\<lambda>x. (fst x) \<in> evsids \<A>\<^sub>i\<^sub>n M \<and> snd x = {}))\<close>

lemma evsids_change_to_remove_order:
  assumes
    vmtf: \<open>vc \<in> evsids \<A>\<^sub>i\<^sub>n M\<close> and
    CD_rem: \<open>((C, D), to_remove) \<in> distinct_atoms_rel \<A>\<^sub>i\<^sub>n\<close> and
    nempty: \<open>isasat_input_nempty \<A>\<^sub>i\<^sub>n\<close> and
    bounded: \<open>isasat_input_bounded \<A>\<^sub>i\<^sub>n\<close> and
    t: \<open>to_remove \<subseteq> set_mset \<A>\<^sub>i\<^sub>n\<close>
  shows \<open>evsids_flush_int \<A>\<^sub>i\<^sub>n M vc (C, D) \<le> \<Down>(Id \<times>\<^sub>r distinct_atoms_rel \<A>\<^sub>i\<^sub>n) (evsids_flush \<A>\<^sub>i\<^sub>n M vc to_remove)\<close>
proof -
  have to_C: \<open>to_remove = set C\<close>
    using CD_rem by (auto simp: distinct_atoms_rel_def distinct_hash_atoms_rel_def)
  have length_le: \<open>length (fst (C,D)) \<le> unat32_max\<close>
  proof -
    have lits: \<open>literals_are_in_\<L>\<^sub>i\<^sub>n \<A>\<^sub>i\<^sub>n (Pos `# mset C)\<close> and
      dist: \<open>distinct C\<close>
      using vmtf CD_rem t unfolding vmtf_def
        vmtf_\<L>\<^sub>a\<^sub>l\<^sub>l_def
      apply (auto simp: literals_are_in_\<L>\<^sub>i\<^sub>n_alt_def distinct_atoms_rel_alt_def inj_on_def)
      by (metis atms_of_\<L>\<^sub>a\<^sub>l\<^sub>l_\<A>\<^sub>i\<^sub>n in_mono)
    have dist: \<open>distinct_mset (Pos `# mset C)\<close>
      by (subst distinct_image_mset_inj)
        (use dist in \<open>auto simp: inj_on_def\<close>)
    have tauto: \<open>\<not> tautology (poss (mset C))\<close>
      by (auto simp: tautology_decomp)

    show ?thesis
      using simple_clss_size_upper_div2[OF bounded lits dist tauto]
      by (auto simp: unat32_max_def)
  qed
  have acids_push_literal_pre: \<open>evsids_push_literal_pre \<A>\<^sub>i\<^sub>n (C ! i) vc\<close>
    if \<open>i < length C\<close> for i
    using t that CD_rem unfolding evsids_push_literal_pre_def distinct_atoms_rel_def
      distinct_hash_atoms_rel_def by auto
  define I where \<open>I \<equiv> \<lambda>(i::nat, vm'::(nat, double\<^sub>p)evsids, h). vm' \<in> evsids \<A>\<^sub>i\<^sub>n M \<and>
    ((drop i C, h), to_remove - set (take i C)) \<in> distinct_atoms_rel \<A>\<^sub>i\<^sub>n \<and> i \<le> length C\<close>

  have sin: \<open>fst s < length (fst (C, D)) \<Longrightarrow> fst (C, D) ! fst s \<in># \<A>\<^sub>i\<^sub>n\<close> and
    atms: \<open>I s \<Longrightarrow> fst s < length (fst (C, D)) \<Longrightarrow> atoms_hash_del_pre (fst (C, D) ! fst s) (snd (snd s))\<close> for s
    using t CD_rem nth_mem[of \<open>fst s\<close> C]
    unfolding evsids_push_literal_pre_def distinct_atoms_rel_def
      distinct_hash_atoms_rel_def I_def atoms_hash_del_pre_def atoms_hash_rel_def by (auto simp del: nth_mem)

  let ?R = \<open>measure (\<lambda>(i, vm', h). length C - i)\<close>

  have I_inv1_acids_push_literal_pre: \<open>I s \<Longrightarrow>
    fst (C, D) ! fst s \<in># \<A>\<^sub>i\<^sub>n \<Longrightarrow>
    x \<in> evsids \<A>\<^sub>i\<^sub>n M \<Longrightarrow>
    fst (fst s + 1, x,
    atoms_hash_del (fst (C, D) ! fst s) (snd (snd s)))
    < length (fst (C, D)) \<Longrightarrow>
    evsids_push_literal_pre \<A>\<^sub>i\<^sub>n
    (fst (C, D) ! fst (fst s + 1, x,
    atoms_hash_del (fst (C, D) ! fst s) (snd (snd s))))
    (fst (snd (fst s + 1, x, atoms_hash_del (fst (C, D) ! fst s) (snd (snd s)))))\<close>
    for s x
    using t CD_rem unfolding evsids_push_literal_pre_def distinct_atoms_rel_def
      distinct_hash_atoms_rel_def by auto
  have I_Suc: \<open>I s \<Longrightarrow>
    fst s < length (fst (C, D)) \<Longrightarrow>
    fst (C, D) ! fst s \<in># \<A>\<^sub>i\<^sub>n \<Longrightarrow>
    atoms_hash_del_pre (fst (C, D) ! fst s) (snd (snd s)) \<Longrightarrow>
    x \<in> evsids \<A>\<^sub>i\<^sub>n M \<Longrightarrow>
    I (fst s + 1, x, atoms_hash_del (fst (C, D) ! fst s) (snd (snd s)))\<close>
    for s x
    apply (auto simp: I_def distinct_atoms_rel_def 
      distinct_hash_atoms_rel_def
      intro!: relcompI[of _ \<open>(drop (Suc (fst s)) C, (snd (snd s))[C ! (fst s) := False], to_remove - set (take (Suc (fst s)) C))\<close>])
    apply (rule  relcompI[of _ \<open>(drop (Suc (fst s)) C, to_remove - set (take (Suc (fst s)) C))\<close>])
    subgoal
      by (auto simp: atoms_hash_rel_def atoms_hash_del_def take_Suc_conv_app_nth)
    subgoal
      by (auto simp: take_Suc_conv_app_nth simp flip: Cons_nth_drop_Suc)
    done

  show ?thesis
    unfolding evsids_flush_int_def evsids_flush_def case_prod_beta
    apply (refine_vcg specify_left[OF WHILEIT_rule_stronger_inv[where \<Phi> = \<open>(\<lambda>x. I x \<and> fst x =length (fst (C, D)))\<close> and I' = \<open>I\<close> and R = ?R]]
      evsids_push_literal[where \<A>=\<A>\<^sub>i\<^sub>n and M=M])
    subgoal by (rule length_le)
    subgoal by auto
    subgoal by auto
    subgoal by (auto intro!: acids_push_literal_pre)
    subgoal using assms by (auto simp: I_def)
    subgoal by (rule sin)
    subgoal by (rule atms)
    subgoal by (auto simp: I_def)
    subgoal by auto
    subgoal by auto
    subgoal for s x by (rule I_inv1_acids_push_literal_pre)
    subgoal by (rule I_Suc)
    subgoal for s x by (auto simp: I_def)
    subgoal by (auto simp: emptied_list_def conc_fun_RES I_def)
    subgoal by (auto simp add: emptied_list_def conc_fun_RES I_def Image_iff to_C)
    done
qed
end
