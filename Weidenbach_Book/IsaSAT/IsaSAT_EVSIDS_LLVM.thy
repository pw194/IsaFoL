theory IsaSAT_EVSIDS_LLVM
  imports IsaSAT_Literals_LLVM
    IsaSAT_EVSIDS
    Pairing_Heaps_Impl_LLVM
    IsaSAT_Trail_LLVM
begin

definition evsids_assn2 where
  \<open>evsids_assn2 = evsids_assn \<times>\<^sub>a dpfloat_assn\<close>

sepref_register EVSIDS.mop_prio_insert_unchanged EVSIDS.mop_prio_insert_raw_unchanged
sepref_def mop_prio_insert_raw_unchanged_impl
  is \<open>uncurry EVSIDS.mop_prio_insert_raw_unchanged\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a evsids_assn\<^sup>d \<rightarrow>\<^sub>a evsids_assn\<close>
  unfolding EVSIDS.mop_prio_insert_raw_unchanged_def
  by sepref

sepref_def mop_prio_insert_unchanged_impl
  is \<open>uncurry EVSIDS.mop_prio_insert_unchanged\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a evsids_assn\<^sup>d \<rightarrow>\<^sub>a evsids_assn\<close>
  unfolding EVSIDS.mop_prio_insert_unchanged_def
  by sepref

sepref_def evsids_tl_impl
  is \<open>uncurry evsids_tl\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a evsids_assn2\<^sup>d \<rightarrow>\<^sub>a evsids_assn2\<close>
  unfolding evsids_assn2_def evsids_tl_def
  by sepref

sepref_def evsids_pop_min_impl
  is evsids_pop_min
  :: \<open>evsids_assn2\<^sup>d \<rightarrow>\<^sub>a atom_assn \<times>\<^sub>a evsids_assn2\<close>
  unfolding evsids_pop_min_def evsids_assn2_def
  by sepref

sepref_register EVSIDS.mop_prio_insert_maybe
sepref_def mop_prio_insert_maybe_impl
  is \<open>uncurry2 (PR_CONST EVSIDS.mop_prio_insert_maybe)\<close>
  ::  \<open>atom_assn\<^sup>k *\<^sub>a dpfloat_assn\<^sup>k *\<^sub>a evsids_assn\<^sup>d \<rightarrow>\<^sub>a evsids_assn\<close>
  unfolding EVSIDS.mop_prio_insert_maybe_def PR_CONST_def
  by sepref

definition mop_imp_change_all_weights_with_inc where
  \<open>mop_imp_change_all_weights_with_inc = (\<lambda>old (xs, inc). do {
    rescaling \<leftarrow> Pairing_Heaps_Impl_LLVM.mop_imp_needs_rescaling old;
    if \<not>rescaling then RETURN (xs, inc)
    else do {
      xs \<leftarrow> mop_imp_decreases_weights_only evsids_rescore_factor xs;
      ASSERT (dpmul_pre evsids_rescore_factor inc);
      RETURN (xs, evsids_rescore_factor * inc)
    }
  })\<close>

lemma mop_imp_decreases_weights_only_spec:
  \<open>((old, xsm), old', ysm')
    \<in> Id \<times>\<^sub>f ((\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>Id\<rangle>option_rel\<rangle>pairing_heaps_rel O
        acids_encoded_hmrel) \<times>\<^sub>f Id) \<Longrightarrow>
   x2 = (x1b, x2a) \<Longrightarrow>
   x1 = (x1a, x2) \<Longrightarrow>
   ysm' = (x1, x2b) \<Longrightarrow>
   xsm = (x1c, x2c) \<Longrightarrow>
   mop_imp_decreases_weights_only evsids_rescore_factor x1c
   \<le> \<Down> {(a, b). (a, b) \<in> \<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>Id\<rangle>option_rel\<rangle>pairing_heaps_rel O acids_encoded_hmrel \<and>
        fst b = fst x1 \<and> fst (snd b) = fst (snd x1)}
      (Refine_Basic.SPEC
        (\<lambda>uu :: nat multiset \<times> nat multiset \<times> (nat \<Rightarrow> double\<^sub>p).
            \<exists>w' \<A>' \<B>'. uu = (\<A>', \<B>', w') \<and> x1a = \<A>' \<and> x1b = \<B>'))\<close>
  apply auto
  subgoal for a aa ab ac ad b ae af ag ah ai ba bb
    apply (rule order_trans)
  apply (rule mop_imp_decreases_weights_only_mop_hp_decreases_weights_only
    [of _ \<open>(ae, (af, ag, ah, ai, ba), bb)\<close>])
  apply (auto simp: mop_hp_decreases_weights_only_def conc_fun_RETURN conc_fun_RES
        evsids_rescore_factor_nonZero evsids_rescore_factor_nonInf)
  apply (rule_tac x = \<open>\<lambda>x. evsids_rescore_factor * x2a x\<close> in exI)
  apply (rule_tac b = \<open>(ae, (af, ag, ah, ai,
        \<lambda>x. map_option (\<lambda>x. evsids_rescore_factor * x) (ba x)), bb)\<close> in relcompI)
  apply assumption
  apply (auto simp: acids_encoded_hmrel_def)
  apply (rule_tac b = \<open>(aja, map_option (hp_rescale_weight evsids_rescore_factor) bca)\<close> in relcompI)
  apply (auto simp: encoded_hp_prop_list_conc_def encoded_hp_prop_def EVSIDS.hmrel_def
        intro!: EVSIDS.invar_hp_rescale_weight
        split: option.splits)
    by (metis hp_node_None_notin2 option.map_sel score_hp_rescale_weights_hp_node)
  done

lemma (in hmstruct_with_prio) mop_hm_change_all_weights_with_inc_alt_def:
  \<open>mop_hm_change_all_weights_with_inc = (\<lambda>old ((\<A>, \<B>, w), inc). do {
    rescaling \<leftarrow> SPEC (\<lambda>_. True);
    if \<not>rescaling then RETURN ((\<A>, \<B>, w), inc)
    else do {
      (\<A>, \<B>, w') \<leftarrow> RES {(\<A>', \<B>', w')|w' \<A>' \<B>'. \<A> = \<A>' \<and> \<B> = \<B>'};
      inc \<leftarrow> RES UNIV;
      RETURN ((\<A>, \<B>, w'), inc)
    }})\<close>
  unfolding mop_hm_change_all_weights_with_inc_def
    RES_RES_RETURN_RES RES_RETURN_RES RES_RES3_RETURN_RES
  by (force intro!: ext bind_cong[OF refl])

lemma mop_imp_change_all_weights_with_inc_mop_hm_change_all_weights_with_inc:
  assumes \<open>((old, xsm), (old', ysm'))
     \<in> Id \<times>\<^sub>f ((\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>Id\<rangle>option_rel\<rangle>pairing_heaps_rel O acids_encoded_hmrel) \<times>\<^sub>f Id)\<close>
  shows \<open>mop_imp_change_all_weights_with_inc old xsm \<le>
    \<Down>((\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>Id\<rangle>option_rel\<rangle>pairing_heaps_rel O acids_encoded_hmrel) \<times>\<^sub>f Id)
      (EVSIDS.mop_hm_change_all_weights_with_inc old' ysm')\<close>
  using assms
  unfolding mop_imp_change_all_weights_with_inc_def
    EVSIDS.mop_hm_change_all_weights_with_inc_alt_def
    Pairing_Heaps_Impl_LLVM.mop_imp_needs_rescaling_def
  apply (refine_vcg mop_imp_decreases_weights_only_spec)
  subgoal by auto
  subgoal by auto
  subgoal by auto
  apply assumption+
  subgoal using evsids_rescore_factor_nonZero evsids_rescore_factor_nonInf
    by (auto simp: dpmul_pre_def)
  subgoal for x1 x1a x2 x1b x2a x2b x1c x2c rescaling rescalinga
    by (auto simp: conc_fun_RETURN conc_fun_RES RES_RETURN_RES Image_def)
  done

lemma mop_imp_change_all_weights_with_inc_mop_hm_change_all_weights_with_inc2:
  \<open>(uncurry mop_imp_change_all_weights_with_inc, uncurry EVSIDS.mop_hm_change_all_weights_with_inc) \<in>
   Id \<times>\<^sub>f ((\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>Id\<rangle>option_rel\<rangle>pairing_heaps_rel O acids_encoded_hmrel) \<times>\<^sub>f Id) \<rightarrow>\<^sub>f
   \<langle>(\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>Id\<rangle>option_rel\<rangle>pairing_heaps_rel O acids_encoded_hmrel) \<times>\<^sub>f Id\<rangle>nres_rel\<close>
  unfolding uncurry_def
  apply (intro frefI nres_relI, (subst case_prod_beta)+)
  subgoal for a b
    by (rule order_trans,
        rule mop_imp_change_all_weights_with_inc_mop_hm_change_all_weights_with_inc
          [of \<open>fst a\<close> \<open>snd a\<close> \<open>fst b\<close> \<open>snd b\<close>])
      auto
  done

sepref_register mop_imp_decreases_weights_only
sepref_def mop_imp_change_all_weights_with_inc_code
  is \<open>uncurry mop_imp_change_all_weights_with_inc\<close>
  :: \<open>dpfloat_assn\<^sup>k *\<^sub>a (hp_assn \<times>\<^sub>a dpfloat_assn)\<^sup>d \<rightarrow>\<^sub>a hp_assn \<times>\<^sub>a dpfloat_assn\<close>
  unfolding mop_imp_change_all_weights_with_inc_def
  by sepref

sepref_register EVSIDS.mop_hm_change_all_weights_with_inc

lemmas [sepref_fr_rules] =
  mop_imp_change_all_weights_with_inc_code.refine
    [FCOMP mop_imp_change_all_weights_with_inc_mop_hm_change_all_weights_with_inc2,
     unfolded hr_comp_assoc[symmetric] evsids_assn_def[symmetric]]

sepref_def evsids_push_literal_impl
  is \<open>uncurry evsids_push_literal\<close>
  :: \<open>atom_assn\<^sup>k *\<^sub>a evsids_assn2\<^sup>d \<rightarrow>\<^sub>a evsids_assn2\<close>
  unfolding evsids_push_literal_def evsids_assn2_def
  by sepref

definition bottom_evsids0 :: \<open>_\<close> where
  \<open>bottom_evsids0 = ((replicate 0 None, replicate 0 None, replicate 0 None, replicate 0 None, replicate 0 0, None))\<close>

definition bottom_evsids :: \<open>_\<close> where
  \<open>bottom_evsids = (bottom_evsids0, None)\<close>

sepref_def bottom_evsids0_impl
  is \<open>uncurry0 (RETURN bottom_evsids0)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a hp_assn\<close>
  unfolding bottom_evsids0_def
  apply (rewrite in \<open>(_, _, _, _, \<hole>, _)\<close> larray_fold_custom_replicate)
  unfolding hp_assn_def atom.fold_option array_fold_custom_replicate
    al_fold_custom_empty[where 'l=64]
  apply (annot_snat_const \<open>TYPE(64)\<close>)
  by sepref

definition empty_evsids0 where
  \<open>empty_evsids0 = ({#}, {#}, \<lambda>_::nat. 0::double\<^sub>p)\<close>

definition empty_evsids where
  \<open>empty_evsids = (empty_evsids0, 1::double\<^sub>p)\<close>

lemma bottom_evsids0:
  \<open>(uncurry0 (RETURN bottom_evsids0), uncurry0 (RETURN empty_evsids0)) \<in> 
   unit_rel \<rightarrow>\<^sub>f \<langle>((\<langle>\<langle>nat_rel\<rangle>option_rel, \<langle>Id\<rangle>option_rel\<rangle>pairing_heaps_rel)) O
   acids_encoded_hmrel\<rangle>nres_rel\<close>
proof -
  have [intro!]: \<open>Me \<in># {#} \<Longrightarrow> False\<close>for Me
    by auto
  have 1: \<open>(({#}, (\<lambda>_. None, \<lambda>_. None, \<lambda>_. None, \<lambda>_. None, \<lambda>_. None), None), empty_evsids0) \<in> acids_encoded_hmrel\<close>
    by (auto simp: acids_encoded_hmrel_def bottom_evsids0_def pairing_heaps_rel_def map_fun_rel_def
      EVSIDS.hmrel_def encoded_hp_prop_list_conc_def encoded_hp_prop_def empty_outside_def empty_evsids0_def
      intro!: relcompI)

  show ?thesis
    unfolding uncurry0_def
    apply (intro frefI nres_relI)
    apply (auto intro!:  relcompI[OF _ 1])
    by(auto simp: acids_encoded_hmrel_def bottom_evsids0_def pairing_heaps_rel_def map_fun_rel_def
      EVSIDS.hmrel_def encoded_hp_prop_list_conc_def encoded_hp_prop_def empty_outside_def)
qed

lemmas [sepref_fr_rules] =
  bottom_evsids0_impl.refine[FCOMP bottom_evsids0, unfolded hr_comp_assoc[symmetric] evsids_assn_def[symmetric]]

sepref_def empty_evsids_code
  is \<open>uncurry0 (RETURN empty_evsids)\<close>
  :: \<open>unit_assn\<^sup>k \<rightarrow>\<^sub>a evsids_assn2\<close>
  unfolding empty_evsids_def evsids_assn2_def
  by sepref

schematic_goal free_evsids_assn[sepref_frame_free_rules]: \<open>MK_FREE evsids_assn ?a\<close>
  unfolding evsids_assn_def hp_assn_def
  by synthesize_free


schematic_goal free_evsids_assn2[sepref_frame_free_rules]: \<open>MK_FREE evsids_assn2 ?a\<close>
  unfolding evsids_assn2_def
  by synthesize_free

sepref_def free_evsids
  is \<open>mop_free\<close>
  :: \<open>evsids_assn2\<^sup>d \<rightarrow>\<^sub>a unit_assn\<close>
  by sepref

lemma free_evsids_assn2': \<open>MK_FREE evsids_assn2 free_evsids\<close>
  unfolding free_evsids_def
  by (rule back_subst[of \<open>MK_FREE evsids_assn2\<close>, OF free_evsids_assn2])
    (auto intro!: ext)

(*New: We need a sepref_def for the decay, since acids didn't have that*)
sepref_def evsids_decay_impl
  is evsids_decay
  :: \<open>evsids_assn2\<^sup>d \<rightarrow>\<^sub>a evsids_assn2\<close>
  unfolding evsids_decay_def evsids_assn2_def
  by sepref

end
