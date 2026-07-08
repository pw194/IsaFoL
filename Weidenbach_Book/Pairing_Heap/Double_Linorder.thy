theory Double_Linorder
  imports Isabelle_LLVM.IICF Isabelle_LLVM.Float_Setup
begin



section \<open>EVSIDS doubles\<close>


(* Note: The following subsection is a courtesy by Peter Lammich *)
subsection \<open>Definitions and sepref setup\<close>

definition is_positive_float :: \<open>('e,'f) float \<Rightarrow> bool\<close> where
  \<open>is_positive_float x \<longleftrightarrow> (sign x = 0) \<and> \<not>is_nan x\<close>


typedef double\<^sub>p = \<open>{x::(11,52) float. is_positive_float x}\<close> 
  morphisms dp_to_float dp_from_float
  unfolding is_positive_float_def 
  using float_sel_simps(7) by blast

setup_lifting type_definition_double\<^sub>p

lift_definition is_zero\<^sub>p :: "double\<^sub>p \<Rightarrow> bool" is is_zero .
lift_definition is_infinity\<^sub>p :: "double\<^sub>p \<Rightarrow> bool" is is_infinity .


lemma dp_from_float_inverse'[simp]: "is_positive_float x \<Longrightarrow> dp_to_float (dp_from_float x) = x" by (simp add: dp_from_float_inverse)
lemmas [simp] = dp_to_float_inverse
lemma dp_to_float'[simp]: "is_positive_float (dp_to_float x)" using dp_to_float by blast
 
 
instantiation double\<^sub>p :: plus
begin

  lift_definition plus_double\<^sub>p :: \<open>double\<^sub>p \<Rightarrow> double\<^sub>p \<Rightarrow> double\<^sub>p\<close> is \<open>(+) :: (11,52) float \<Rightarrow> (11,52) float \<Rightarrow> (11,52) float\<close>
    unfolding is_positive_float_def
    by (auto simp: plus_float_def sign0_fadd is_nan_fadd)

  instance ..
end  


instantiation double\<^sub>p :: ord begin
  lift_definition less_eq_double\<^sub>p :: "double\<^sub>p \<Rightarrow> double\<^sub>p \<Rightarrow> bool" is \<open>(\<le>) :: (11,52) float \<Rightarrow> (11,52) float \<Rightarrow> _\<close> .
  lift_definition less_double\<^sub>p :: "double\<^sub>p \<Rightarrow> double\<^sub>p \<Rightarrow> bool" is \<open>(<) :: (11,52) float \<Rightarrow> (11,52) float \<Rightarrow> _\<close> .
  
  instance ..
end

instantiation double\<^sub>p :: times begin

  definition fmul\<^sub>p :: \<open>(('e,'f) float) \<Rightarrow> (('e,'f) float) \<Rightarrow> (('e,'f) float)\<close> where
    \<open>fmul\<^sub>p x y = (if ((is_zero x \<and> is_infinity y) \<or> (is_infinity x \<and> is_zero y)) then 0 else x * y)\<close>
    
  lift_definition times_double\<^sub>p :: \<open>double\<^sub>p \<Rightarrow> double\<^sub>p \<Rightarrow> double\<^sub>p\<close> is fmul\<^sub>p
    unfolding is_positive_float_def
    by (auto simp: fmul\<^sub>p_def times_float_def sign0_fmul is_nan_fmul)

  instance ..
end
  
definition "dp_const_aux w \<equiv> let f = float_of_fp64 w in if is_positive_float f then f else 0"
lift_definition const_double\<^sub>p :: "64 word \<Rightarrow> double\<^sub>p" is "dp_const_aux"
  unfolding dp_const_aux_def Let_def by (auto simp: is_positive_float_def)


instantiation double\<^sub>p :: zero begin
  lift_definition zero_double\<^sub>p :: double\<^sub>p is "0" unfolding is_positive_float_def by simp
  instance ..
end

instantiation double\<^sub>p :: one begin
  lift_definition one_double\<^sub>p :: double\<^sub>p is "1" unfolding is_positive_float_def by simp
  instance ..
end

sepref_register 
  "(+) :: double\<^sub>p \<Rightarrow> _"
  "(*) :: double\<^sub>p \<Rightarrow> _"
  "(\<le>) :: double\<^sub>p \<Rightarrow> _"
  "(<) :: double\<^sub>p \<Rightarrow> _"
  "0 :: double\<^sub>p"
  "1 :: double\<^sub>p"
  const_double\<^sub>p
  
definition \<open>float\<^sub>p_rel = br id (\<lambda>x. is_positive_float x)\<close>

definition "dpfloat_rel_aux \<equiv> br dp_from_float is_positive_float"

definition "dpfloat_rel \<equiv> dfloat_rel O dpfloat_rel_aux"

abbreviation "dpfloat_assn \<equiv> pure dpfloat_rel"


lemma rel2p_dpfloat_rel_aux[rel2p]: "rel2p dpfloat_rel_aux = cr_double\<^sub>p"
  unfolding cr_double\<^sub>p_def dpfloat_rel_aux_def in_br_conv rel2p_def by (auto simp: fun_eq_iff)

lemma p2rel_cr_double\<^sub>p[simp]: "p2rel cr_double\<^sub>p = dpfloat_rel_aux"
  unfolding cr_double\<^sub>p_def dpfloat_rel_aux_def p2rel_def by (auto simp: in_br_conv)


lemma dp_add_refine: "(mop_fadd, RETURN oo (+)) \<in> dpfloat_rel_aux \<rightarrow> dpfloat_rel_aux \<rightarrow> \<langle>dpfloat_rel_aux\<rangle>nres_rel" 
  unfolding mop_fadd_def nanize_float_def dpfloat_rel_aux_def
  by (auto 
    simp: in_br_conv pw_nres_rel_iff refine_pw_simps IEEE.plus_float_def is_nan_fadd 
      is_positive_float_def sign0_fadd plus_double\<^sub>p.abs_eq eq_onp_same_args) (* TODO: Looks like we prove invar-pres again here *)
  

definition "dpmul_pre a b \<equiv> (is_zero\<^sub>p a \<longrightarrow> \<not>is_infinity\<^sub>p b) \<and> (is_zero\<^sub>p b \<longrightarrow> \<not>is_infinity\<^sub>p a)"  
      
definition "mop_dpmul a b \<equiv> doN { ASSERT (dpmul_pre a b); RETURN (a*b) }"
      
lemma dp_mul_refine: "(mop_fmul, mop_dpmul) \<in> dpfloat_rel_aux \<rightarrow> dpfloat_rel_aux \<rightarrow> \<langle>dpfloat_rel_aux\<rangle>nres_rel" 
  unfolding mop_fmul_def mop_dpmul_def dpmul_pre_def
  apply refine_vcg
  unfolding nanize_float_def
  apply refine_vcg
  (* TODO: Clean up proof, this one is brute-force + sledgehammer *)
  unfolding dpfloat_rel_aux_def in_br_conv
  subgoal
    apply (clarsimp simp: is_nan_fmul times_float_def is_zero\<^sub>p.rep_eq is_infinity\<^sub>p.rep_eq is_positive_float_def) 
    by (metis nnan_ninf_eq_fin)
  subgoal
    apply (clarsimp simp: is_nan_fmul is_zero\<^sub>p.rep_eq is_infinity\<^sub>p.rep_eq is_positive_float_def) 
    by (metis (lifting) ext dp_from_float_inverse dp_to_float' eq_onp_same_args fmul\<^sub>p_def is_positive_float_def mem_Collect_eq nnan_nfin_eq_inf times_double\<^sub>p.abs_eq times_double\<^sub>p.rep_eq)
  done    
  
lemma dp_mul_refine': "(uncurry mop_fmul, uncurry (RETURN oo (*))) \<in> [uncurry dpmul_pre]\<^sub>f dpfloat_rel_aux \<times>\<^sub>r dpfloat_rel_aux \<rightarrow> \<langle>dpfloat_rel_aux\<rangle>nres_rel"
  apply (intro frefI; clarsimp)
  subgoal for a b a' b'
    using dp_mul_refine[THEN fun_relD, THEN fun_relD, of a a' b b']
    unfolding mop_dpmul_def
    by simp
  done
      
      
lemma dp_le_refine: "((\<le>), (\<le>)) \<in> dpfloat_rel_aux \<rightarrow> dpfloat_rel_aux \<rightarrow> bool_rel" 
  unfolding dpfloat_rel_aux_def
  by (auto simp: in_br_conv less_eq_double\<^sub>p.rep_eq)

lemma dp_lt_refine: "((<), (<)) \<in> dpfloat_rel_aux \<rightarrow> dpfloat_rel_aux \<rightarrow> bool_rel" 
  unfolding dpfloat_rel_aux_def
  by (auto simp: in_br_conv less_double\<^sub>p.rep_eq)
  
lemma dp_0_refine: "(op_fp64_0,0)\<in>dpfloat_rel_aux"  
  unfolding dpfloat_rel_aux_def
  by (auto simp: in_br_conv op_fp64_0_def zero_double\<^sub>p_def is_positive_float_def)
  
lemma dp_1_refine: "(op_fp64_1,1)\<in>dpfloat_rel_aux"  
  unfolding dpfloat_rel_aux_def
  by (auto simp: in_br_conv simp flip: float_of_fp64_1 simp: is_positive_float_def one_double\<^sub>p_def)
  
  
lemma const_doublep_refine: "(float_of_fp64, const_double\<^sub>p) \<in> [\<lambda>w. is_positive_float (float_of_fp64 w)]\<^sub>f word_rel \<rightarrow> dpfloat_rel_aux"  
  apply (intro frefI; clarsimp)
  unfolding dpfloat_rel_aux_def in_br_conv
  by (simp add: const_double\<^sub>p_def dp_const_aux_def)
  
        
context 
  notes [fcomp_norm_unfold] = dpfloat_rel_def[symmetric]
begin      
      
  lemmas [sepref_fr_rules] = 
    fadd_double_hnr[FCOMP dp_add_refine]
    fmul_double_hnr[FCOMP dp_mul_refine]
    fmul_double_hnr[FCOMP dp_mul_refine']
    fleq_d_hnr[FCOMP dp_le_refine]
    flt_d_hnr[FCOMP dp_lt_refine]

    op_fp64_0_ll.refine[FCOMP dp_0_refine]
    op_fp64_1_ll.refine[FCOMP dp_1_refine]
    float_of_fp64_hnr[FCOMP const_doublep_refine]

end    
    
  
definition "mop_dpconst w \<equiv> doN {ASSERT (is_positive_float (float_of_fp64 w)); RETURN (const_double\<^sub>p w) }"
  
sepref_register mop_dpconst

sepref_def mop_dpconst_impl [llvm_inline] is "mop_dpconst" :: "word_assn\<^sup>k \<rightarrow>\<^sub>a dpfloat_assn"
  unfolding mop_dpconst_def
  by sepref


experiment
begin

  sepref_definition test [llvm_code] is "\<lambda>a. doN {
    let b = a+1;
    b \<leftarrow> mop_dpmul a b; \<comment> \<open>mop-operation, includes assertion\<close>
    RETURN (0\<le>b \<and> b<1)
  }" :: "dpfloat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    by sepref

    
  sepref_definition test2 [llvm_code] is "\<lambda>a. doN {
    ASSERT (dpmul_pre a (a+1)); \<comment> \<open>Explicit assertion, proof is done during sepref (can be slower and harder to debug)\<close>
    RETURN (0 \<le> a*(a+1) \<and> a*(a+1) < 1)
  }" :: "dpfloat_assn\<^sup>k \<rightarrow>\<^sub>a bool1_assn"
    by sepref
    
      
  export_llvm test test2
    
end  

subsection \<open>Heap locale proofs\<close>

subsubsection \<open>Iff\<close>
lemma float\<^sub>p_le_iff_le_or_eq: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> x \<le> y \<longleftrightarrow> x = y \<or> x < y\<close>
  unfolding is_positive_float_def less_float_def flt_def less_eq_float_def fle_def fcompare_def 
  by (smt (verit, best) ccode.simps(4) float_cases_finite float_class_consts(26) float_sel_simps(8) 
        infinity_simps'(1,2) is_infinity_alt valof_almost_injective zero_neq_one)

lemma double\<^sub>p_le_iff_le_or_eq: \<open>(x::double\<^sub>p) \<le> y \<longleftrightarrow> x = y \<or> x < y\<close>
  by transfer (rule float\<^sub>p_le_iff_le_or_eq)

subsubsection \<open>Transitivity\<close>
lemma float\<^sub>p_trans_le: \<open>is_positive_float x 
                   \<Longrightarrow> is_positive_float y 
                   \<Longrightarrow> is_positive_float z 
                   \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
  unfolding is_positive_float_def less_eq_float_def fle_def fcompare_def
  using finite_infinity by (auto split: if_splits)

lemma double\<^sub>p_trans_le: \<open>(x :: double\<^sub>p) \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
  by transfer (rule float\<^sub>p_trans_le)

lemma float\<^sub>p_trans_lt: \<open>is_positive_float x 
                   \<Longrightarrow> is_positive_float y 
                   \<Longrightarrow> is_positive_float z 
                   \<Longrightarrow> x < y \<Longrightarrow> y < z \<Longrightarrow> x < z\<close>
  unfolding is_positive_float_def less_float_def flt_def fcompare_def
  using finite_infinity by (auto split: if_splits)
  

lemma double\<^sub>p_trans_lt: \<open>(x :: double\<^sub>p) < y \<Longrightarrow> y < z \<Longrightarrow> x < z\<close>
  by transfer (rule float\<^sub>p_trans_lt)

subsubsection \<open>Totality\<close>

lemma float\<^sub>p_total_le: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> (x \<le> y) \<or> (y \<le> x)\<close>
  unfolding is_positive_float_def less_eq_float_def fle_def fcompare_def
  using finite_infinity by (auto split: if_splits)

lemma double\<^sub>p_total_le: \<open>(x::double\<^sub>p) \<le> y \<or> y \<le> x\<close>
  by transfer (rule float\<^sub>p_total_le)

lemma float\<^sub>p_total_lt: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> ((x \<noteq> y) \<longrightarrow> (x < y) \<or> (y < x))\<close>
  unfolding is_positive_float_def less_float_def flt_def fcompare_def
  apply (simp split: if_splits)
  by (smt (verit) One_nat_def diff_zero float_distinct_finite(2) is_infinity_alt 
        sign_minus_float sign_neg_iff_valof val_zero valof_nonzero_injective zero_neq_one)
  
lemma double\<^sub>p_total_lt: \<open>(x \<noteq> y) \<longrightarrow> ((x::double\<^sub>p) < y \<or> (y < x))\<close>
  by transfer (rule float\<^sub>p_total_lt)

subsection \<open>Linorder\<close>
lemma float\<^sub>p_refl: \<open>is_positive_float x \<Longrightarrow> x \<le> x\<close>
  unfolding is_positive_float_def less_eq_float_def fle_def fcompare_def 
  by (auto split: if_splits)

lemma double\<^sub>p_refl: \<open>(x::double\<^sub>p) \<le> x\<close>
  by transfer (rule float\<^sub>p_refl)

lemma float\<^sub>p_less_le_not_le: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> (x < y) \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)\<close>
  unfolding is_positive_float_def less_float_def flt_def less_eq_float_def fle_def fcompare_def
  using finite_infinity by (auto split: if_splits) 

lemma double\<^sub>p_less_le_not_le: \<open>((x::double\<^sub>p) < y) \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)\<close>
  by transfer (rule float\<^sub>p_less_le_not_le)

lemma float\<^sub>p_antisym: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
  unfolding is_positive_float_def
  by (meson float\<^sub>p_le_iff_le_or_eq float\<^sub>p_less_le_not_le is_positive_float_def) 

lemma double\<^sub>p_antisym: \<open>(x::double\<^sub>p) \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
  by transfer (rule float\<^sub>p_antisym)

text \<open>The instantiations\<close>
instance double\<^sub>p :: order
  apply intro_classes
  subgoal using double\<^sub>p_less_le_not_le by auto
  subgoal using double\<^sub>p_refl  by auto
  subgoal using double\<^sub>p_trans_le by auto
  subgoal using double\<^sub>p_antisym by auto
  done

instance double\<^sub>p :: linorder
  apply intro_classes
  subgoal using double\<^sub>p_total_le by auto
  done

subsection \<open>Constants\<close>

text \<open>EVSIDS needs a limit that once exceeded, triggers a re-score of the scores and inc\<close>
text \<open>The below definition is inspired by CADICAL and corresponds to 
      2^500 \<approx> 3.273390607896142 \<cdot> 10^150\<close>
definition evsids_limit_word :: \<open>64 word\<close> where
  \<open>evsids_limit_word = 0x5F30000000000000\<close>

definition evsids_limit :: \<open>double\<^sub>p\<close> where
  \<open>evsids_limit = const_double\<^sub>p evsids_limit_word\<close>

text \<open>EVSIDS needs a rescore factor that is applied to all scores and inc, once any of them exceeds
      the limit above\<close>
text \<open>2^-500, for now a flip of the vsids_limit = 2^500\<close>
definition evsids_rescore_factor_word :: \<open>64 word\<close> where
  \<open>evsids_rescore_factor_word = 0x20B0000000000000\<close> 

definition evsids_rescore_factor :: \<open>double\<^sub>p\<close> where
  \<open>evsids_rescore_factor = const_double\<^sub>p evsids_rescore_factor_word\<close>

text \<open>EVSIDS needs a constant that increases our inc, in order to have the implicit decay happening\<close>
text \<open>Here I went with \<approx> 1/0.95 as the factor\<close>
definition evsids_decay_factor_word :: \<open>64 word\<close> where
  \<open>evsids_decay_factor_word = 0x3FF0D79435E53BC5\<close> 

definition evsids_decay_factor :: \<open>double\<^sub>p\<close> where
  \<open>evsids_decay_factor = const_double\<^sub>p evsids_decay_factor_word\<close>

subsection \<open>Helpers\<close>
text \<open>Monotonicity\<close>
lemma float\<^sub>p_plus_mono: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> x \<le> x + y\<close>
  unfolding is_positive_float_def plus_float_def fadd_def
  apply (cases \<open>is_infinity x\<close>; cases \<open>is_infinity y\<close>)
     apply (simp_all only: simp_thms is_positive_float_def if_True if_False roundmode.distinct if_cancel)
  subgoal by (simp add: float\<^sub>p_le_iff_le_or_eq is_positive_float_def) 
  subgoal by (simp add: float\<^sub>p_le_iff_le_or_eq is_positive_float_def)
  subgoal by (metis float_le_inf_simps(3) float_neg_sign infinity_simps'(1) is_infinity_alt) 
  subgoal by (smt (verit, ccfv_threshold) bound_at_worst_lemma defloat_float_zerosign_round_finite float_cases_finite float_class_consts(8) float_le float_le_inf_simps(3)
        infinity_float_def round.simps(1) signzero_zero threshold_pos val_zero valof_nonneg zerosign_def) 
  done

lemma double_plus\<^sub>p_mono: \<open>(x::double\<^sub>p) \<le> x + y\<close>
  by transfer (rule float\<^sub>p_plus_mono)

text \<open>Constant helpers\<close>
lemma evsids_limit_word_positive: \<open>is_positive_float (float_of_fp64 0x5F30000000000000)\<close>
  by eval

lemma evsids_limit_word_nonZero: \<open>\<not>is_zero (float_of_fp64 0x5F30000000000000)\<close>
  by eval

lemma evsids_limit_word_nonInf: \<open>\<not>is_infinity (float_of_fp64 0x5F30000000000000)\<close>
  by eval

lemma evsids_limit_nonZero: \<open>\<not>is_zero\<^sub>p evsids_limit\<close>
  by eval

lemma evsids_limit_nonInf: \<open>\<not>is_infinity\<^sub>p evsids_limit\<close>
  by eval

lemma mop_dpconst_evsids_limit[simp]:
  \<open>mop_dpconst evsids_limit_word = RETURN evsids_limit\<close>
  unfolding mop_dpconst_def evsids_limit_def evsids_limit_word_def
  by (simp add: evsids_limit_word_positive)

lemma evsids_rescore_factor_word_positive: \<open>is_positive_float (float_of_fp64 0x20B0000000000000)\<close>
  by eval

lemma evsids_rescore_factor_word_nonZero: \<open>\<not>is_zero (float_of_fp64 0x20B0000000000000)\<close>
  by eval

lemma evsids_rescore_factor_word_nonInf: \<open>\<not>is_infinity (float_of_fp64 0x20B0000000000000)\<close>
  by eval

lemma evsids_rescore_factor_nonZero: \<open>\<not>is_zero\<^sub>p evsids_rescore_factor\<close>
  by eval

lemma evsids_rescore_factor_nonInf: \<open>\<not>is_infinity\<^sub>p evsids_rescore_factor\<close>
  by eval

lemma mop_dpconst_evsids_rescore_factor[simp]:
  \<open>mop_dpconst evsids_rescore_factor_word = RETURN evsids_rescore_factor\<close>
  unfolding mop_dpconst_def evsids_rescore_factor_def evsids_rescore_factor_word_def
  by (simp add: evsids_rescore_factor_word_positive)

lemma evsids_decay_factor_word_positive: \<open>is_positive_float (float_of_fp64 0x3FF0D79435E53BC5)\<close>
  by eval

lemma evsids_decay_factor_word_nonZero: \<open>\<not>is_zero (float_of_fp64 0x3FF0D79435E53BC5)\<close>
  by eval

lemma evsids_decay_factor_word_nonInf: \<open>\<not>is_infinity (float_of_fp64 0x3FF0D79435E53BC5)\<close>
  by eval

lemma evsids_decay_factor_nonZero: \<open>\<not>is_zero\<^sub>p evsids_decay_factor\<close>
  by eval

lemma evsids_decay_factor_nonInf: \<open>\<not>is_infinity\<^sub>p evsids_decay_factor\<close>
  by eval

lemma mop_dpconst_evsids_decay_factor[simp]:
  \<open>mop_dpconst evsids_decay_factor_word = RETURN evsids_decay_factor\<close>
  unfolding mop_dpconst_def evsids_decay_factor_def evsids_decay_factor_word_def
  by (simp add: evsids_decay_factor_word_positive)


subsubsection \<open>Experiments\<close>

(*Experiment: Testing out mop_dpconst*)
experiment
begin
  sepref_definition test [llvm_code] is "\<lambda>a. doN {
    b \<leftarrow> mop_dpconst evsids_rescore_factor_word;
    mop_dpmul b a
  }" :: "dpfloat_assn\<^sup>k \<rightarrow>\<^sub>a dpfloat_assn"
    unfolding evsids_rescore_factor_word_def
    by sepref
    
  export_llvm test
end  

end