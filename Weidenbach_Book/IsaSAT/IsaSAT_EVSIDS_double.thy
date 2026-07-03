theory IsaSAT_EVSIDS_double
  imports Pairing_Heap_LLVM.Heaps_Abs
begin

section \<open>Experimental typedef for VSIDS\<close>
subsection \<open>The typedef\<close>
definition is_positive_float :: \<open>('e,'f) float \<Rightarrow> bool\<close> where
  \<open>is_positive_float x \<longleftrightarrow> (sign x = 0) \<and> \<not>is_nan x\<close>

lift_definition is_positive_double :: \<open>double \<Rightarrow> bool\<close> is is_positive_float .

text \<open>We define the type of positive doubles, excluding NaN\<close>
typedef double\<^sub>p = \<open>{x. is_positive_double x}\<close> 
  morphisms to_double from_double
proof
  show \<open>0 \<in> {x. is_positive_double x}\<close>
    unfolding is_positive_double_def is_positive_float_def
    by (simp add: zero_double.rep_eq) 
qed

setup_lifting type_definition_double\<^sub>p

subsection \<open>Pairing Heap Locale Properties\<close>
text \<open>We need to fulfill the same properties that the ACIDS interpretation already did. Furthermore,
      our type should be a linorder\<close>

instantiation double\<^sub>p :: ord
begin

lift_definition less_double\<^sub>p :: \<open>double\<^sub>p \<Rightarrow> double\<^sub>p \<Rightarrow> bool\<close> is \<open>(<)\<close> .
lift_definition less_eq_double\<^sub>p :: \<open>double\<^sub>p \<Rightarrow> double\<^sub>p \<Rightarrow> bool\<close> is \<open>(\<le>)\<close> .

instance ..
end

(* 
Proofs that all the pairing heap locale assumptions hold for this type. These include:
  1. Transitivity of le
  2. Transitivity of lt
  3. Totality of le
  4. \<le> iff < or =
*)

text \<open>Transitivity\<close>

lemma float_trans_le: \<open>(x::('e,'f) float) \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
  unfolding less_eq_float_def fle_def fcompare_def
  by (auto split: if_splits)

lemma double_trans_le: \<open>(x :: double) \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
  by transfer (rule float_trans_le)

lemma double\<^sub>p_trans_le: \<open>(x :: double\<^sub>p) \<le> y \<Longrightarrow> y \<le> z \<Longrightarrow> x \<le> z\<close>
  by transfer (rule double_trans_le)

lemma float_trans_lt: \<open>(x::('e,'f) float) < y \<Longrightarrow> y < z \<Longrightarrow> x < z\<close>
  unfolding less_float_def flt_def fcompare_def
  by (auto split: if_splits)

lemma double_trans_lt: \<open>(x :: double) < y \<Longrightarrow> y < z \<Longrightarrow> x < z\<close>
  by transfer (rule float_trans_lt)

lemma double\<^sub>p_trans_lt: \<open>(x :: double\<^sub>p) < y \<Longrightarrow> y < z \<Longrightarrow> x < z\<close>
  by transfer (rule double_trans_lt)

text \<open>Totality\<close>

lemma float\<^sub>p_total_le: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> (x \<le> y) \<or> (y \<le> x)\<close>
  unfolding is_positive_float_def less_eq_float_def fle_def fcompare_def
  by (auto split: if_splits)

lemma double_total_le: \<open>is_positive_double x \<Longrightarrow> is_positive_double y \<Longrightarrow> (x \<le> y) \<or> (y \<le> x)\<close>
  by transfer (rule float\<^sub>p_total_le)

lemma double\<^sub>p_total_le: \<open>(x::double\<^sub>p) \<le> y \<or> y \<le> x\<close>
  by transfer (rule double_total_le)

lemma float\<^sub>p_total_lt: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> ((x \<noteq> y) \<longrightarrow> (x < y) \<or> (y < x))\<close>
  unfolding is_positive_float_def less_float_def flt_def fcompare_def
  apply (simp split: if_splits)
  by (metis float_cases_finite infinity_simps'(2) is_infinity_alt sign_pos_iff_valof valof_almost_injective zero_neq_one) 

lemma double_total_lt: \<open>is_positive_double x \<Longrightarrow> is_positive_double y \<Longrightarrow> ((x \<noteq> y) \<longrightarrow> (x < y) \<or> (y < x))\<close>
  by transfer (rule float\<^sub>p_total_lt)

lemma double\<^sub>p_total_lt: \<open>(x \<noteq> y) \<longrightarrow> ((x::double\<^sub>p) < y \<or> (y < x))\<close>
  by transfer (rule double_total_lt)

text \<open>Iff\<close>

lemma float\<^sub>p_le_iff_le_or_eq: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> x \<le> y \<longleftrightarrow> x = y \<or> x < y\<close>
  unfolding is_positive_float_def less_float_def flt_def less_eq_float_def fle_def fcompare_def 
  by (smt (verit, best) ccode.simps(4) float_cases_finite float_class_consts(26) float_sel_simps(8) infinity_simps'(1,2) is_infinity_alt valof_almost_injective
      zero_neq_one)

lemma double_le_iff_le_or_eq: \<open>is_positive_double x \<Longrightarrow> is_positive_double y \<Longrightarrow> x \<le> y \<longleftrightarrow> x = y \<or> x < y\<close>
  by transfer (rule float\<^sub>p_le_iff_le_or_eq)

lemma double\<^sub>p_le_iff_le_or_eq: \<open>(x::double\<^sub>p) \<le> y \<longleftrightarrow> x = y \<or> x < y\<close>
  by transfer (rule double_le_iff_le_or_eq)

text \<open>Now we can finalize the interpretation with the new type\<close>
(*
interpretation VSIDS: hmstruct_with_prio where
  le = \<open>(\<ge>) :: double\<^sub>p \<Rightarrow> double\<^sub>p \<Rightarrow> bool\<close> and
  lt = \<open>(>)\<close>
  apply unfold_locales
  subgoal using double\<^sub>p_le_iff_le_or_eq by auto
  subgoal using transp_def double\<^sub>p_trans_le by auto
  subgoal using transp_def double\<^sub>p_trans_lt by auto
  subgoal using double\<^sub>p_total_lt by (simp add: totalpI)
  done
*)
subsection \<open>Linorder instantiation\<close>
text \<open>Test if we can actually show that \<^verbatim>\<open>double\<^sub>p\<close> is a linorder\<close>

lemma float_refl: \<open>is_positive_float x \<Longrightarrow> x \<le> x\<close>
  unfolding is_positive_float_def less_eq_float_def fle_def fcompare_def by (auto split: if_splits)

lemma double_refl: \<open>is_positive_double x \<Longrightarrow> x \<le> x\<close>
  by transfer (rule float_refl)

lemma double\<^sub>p_refl: \<open>(x::double\<^sub>p) \<le> x\<close>
  by transfer (rule double_refl)

(*TODO: Find the proper name for this property*)
lemma float_prop1: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> (x < y) \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)\<close>
  unfolding is_positive_float_def less_float_def flt_def less_eq_float_def fle_def fcompare_def
  by (auto split: if_splits) 

lemma double_prop1: \<open>is_positive_double x \<Longrightarrow> is_positive_double y \<Longrightarrow> (x < y) \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)\<close>
  by transfer (rule float_prop1)

lemma double\<^sub>p_prop1: \<open>((x::double\<^sub>p) < y) \<longleftrightarrow> (x \<le> y \<and> \<not> y \<le> x)\<close>
  by transfer (rule double_prop1)

lemma float\<^sub>p_antisym: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
  unfolding is_positive_float_def less_eq_float_def fle_def fcompare_def
  by (smt (verit, ccfv_threshold) IEEE.less_eq_float_def IEEE.less_float_def ccode.distinct(1,7) fcompare_def fle_def float\<^sub>p_le_iff_le_or_eq flt_def is_positive_float_def order.asym
      zero_neq_one)

lemma double_antisym: \<open>is_positive_double x \<Longrightarrow> is_positive_double y \<Longrightarrow> x \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
  by transfer (rule float\<^sub>p_antisym)

lemma double\<^sub>p_antisym: \<open>(x::double\<^sub>p) \<le> y \<Longrightarrow> y \<le> x \<Longrightarrow> x = y\<close>
  by transfer (rule double_antisym)

text \<open>The instantiations\<close>
instance double\<^sub>p :: order
  apply intro_classes
  subgoal using double\<^sub>p_prop1 by auto
  subgoal using double\<^sub>p_refl  by auto
  subgoal using double\<^sub>p_trans_le by auto
  subgoal using double\<^sub>p_antisym by auto
  done
  
instance double\<^sub>p :: linorder
  apply intro_classes
  subgoal using double\<^sub>p_total_le by auto
  done

instantiation double\<^sub>p :: zero
begin

lift_definition zero_double\<^sub>p :: double\<^sub>p is \<open>(0 :: double)\<close>
   by (simp add: is_positive_float_def is_positive_double_def zero_double.rep_eq)

instance ..

end

subsection \<open>EVSIDS arithmeic\<close>
text \<open>
In order to change to EVSIDS we need to acoomodate two different arithmetic operations:
  
  1. (+) for bumping scores
  2. (*) for growing the increment
  
We need to define these for the \<^verbatim>\<open>double\<^sub>p\<close> type and then prove their closure property
\<close>

subsubsection \<open>Addition (+)\<close>
text \<open>First we prove addition\<close>
lemma float\<^sub>p_plus_notNaN: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> \<not>is_nan(x + y)\<close>
  unfolding is_positive_float_def plus_float_def fadd_def
  apply (simp split: if_splits)
  by (metis float_class_consts(13,19,7) is_finite_closest nan_not_finite zerosign_def)

lemma threshold_pos: "0 < threshold TYPE(('e::len, 'f::len) float)"
  unfolding threshold_def
  by (smt (verit, best) divide_pos_pos less_divide_eq_1_pos power_less1_D zero_less_mult_iff)

lemma rounding_if_false: \<open>x \<ge> 0 \<Longrightarrow> - threshold TYPE(('e::len, 'f::len) float) < x\<close>
  using less_eq_real_def threshold_pos by auto 

lemma rounding_pos_sign0:
  fixes x :: real
  assumes \<open>x \<ge> 0\<close>
  shows \<open>sign (round To_nearest x :: ('e::len,'f::len) float) = 0
       \<or> is_zero (round To_nearest x :: ('e,'f) float)\<close>
proof (cases \<open>x \<ge> threshold TYPE(('e::len, 'f::len) float)\<close>)
  case True
  have x_is_infinity: \<open>(round To_nearest x) = (\<infinity>::('e,'f) float)\<close>
    using True assms leD rounding_if_false by auto 
  then show ?thesis
    by auto 
next
  case False
  note outer = False
  then show ?thesis
  proof (cases \<open>x \<le> - threshold TYPE(('e::len, 'f::len) float)\<close>)
    case True
    then show ?thesis using False assms by auto
  next
    case False
    have H1: \<open>(round To_nearest x) = (closest valof (\<lambda>a. even (fraction a)) {a. is_finite a} x :: ('e,'f) float)\<close>
      using outer False by auto  
    then show ?thesis
      by (smt (verit, del_insts) assms bound_at_worst_lemma fcc_le_cases float_class_consts(21) is_finite_closest is_zero_iff_valof0 outer valof_nonpos
          valof_zero(1)) 
  qed
qed

lemma float\<^sub>p_plus_sign0: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> sign (x + y) = 0\<close>
  unfolding plus_float_def fadd_def
  apply (cases \<open>is_infinity x\<close>; cases \<open>is_infinity y\<close>)
  apply (simp_all only: simp_thms is_positive_float_def if_True if_False roundmode.distinct if_cancel)
  by (metis add_increasing2 float_sel_simps(7) rounding_pos_sign0 valof_nonneg zerosign_def)

lemma float\<^sub>p_plus_closure: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> is_positive_float (x + y)\<close>
  by (simp add: is_positive_float_def float\<^sub>p_plus_notNaN float\<^sub>p_plus_sign0)

lemma double_plus_closure: \<open>is_positive_double x \<Longrightarrow> is_positive_double y \<Longrightarrow> is_positive_double (x + y)\<close>
  by transfer (rule float\<^sub>p_plus_closure)

instantiation double\<^sub>p :: plus
begin

lift_definition plus_double\<^sub>p :: \<open>double\<^sub>p \<Rightarrow> double\<^sub>p \<Rightarrow> double\<^sub>p\<close> is \<open>(+) :: double \<Rightarrow> double \<Rightarrow> double\<close>
  by transfer (rule double_plus_closure)

instance ..

end

subsubsection \<open>Multiplication (+)\<close>
text \<open>Next multiplication. Here we have an issue:\<close>
lemma \<open>is_nan ((0::('e,'f) float) * (\<infinity>::('e,'f) float))\<close> (*NaN \<notin> double\<^sub>p !!!*)
  unfolding times_float_def fmul_def 
  by (auto split: if_splits)

text \<open>Therefore, we need to specify our own multiplication that handles this pair explicitly\<close>
definition fmul\<^sub>p :: \<open>(('e,'f) float) \<Rightarrow> (('e,'f) float) \<Rightarrow> (('e,'f) float)\<close> (infixl \<open>*\<^sub>p\<close> 70) where
  \<open>fmul\<^sub>p x y = (if ((is_zero x \<and> is_infinity y) \<or> (is_infinity x \<and> is_zero y)) then 0 else x * y)\<close>
  
text \<open>Now we try to prove the closure of this custom multiplication \<^verbatim>\<open>fmul\<^sub>p\<close> the same way as before\<close>
lemma float\<^sub>p_times_notNaN: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> \<not>is_nan (x *\<^sub>p y)\<close>
  unfolding is_positive_float_def fmul\<^sub>p_def times_float_def fmul_def
  by (smt (verit, best) defloat_float_zerosign_round_finite float_cases' float_class_consts(12,19,7) infinity_float_def nan_not_finite round.simps(1)
      zerosign_def)

lemma float\<^sub>p_times_sign0: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> sign (x *\<^sub>p y) = 0\<close>
  apply (cases \<open>(is_zero x \<and> is_infinity y) \<or> (is_infinity x \<and> is_zero y)\<close>)
  subgoal by (auto simp add: is_positive_float_def fmul\<^sub>p_def)
  subgoal apply (simp only: simp_thms is_positive_float_def fmul\<^sub>p_def if_True if_False)
    unfolding times_float_def fmul_def
    apply (simp only: simp_thms is_positive_float_def fmul\<^sub>p_def if_True if_False)
    by (smt (verit) float_sel_simps(7) infinity_simps'(1) plus_infinity_conv rounding_pos_sign0 valof_nonneg zero_le_mult_iff zerosign_def)
  done
  
lemma float\<^sub>p_times_closure: \<open>is_positive_float x \<Longrightarrow> is_positive_float y \<Longrightarrow> is_positive_float (x *\<^sub>p y)\<close>
  by (simp add: is_positive_float_def float\<^sub>p_times_notNaN float\<^sub>p_times_sign0)

text \<open>Now we can lift the definition to double, and finally to \<^verbatim>\<open>double\<^sub>p\<close> to conclude\<close>
lift_definition dmul :: \<open>double \<Rightarrow> double \<Rightarrow> double\<close> is \<open>fmul\<^sub>p\<close> .
lift_definition dmul\<^sub>p :: \<open>double\<^sub>p \<Rightarrow> double\<^sub>p \<Rightarrow> double\<^sub>p\<close> is \<open>dmul\<close>
  by transfer (rule float\<^sub>p_times_closure)

subsection \<open>Helpers\<close>
text \<open>For some goals we need monotoicity of addition\<close>
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

lemma double_plus_mono: \<open>is_positive_double x \<Longrightarrow> is_positive_double y \<Longrightarrow> x \<le> x + y\<close>
  by transfer (rule float\<^sub>p_plus_mono)

lemma double_plus\<^sub>p_mono: \<open>(x::double\<^sub>p) \<le> x + y\<close>
  by transfer (rule double_plus_mono)

subsection \<open>Constants\<close>

text \<open>EVSIDS needs a so-called dampening constant in order to increase our increment
      Here I chose \<approx> 1.052631579\<close>
definition vsids_float_damping :: \<open>(11, 52) float\<close> where
 \<open>vsids_float_damping = Abs_float (0, 0, 0x0D79435E8AB61)\<close>

lemma damping_is_pos: \<open>is_positive_float vsids_float_damping\<close>
  unfolding is_positive_float_def vsids_float_damping_def is_nan_def
  by (auto simp add: sign.rep_eq exponent.rep_eq fraction.rep_eq Abs_float_inverse)

lift_definition vsids_double_damping :: double is vsids_float_damping .

lift_definition vsids_damping :: \<open>double\<^sub>p\<close> is vsids_double_damping
  by transfer (rule damping_is_pos)

text \<open>EVSIDS needs a limit that once exceeded, triggers a re-score of the scores and inc\<close>
text \<open>The below definition is inspired by CADICAL and corresponds to 
      2^500 \<approx> 3.273390607896142 \<cdot> 10^150\<close>

definition vsids_float_limit :: \<open>(11, 52) float\<close> where
  \<open>vsids_float_limit = Abs_float (0, of_nat 1523, 0)\<close>

lemma limit_is_pos: "is_positive_float vsids_float_limit"
  unfolding is_positive_float_def vsids_float_limit_def is_nan_def
  by (auto simp add: sign.rep_eq exponent.rep_eq fraction.rep_eq Abs_float_inverse)

lift_definition vsids_double_limit :: double is vsids_float_limit .

lift_definition vsids_limit :: \<open>double\<^sub>p\<close> is vsids_double_limit
  by transfer (rule limit_is_pos)

text \<open>For rescoring we also need a small constant that we multiply with.
      For now I go with \<approx> 1^-100\<close>
definition vsids_float_rescore_factor :: "(11,52) float" where
  "vsids_float_rescore_factor = Abs_float (0, of_nat 690, 0xBFF2EE48E0530)"

lemma emax_double: "emax TYPE((11,52) float) = 2047"
  unfolding emax_def by eval

lemma rescore_is_pos: \<open>is_positive_float vsids_float_rescore_factor\<close>
  unfolding is_positive_float_def vsids_float_rescore_factor_def is_nan_def
  by (auto simp add: sign.rep_eq exponent.rep_eq fraction.rep_eq Abs_float_inverse emax_double)

lift_definition vsids_double_rescore_factor :: double is vsids_float_rescore_factor .

lift_definition vsids_rescore_factor :: \<open>double\<^sub>p\<close> is vsids_double_rescore_factor
  by transfer (rule rescore_is_pos)

end