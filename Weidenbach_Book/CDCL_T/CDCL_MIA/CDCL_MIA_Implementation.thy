theory CDCL_MIA_Implementation
  imports CDCL_MIA_Interp
begin

term \<open>mixed_cs_solver\<close>

(*
definition decide_mia_formula :: "'c :: lira_solver_config \<Rightarrow> var list \<Rightarrow> var mia_formula \<Rightarrow>
  (rat valuation \<times> (var \<Rightarrow> bool)) option" where
  "decide_mia_formula c Is f = (let II = int_vars_of_list Is; I = int_vars_set II in
     decide_mia_formula_main c II Mapping.empty Mapping.empty [] [to_kf I (tighten_mf I f)])"

theorem decide_mia_formula_sat: assumes "decide_mia_formula c Is f = Some (v, \<beta>)"
  shows "sat_mf (of_rat_val v) Is \<beta> f"
proof -
  from decide_mia_formula_main_sat(1)[OF assms[unfolded decide_mia_formula_def Let_def int_vars_set_of_list] cm_inv_empty]
    wf_to_kf
  have int: "of_rat_val v \<Turnstile>\<^sub>r\<^sub>m\<^sub>c\<^sub>s ({}, set Is)"
    and sat: "sat_kf (of_rat_val v) \<beta> (to_kf (set Is) (tighten_mf (set Is) f))" by auto
  from int have "\<forall> x \<in> set Is. of_rat_val v x \<in> \<int>" by simp
  from sat[unfolded sat_to_kf sat_tighten_mf[OF this]] int show ?thesis unfolding sat_mf_def by simp
qed

theorem decide_mia_formula_unsat: assumes "decide_mia_formula c Is f = None"
  shows "\<nexists> v \<beta>. sat_mf v Is \<beta> f"
proof
  assume "\<exists> v \<beta>. sat_mf v Is \<beta> f"
  then obtain v \<beta> where int: "v \<Turnstile>\<^sub>r\<^sub>m\<^sub>c\<^sub>s ({}, set Is)" and sat: "sat_mf_struct v \<beta> f"
    unfolding sat_mf_def by blast
  from int have ints: "\<forall> x \<in> set Is. v x \<in> \<int>" by simp
  from sat have "sat_kf v \<beta> (to_kf (set Is) (tighten_mf (set Is) f))"
    unfolding sat_to_kf sat_tighten_mf[OF ints] .
  with decide_mia_formula_main_unsat(1)[OF assms[unfolded decide_mia_formula_def Let_def int_vars_set_of_list] cm_inv_empty _ int[folded int_vars_set_of_list]
      sat_bm_empty sat_cm_empty]
    wf_to_kf show False by auto
qed
*)

end