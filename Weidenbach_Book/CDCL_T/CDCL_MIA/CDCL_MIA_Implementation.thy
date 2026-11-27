theory CDCL_MIA_Implementation
  imports CDCL_MIA_Interp CDCL_T.DPLL_T_Implementation
begin

definition cnf_disj :: \<open>'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list\<close> where
  \<open>cnf_disj F1 F2 = [C1 @ C2. C1 \<leftarrow> F1, C2 \<leftarrow> F2]\<close>

fun to_cnf :: \<open>'b mia_formula \<Rightarrow> 'b mia_atom literal list list\<close> where
  \<open>to_cnf (Lit b c) = [[lit_of_arith_atom b c]]\<close> |
  \<open>to_cnf (BVar b x) = [[lit_of_bool_atom b x]]\<close> |
  \<open>to_cnf (Conj FS) = concat (map to_cnf FS)\<close> |
  \<open>to_cnf (Disj FS) = foldr cnf_disj (map to_cnf FS) [[]]\<close>

definition holds_cnf :: \<open>(nat \<Rightarrow> real) \<Rightarrow> ('a \<Rightarrow> bool) \<Rightarrow> 'a mia_atom literal list list \<Rightarrow> bool\<close> where
  \<open>holds_cnf v \<beta> CS = (\<forall>C\<in>set CS. \<exists>L \<in> set C. holds_lit v \<beta> L)\<close>

lemma cnf_disj_sem: \<open>(holds_cnf v \<beta> (cnf_disj F1 F2)) \<longleftrightarrow> ((holds_cnf v \<beta> F1) \<or> (holds_cnf v \<beta> F2))\<close>
   by (auto simp: holds_cnf_def cnf_disj_def; fastforce)

lemma cnf_foldr: \<open>(holds_cnf v \<beta> (foldr cnf_disj FS [[]])) \<longleftrightarrow> (\<exists>f\<in>set FS. holds_cnf v \<beta> f)\<close>
proof (induction FS)
  case Nil
  then show ?case by (auto simp: holds_cnf_def)
next
  case (Cons a FS)
  then show ?case by (auto simp: cnf_disj_sem)
qed

lemma to_cnf_correct: \<open>sat_mf_struct v \<beta> F \<longleftrightarrow> holds_cnf v \<beta> (to_cnf F)\<close>
proof (induction F)
  case (Conj x)
  then show ?case unfolding holds_cnf_def by auto
next
  case (Disj x)
  then show ?case by (auto simp: cnf_foldr)
next
  case (Lit x1a x2a)
  then show ?case 
    unfolding holds_cnf_def using literal.inject(2) by fastforce
next
  case (BVar x1a x2a)
  then show ?case unfolding holds_cnf_def using literal.inject(2) by fastforce
qed

definition cnf :: \<open>'b mia_formula \<Rightarrow> 'b mia_atom clauses\<close> where
  \<open>cnf F = mset (map mset (to_cnf F))\<close>

lemma cnf_correct: \<open>sat_mf_struct v \<beta> F \<longleftrightarrow> (\<forall>C \<in># cnf F. \<exists>L \<in># C. holds_lit v \<beta> L)\<close>
  by (auto simp: cnf_def to_cnf_correct holds_cnf_def)

lemma sat_conj: \<open>sat_mf_struct v \<beta> (Conj (map lit_to_mf Ms)) \<longleftrightarrow> (\<forall>L \<in> set Ms. holds_lit v \<beta> L)\<close>
proof (induction Ms)
  case Nil
  then show ?case by auto
next
  case (Cons a Ms)
  then show ?case
    by (simp add: lit_to_mf_correct) 
qed

definition mia_\<T>_solver :: \<open>'c :: lira_solver_config \<Rightarrow> var list \<Rightarrow> var mia_atom literal list \<Rightarrow> ((nat \<Rightarrow> rat) \<times> (nat \<Rightarrow> bool)) option\<close> where
  \<open>mia_\<T>_solver c Is = (\<lambda>Ms. decide_mia_formula c Is (Conj (map lit_to_mf Ms)))\<close>

thm decide_mia_formula_unsat
lemma mia_solver_iff:
  \<open>(\<not> Option.is_none (mia_\<T>_solver c Is Ms)) \<longleftrightarrow> theory_check_mia (set Ms) (set Is)\<close>
proof
  assume \<open>\<not> Option.is_none (mia_\<T>_solver c Is Ms)\<close>
  then obtain v \<beta> where sat: \<open>sat_mf v Is \<beta> (Conj (map lit_to_mf Ms))\<close>
    using decide_mia_formula_sat unfolding mia_\<T>_solver_def
    by (metis is_none_code(1) option.exhaust surj_pair)  
  show \<open>theory_check_mia (set Ms) (set Is)\<close>
    unfolding theory_check_mia_def 
  proof (intro exI[of _ v] exI[of _ \<beta>] conjI)
    show \<open>wf_integral v (set Is)\<close>
      using sat unfolding sat_mf_def by auto 
  next
    show \<open>Ball (set Ms) (holds_lit v \<beta>)\<close>
      using sat unfolding sat_mf_def using sat_conj by blast 
  qed
next
  assume A1: \<open>theory_check_mia (set Ms) (set Is)\<close>
  then obtain v \<beta> where integral: \<open>wf_integral v (set Is)\<close> \<open>Ball (set Ms) (holds_lit v \<beta>)\<close>
    by (auto simp: theory_check_mia_def)
  then have con: \<open>sat_mf_struct v \<beta> (Conj (map lit_to_mf Ms))\<close>
    using sat_conj by blast 
  show \<open>\<not> Option.is_none (mia_\<T>_solver c Is Ms)\<close>
  proof
    assume \<open>Option.is_none (mia_\<T>_solver c Is Ms)\<close>
    then have \<open>\<nexists>v \<beta>. sat_mf v Is \<beta> (Conj (map lit_to_mf Ms))\<close>
      unfolding mia_\<T>_solver_def using decide_mia_formula_unsat by (metis Option.is_none_def) 
    then show \<open>False\<close>
      using integral con unfolding sat_mf_def
      by (meson empty_iff satisfies_real_mixed_constraints.simps) 
  qed
qed

corollary mia_solver_correct:
  \<open>theory_problem.\<T>_solver_correct theory_check_mia
     (\<lambda>Ms. \<not> Option.is_none (mia_\<T>_solver c Is Ms)) (set Is) N\<close>
proof (intro theory_problem.\<T>_solver_correctI[OF theory_mia.theory_problem_axioms])
  fix Ms
  show \<open>(\<not> Option.is_none (mia_\<T>_solver c Is Ms)) = theory_check_mia (set Ms) (set Is)\<close>
    using mia_solver_iff by auto
qed

definition dpll_mia :: \<open>'c :: lira_solver_config \<Rightarrow> var list \<Rightarrow> var mia_formula \<Rightarrow> ((nat \<Rightarrow> rat) \<times> (nat \<Rightarrow> bool)) option\<close> where
  \<open>dpll_mia c Is F = (let N = to_cnf F;
      (M, _) = DPLL_T_partial (\<lambda>Ms. \<not> Option.is_none (mia_\<T>_solver c Is Ms)) ([], N);
      Ms = map lit_of M
    in if \<forall>C \<in> set N. \<exists>L \<in> set C. L \<in> set Ms then mia_\<T>_solver c Is Ms else None)\<close>

thm decide_mia_formula_sat
theorem dpll_mia_formula_sat: 
  assumes "dpll_mia c Is F = Some (v, \<beta>)"
  shows "sat_mf (of_rat_val v) Is \<beta> F"
proof -
  define N where \<open>N = to_cnf F\<close>
  obtain M N' where run: \<open>DPLL_T_partial (\<lambda>Ms. \<not> Option.is_none (mia_\<T>_solver c Is Ms)) ([], N) = (M, N')\<close>
    using assms N_def unfolding dpll_mia_def by (metis (lifting) prod.exhaust)
  define Ms where \<open>Ms = map lit_of M\<close>
  have sat: \<open>\<forall>C \<in> set N. \<exists>L \<in> set C. L \<in> set Ms\<close> 
  and vals: \<open>mia_\<T>_solver c Is Ms = Some (v, \<beta>)\<close>
    using assms run
    unfolding dpll_mia_def N_def Ms_def
    by (auto simp: Let_def split: if_splits prod.splits)
  then have some_vals: \<open>decide_mia_formula c Is (Conj (map lit_to_mf Ms)) = Some (v, \<beta>)\<close>
    by (simp add: mia_\<T>_solver_def) \<comment> \<open>Our \<T>_solver gave the valuations\<close>
  then have satconjmf: \<open>sat_mf (of_rat_val v) Is \<beta> (Conj (map lit_to_mf Ms))\<close>
    by (rule decide_mia_formula_sat) \<comment> \<open>Using René's theorem\<close>
  then have satconj: \<open>sat_mf_struct (of_rat_val v) \<beta> (Conj (map lit_to_mf Ms))\<close>
    by (auto simp: sat_mf_def) \<comment> \<open>By definition\<close>
  then have all: \<open>(\<forall>L \<in> set Ms. holds_lit (of_rat_val v) \<beta> L)\<close>
    using sat_conj by blast
  show \<open>sat_mf (of_rat_val v) Is \<beta> F\<close>
    unfolding sat_mf_def
    using N_def all sat satconjmf by (metis holds_cnf_def sat_mf_def to_cnf_correct) 
qed

thm disjE
thm decide_mia_formula_unsat
theorem decide_mia_formula_unsat: 
  assumes "dpll_mia c Is F = None"
  shows "\<nexists> v \<beta>. sat_mf v Is \<beta> F"
proof 
  define N where \<open>N = to_cnf F\<close>
  obtain M N' where run: \<open>DPLL_T_partial (\<lambda>Ms. \<not> Option.is_none (mia_\<T>_solver c Is Ms)) ([], N) = (M, N')\<close>
    using assms N_def[symmetric] unfolding dpll_mia_def by (metis (lifting) prod.exhaust)
  define Ms where \<open>Ms = map lit_of M\<close>
  have dis: \<open>\<not>(\<forall>C \<in> set N. \<exists>L \<in> set C. L \<in> set Ms) \<or> (mia_\<T>_solver c Is Ms = None)\<close> \<comment> \<open>Either we have a propositional conflict or the theory rejects, used to split on later\<close>
    using run assms N_def Ms_def unfolding dpll_mia_def 
    by (auto simp: Let_def split: if_splits prod.splits)
  assume \<open>\<exists>v \<beta>. sat_mf v Is \<beta> F\<close>
  then obtain v \<beta> where sat: \<open>sat_mf v Is \<beta> F\<close> by auto
  then have clauses: \<open>holds_cnf v \<beta> N\<close>
    unfolding sat_mf_def N_def using to_cnf_correct by auto
  have integral: \<open>wf_integral v (set Is)\<close>
    using sat by (auto simp: sat_mf_def)
  have sat_t: \<open>theory_mia.satisfiable\<^sub>\<T> (set Is) (set_mset (mset (map mset N)))\<close>
    using satisfiable\<^sub>\<T>_iff_model integral clauses using N_def by (metis cnf_correct cnf_def to_cnf_correct)
  have init: \<open>dpll\<^sub>W_all_inv (theory_mia.state\<^sub>\<T> (set Is) (toS [] N))\<close>
    by (rule theory_mia.dpll\<^sub>W_all_inv_state\<^sub>\<T>_init)
  have solver: \<open>theory_problem.\<T>_solver_correct theory_check_mia
                  (\<lambda>Ms. \<not> Option.is_none (mia_\<T>_solver c Is Ms)) (set Is) N\<close>
    by (rule theory_problem.\<T>_solver_correctI[OF theory_mia.theory_problem_axioms]; simp add: mia_solver_iff)
  have NN: \<open>N = N'\<close>
    using theory_problem.DPLL_T_partial_inv_fix(3)[OF theory_mia.theory_problem_axioms init run]
      solver by blast
  then have model: \<open>(M \<Turnstile>asm mset (map mset N) \<and> theory_check_mia (lits_of_l M) (set Is))\<close> \<comment> \<open>Goal for the contradictions\<close>
    using theory_problem.DPLL_T_partial_correct[OF theory_mia.theory_problem_axioms run, of M \<open>((mset (map mset N)))\<close> \<open>(set Is)\<close>]
    using sat_t solver by blast 
  from dis show \<open>False\<close>
  proof (elim disjE)
    assume \<open>\<not> (\<forall>C\<in>set N. \<exists>L\<in>set C. L \<in> set Ms)\<close>
    then show \<open>False\<close>
      using model Ms_def 
      by (simp add: true_annots_true_cls true_clss_def true_cls_def lits_of_def; blast)
  next
    have \<open>(set Ms) = lits_of_l M\<close>
      using Ms_def by (simp add: lits_of_def) 
    then have \<open>(\<not> Option.is_none (mia_\<T>_solver c Is Ms))\<close>
      using model mia_solver_iff[of c Is Ms] Ms_def by auto 
    then have con: \<open>mia_\<T>_solver c Is Ms \<noteq> None\<close>
      by (metis is_none_simps(1)) 
    assume \<open>mia_\<T>_solver c Is Ms = None\<close>
    then show \<open>False\<close>
      using con by auto 
  qed
qed

(*Code gen test*)
derive (eq) ceq literal
derive (no) ccompare literal
derive (dlist) set_impl literal

derive (eq) ceq mia_atom
derive (no) ccompare mia_atom
derive (dlist) set_impl mia_atom

derive (eq) ceq annotated_lit
derive (no) ccompare annotated_lit
derive (dlist) set_impl annotated_lit

definition dpll_mia_default ::
  \<open>nat list \<Rightarrow> nat mia_formula \<Rightarrow> ((nat \<Rightarrow> rat) \<times> (nat \<Rightarrow> bool)) option\<close> where
  \<open>dpll_mia_default = dpll_mia Preprocess_Eqs\<close>

definition rat_of_integers :: \<open>integer \<Rightarrow> integer \<Rightarrow> rat\<close> where
  \<open>rat_of_integers a b = of_int (int_of_integer a) / of_int (int_of_integer b)\<close>

definition integers_of_rat :: \<open>rat \<Rightarrow> integer \<times> integer\<close> where
  \<open>integers_of_rat r = (case quotient_of r of (a, b) \<Rightarrow> (integer_of_int a, integer_of_int b))\<close>

export_code
  dpll_mia_default dpll_mia Preprocess_Eqs No_Preprocess
  Conj Disj Lit BVar
  LT GT LEQ GEQ EQ
  lp_of_list lp_monom
  nat_of_integer integer_of_nat rat_of_integers integers_of_rat
  in Haskell module_name MIA_Solver

definition F1 :: \<open>var mia_formula\<close> where
  \<open>F1 = Conj [(BVar True 0), Disj [(BVar False 0), (Lit True (GT (lp_monom 1 0) 5))]]\<close>

value \<open>map_option (\<lambda>(v, \<beta>). (v 0, \<beta> 0)) (dpll_mia Preprocess_Eqs [0] F1)\<close>

end