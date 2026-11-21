theory CDCL_MIA_Implementation
  imports CDCL_MIA_Interp CDCL_T.DPLL_T_Implementation
begin

subsection \<open>Preprocessing\<close>
fun translate_equality :: \<open>bool \<Rightarrow> linear_poly \<Rightarrow> rat \<Rightarrow> 'b mia_formula\<close> where
  \<open>translate_equality True p r = Conj [(Lit True (GEQ p r)), (Lit True (LEQ p r))]\<close> |
  \<open>translate_equality False p r = Disj [(Lit False (GEQ p r)), (Lit False (LEQ p r))]\<close>

lemma translate_equality_correct: \<open>sat_mf_struct v \<beta> (Lit b (EQ p r)) \<longleftrightarrow> sat_mf_struct v \<beta> (translate_equality b p r)\<close>
proof (cases \<open>b\<close>)
  case True
  then show ?thesis by auto 
next
  case False
  then show ?thesis by auto
qed

fun remove_equalities :: \<open>'b mia_formula \<Rightarrow> 'b mia_formula\<close> where
  \<open>remove_equalities (Lit b c)  = (case c of (EQ p r) \<Rightarrow> translate_equality b p r | _ \<Rightarrow> (Lit b c))\<close>  |
  \<open>remove_equalities (BVar b x) = (BVar b x)\<close> |
  \<open>remove_equalities (Conj FS)  = Conj (map remove_equalities FS)\<close>  |
  \<open>remove_equalities (Disj FS)  = Disj (map remove_equalities FS)\<close>

lemma remove_equalities_correct: \<open>sat_mf_struct v \<beta> F \<longleftrightarrow> sat_mf_struct v \<beta> (remove_equalities F)\<close>
proof (induction F)
  case (Conj x)
  then show ?case by auto
next
  case (Disj x)
  then show ?case by auto
next
  case (Lit x1a x2a)
  then show ?case 
    using translate_equality_correct by (cases \<open>x2a\<close>; auto; blast)
next
  case (BVar x1a x2a)
  then show ?case by auto
qed

subsection \<open>Naive formula translation\<close>
text \<open>To run the DPLL I want to get a mia formula into the shape of clauses.
      Moreover, the translation should respect formula entailment. I will do some simple
      pre-processing and a very naive CNF transformation.\<close>

definition cnf_disj :: \<open>'a list list \<Rightarrow> 'a list list \<Rightarrow> 'a list list\<close> where
  \<open>cnf_disj F1 F2 = [C1 @ C2. C1 \<leftarrow> F1, C2 \<leftarrow> F2]\<close>

fun to_cnf :: \<open>'b mia_formula \<Rightarrow> 'b mia_atom literal list list\<close> where
  \<open>to_cnf (Lit b c) = [[arith_atom b c]]\<close> |
  \<open>to_cnf (BVar b x) = [[bool_atom b x]]\<close> |
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

subsection \<open>The \<T>_solver\<close>
fun constraint_list_of :: \<open>'b mia_atom literal list \<Rightarrow> constraint list\<close> where
  \<open>constraint_list_of [] = []\<close> |
  \<open>constraint_list_of (x#xs) = (case x of 
      Pos (BoolAtom x) \<Rightarrow> constraint_list_of xs |
      Neg (BoolAtom x) \<Rightarrow> constraint_list_of xs |
      Pos (ArithAtom c) \<Rightarrow> c # constraint_list_of xs |
      Neg (ArithAtom c) \<Rightarrow> (case c of
          EQ p r \<Rightarrow> constraint_list_of xs |
          _ \<Rightarrow> negate_ineq c # constraint_list_of xs))\<close>

lemma constraint_list_of_correct:
  assumes \<open>(\<forall>L \<in> set Ms. holds_lit v \<beta> L)\<close>
  shows \<open>(\<forall>c \<in> set (constraint_list_of Ms). v \<Turnstile>\<^sub>c c)\<close>
  using assms proof (induction Ms)
  case Nil
  then show ?case by auto
next
  case (Cons a Ms)
  then show ?case 
    by (auto split: literal.splits mia_atom.splits constraint.splits)
qed

lemma constraint_list_to_correct:
  assumes \<open>\<forall>c' \<in> set (constraint_list_of Ms). v \<Turnstile>\<^sub>c c'\<close>
    and \<open>L \<in> set Ms\<close> and \<open>atm_of L = ArithAtom c\<close> and \<open>\<forall>p r. c \<noteq> EQ p r\<close>
  shows \<open>holds_lit v \<beta> L\<close>
  using assms proof (induction Ms)
  case Nil
  then show ?case by auto
next
  case (Cons a Ms)
  then show ?case 
    by (auto split: literal.splits mia_atom.splits constraint.splits)
qed

lemma constraint_list_of_pos_mem:
  \<open>Pos (ArithAtom c) \<in> set Ms \<Longrightarrow> c \<in> set (constraint_list_of Ms)\<close>
  by (induction Ms) (auto split: literal.splits mia_atom.splits constraint.splits)

definition mia_\<T>_solver :: \<open>'c :: lira_solver_config \<Rightarrow> int_vars \<Rightarrow> var mia_atom literal list \<Rightarrow> bool\<close> where
  \<open>mia_\<T>_solver c Is = (\<lambda>Ms. \<not> Option.is_none (mixed_cs_solver c (constraint_list_of Ms) Is))\<close>

thm mixed_cs_solver_sat
thm mixed_cs_solver_unsat

lemma mia_\<T>_solver_rejection: 
  assumes A1: \<open>\<not> mia_\<T>_solver c Is Ms\<close>
  shows \<open>\<not> theory_check_mia (set Ms) (int_vars_set Is)\<close>
proof 
  have unsatV: \<open>\<And>v. \<not> v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set (constraint_list_of Ms), int_vars_set Is)\<close> 
               and unsatW: \<open>\<And>w. \<not> w \<Turnstile>\<^sub>r\<^sub>m\<^sub>c\<^sub>s (set (constraint_list_of Ms), int_vars_set Is)\<close>
    using A1 unfolding mia_\<T>_solver_def
    apply (meson Option.is_none_def mixed_cs_solver_unsat(1))
    using A1 by (metis Option.is_none_def mia_\<T>_solver_def mixed_cs_solver_unsat(2))
  assume \<open>theory_check_mia (set Ms) (int_vars_set Is)\<close>
  then obtain v \<beta> where integral: \<open>(wf_integral v (int_vars_set Is))\<close> 
                  and holds: \<open>(\<forall>L \<in> (set Ms). holds_lit v \<beta> L)\<close>
    by (auto simp: theory_check_mia_def) 
  then show \<open>False\<close> 
    using A1 unfolding theory_check_mia_def
    using constraint_list_of_correct unsatW by fastforce
qed

lemma mia_\<T>_solver_acceptance:
  assumes cons: \<open>consistent_interp (set Ms)\<close> 
     and check: \<open>mia_\<T>_solver c Is Ms\<close>
     and no_EQ: \<open>\<forall>L \<in> set Ms. \<forall>p r. atm_of L \<noteq> ArithAtom (EQ p r)\<close>
  shows \<open>theory_check_mia (set Ms) (int_vars_set Is)\<close>
proof -
  define \<beta> where \<open>\<beta> = (\<lambda>b. Pos (BoolAtom b) \<in> set Ms)\<close>
  obtain v where val1: \<open>v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set (constraint_list_of Ms), (int_vars_set Is))\<close> and
                 val2: \<open>of_rat_val v \<Turnstile>\<^sub>r\<^sub>m\<^sub>c\<^sub>s (set (constraint_list_of Ms), int_vars_set Is)\<close>
    using check by (metis mia_\<T>_solver_def is_none_code(1) mixed_cs_solver_sat(1) mixed_rat_sol_imp_mixed_real_sol option.exhaust)
  have \<beta>_pos: \<open>holds_lit (of_rat_val v) \<beta> (Pos (BoolAtom b))\<close>
    if \<open>Pos (BoolAtom b) \<in> set Ms\<close> for b
    using that by (simp add: \<beta>_def)
  have \<beta>_neg: \<open>holds_lit (of_rat_val v) \<beta> (Neg (BoolAtom b))\<close>
    if \<open>Neg (BoolAtom b) \<in> set Ms\<close> for b
    using that cons by (auto simp: \<beta>_def consistent_interp_def)
  have sat: \<open>\<forall>c \<in> set (constraint_list_of Ms). of_rat_val v \<Turnstile>\<^sub>c c\<close>
    using val2 by simp
  show \<open>theory_check_mia (set Ms) (int_vars_set Is)\<close>
    unfolding theory_check_mia_def 
  proof (intro exI[of _ \<open>of_rat_val v\<close>], rule exI[of _ \<beta>], intro conjI)
    show \<open>wf_integral (of_rat_val v) (int_vars_set Is)\<close>
      using val1 val2 satisfies_real_mixed_constraints.simps by auto 
  next
    show \<open>Ball (set Ms) (holds_lit (of_rat_val v) \<beta>)\<close>
    proof
      fix x
      assume \<open>x \<in> set Ms\<close>
      then show \<open>holds_lit (of_rat_val v) \<beta> x\<close> 
      proof (induction x)
        case (Pos y)
        then show ?case
          proof (induction y)
            case (ArithAtom c)
            then show ?case
              by (simp add: constraint_list_of_pos_mem sat) 
          next
            case (BoolAtom x)
            then show ?case
              using \<beta>_pos by auto 
          qed
      next
        case (Neg y)
        then show ?case proof (induction y)
          case (ArithAtom c)
          then show ?case 
          proof (cases \<open>\<exists>p r. c = EQ p r\<close>)
            case True
            then show ?thesis
              using ArithAtom.prems no_EQ by auto 
          next
            case False
            then show ?thesis
              using ArithAtom.prems sat by (meson constraint_list_to_correct literal.sel(2)) 
          qed
        next
          case (BoolAtom x)
          then show ?case
            using \<beta>_neg by auto 
        qed
      qed
    qed
  qed
qed

subsection \<open>Top level procedure\<close>
definition preprocess_formula :: \<open>var set \<Rightarrow> 'b mia_formula \<Rightarrow> 'b mia_atom literal list list\<close> where
  \<open>preprocess_formula I F = to_cnf (tighten_mf I (remove_equalities F))\<close>

lemma mia_solver_iff:
  assumes \<open>N = preprocess_formula (int_vars_set II) F\<close>
  shows \<open>consistent_interp (set Ms) \<Longrightarrow> atm_of ` set Ms \<subseteq> atms_of_mm (mset (map mset N)) \<Longrightarrow>
         mia_\<T>_solver c II Ms \<longleftrightarrow> theory_check_mia (set Ms) (int_vars_set II)\<close>
  sorry

lemma translation_correct:
  \<open>theory_mia.satisfiable\<^sub>\<T> (set Is)
     (set_mset (mset (map mset (preprocess_formula (set Is) F)))) \<longleftrightarrow> (\<exists>v \<beta>. sat_mf v Is \<beta> F)\<close>
  sorry

(*MIA_Formula.sat_tighten_mf: \<forall>x\<in>?I. ?v x \<in> \<int> \<Longrightarrow> sat_mf_struct ?v ?\<beta> (tighten_mf ?I ?f) = sat_mf_struct ?v ?\<beta> ?f*)
lemma preprocess_formula_correct: \<open>(\<forall>x \<in> I. v x \<in> \<int>) \<Longrightarrow> sat_mf_struct v \<beta> F \<longleftrightarrow> holds_cnf v \<beta> (preprocess_formula I F)\<close>
  by (metis preprocess_formula_def remove_equalities_correct sat_tighten_mf to_cnf_correct)

definition dpll_mia :: \<open>'c :: lira_solver_config \<Rightarrow> var list \<Rightarrow> var mia_formula \<Rightarrow> ((nat \<Rightarrow> rat) \<times> (nat \<Rightarrow> bool)) option\<close> where
  \<open>dpll_mia c Is F = (let II = int_vars_of_list Is;
                          I = int_vars_set II;
                          N = (preprocess_formula I F) in
                          (let (M, _) = (DPLL_T_partial (mia_\<T>_solver c II) ([], N));
                              Ms = map lit_of M in if \<forall>C \<in> set N. \<exists>L \<in> set C. L \<in> set Ms
                                  then map_option (\<lambda>w. (w, \<lambda>b. Pos (BoolAtom b) \<in> set Ms))
                                      (mixed_cs_solver c (constraint_list_of Ms) II) else None))\<close>

subsection \<open>Final theorems\<close>
theorem dpll_mia_formula_sat: 
  assumes "dpll_mia c Is F = Some (v, \<beta>)"
  shows "sat_mf (of_rat_val v) Is \<beta> F"
proof -
  define II where \<open>II = int_vars_of_list Is\<close>
  define I where \<open>I = int_vars_set II\<close>
  define N where \<open>N = (preprocess_formula I F)\<close>
  obtain M N' where run: \<open>(M, N') = (DPLL_T_partial (mia_\<T>_solver c II) ([], N))\<close>
    by (metis prod.exhaust)
  define Ms where \<open>Ms = map lit_of M\<close>
  have model: \<open>\<forall>C \<in> set N. \<exists>L \<in> set C. L \<in> set Ms\<close>
   and beta: \<open>\<beta> = (\<lambda>b. Pos (BoolAtom b) \<in> set Ms)\<close>
    and Val: \<open>Some v = mixed_cs_solver c (constraint_list_of Ms) II\<close>
    using assms run[symmetric]
    unfolding dpll_mia_def
    by (auto simp: Let_def II_def[symmetric] I_def[symmetric] N_def[symmetric] Ms_def
             split: if_splits prod.splits)
  show \<open>sat_mf (of_rat_val v) Is \<beta> F\<close>
    unfolding sat_mf_def  sorry
qed

theorem decide_mia_formula_unsat: 
  assumes "dpll_mia c Is f = None"
  shows "\<nexists> v \<beta>. sat_mf v Is \<beta> f"
  sorry

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

export_code dpll_mia in Haskell


definition F1 :: \<open>var mia_formula\<close> where
  \<open>F1 = Conj [(BVar True 0), Disj [(BVar False 0), (Lit True (GT (lp_monom 1 0) 5))]]\<close>

value \<open>map_option (\<lambda>(v, \<beta>). (v 0, \<beta> 0)) (dpll_mia Preprocess_Eqs [0] F1)\<close>

end