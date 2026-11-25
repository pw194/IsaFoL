theory CDCL_MIA_Implementation_Alt
  imports CDCL_MIA_Interp CDCL_T.DPLL_T_Implementation
begin

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

definition is_EQ_c :: \<open>constraint \<Rightarrow> bool\<close> where
  \<open>is_EQ_c c = (\<exists>p r. c = (EQ p r))\<close>

fun is_EQ_mf :: \<open>'b mia_formula \<Rightarrow> bool\<close> where
  \<open>is_EQ_mf (Lit b c) = is_EQ_c c\<close> |
  \<open>is_EQ_mf _ = False\<close>

lemma is_EQ_is_arith_atom_EQ: \<open>is_EQ_mf F \<Longrightarrow> \<exists>b p r. F = (Lit b (EQ p r))\<close>
  by (cases F; auto simp: is_EQ_c_def)

definition is_EQ_atom :: \<open>'b mia_atom \<Rightarrow> bool\<close> where
  \<open>is_EQ_atom a = (\<exists>p r. a = (ArithAtom (EQ p r)))\<close>

definition is_EQ_lit :: \<open>'b mia_atom literal \<Rightarrow> bool\<close> where
  \<open>is_EQ_lit L = is_EQ_atom (atm_of L)\<close>

definition is_Arith_atom :: \<open>'b mia_atom \<Rightarrow> bool\<close> where
  \<open>is_Arith_atom a = (\<exists>c. a = (ArithAtom c))\<close>

definition is_Arith_lit :: \<open>'b mia_atom literal \<Rightarrow> bool\<close> where
  \<open>is_Arith_lit L = (is_Arith_atom (atm_of L))\<close>

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

(*TODO: CHANGE is_EQ_c because no code equation*)
fun constraint_list_of :: \<open>'b mia_atom literal list \<Rightarrow> constraint list\<close> where
  \<open>constraint_list_of [] = []\<close> |
  \<open>constraint_list_of (L#Ms) = (case L of 
      Pos (BoolAtom _) \<Rightarrow> constraint_list_of Ms |
      Neg (BoolAtom _) \<Rightarrow> constraint_list_of Ms |
      Pos (ArithAtom c) \<Rightarrow> (if is_EQ_c c then constraint_list_of Ms else c # constraint_list_of Ms) |
      Neg (ArithAtom c) \<Rightarrow> (if is_EQ_c c then constraint_list_of Ms else negate_ineq c # constraint_list_of Ms))\<close>

lemma negate_ineq_no_EQ: \<open>\<not> (is_EQ_c c) \<Longrightarrow> \<not> (is_EQ_c (negate_ineq c))\<close>
  by (cases c) auto

lemma constraint_list_of_no_EQ: \<open>\<forall> c \<in> set (constraint_list_of Ms). \<not> (is_EQ_c c)\<close>
proof (induction Ms)
  case Nil
  then show ?case by auto
next
  case (Cons a Ms)
  then show ?case proof (cases a)
    case (Pos x1)
    then show ?thesis 
      using Cons by (cases x1; auto split: prod.splits)
  next
    case (Neg x2)
    then show ?thesis 
      using negate_ineq_no_EQ Cons by (cases x2; auto split: prod.splits)
  qed 
qed
  
lemma testlemma: 
  assumes no_EQ: \<open>(\<forall>L \<in> set Ms. \<not> (is_EQ_lit L))\<close>
  shows \<open>(\<forall>c \<in> (set (constraint_list_of Ms)). v \<Turnstile>\<^sub>c c) \<longleftrightarrow> (\<forall>L \<in> set Ms. is_Arith_lit L \<longrightarrow> holds_lit v \<beta> L)\<close>
proof
  assume \<open>v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s set (constraint_list_of Ms)\<close>
  then show \<open>\<forall>L\<in>set Ms. is_Arith_lit L \<longrightarrow> holds_lit v \<beta> L\<close>
  proof(intro ballI impI)
    fix L
    assume A1: \<open>v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s set (constraint_list_of Ms)\<close> 
        and A2: \<open>L \<in> set Ms\<close> 
        and A3: \<open>is_Arith_lit L\<close>
    then show \<open>holds_lit v \<beta> L\<close>
    proof (cases L)
      case (Pos x1)
      then show ?thesis sorry
    next
      case (Neg x2)
      then show ?thesis sorry
    qed
  qed
next
  assume \<open>\<forall>L\<in>set Ms. is_Arith_lit L \<longrightarrow> holds_lit v \<beta> L\<close>
  then show \<open>v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s set (constraint_list_of Ms)\<close>
    sorry
qed

definition preprocess_formula :: \<open>var set \<Rightarrow> 'b mia_formula \<Rightarrow> 'b mia_atom literal list list\<close> where
  \<open>preprocess_formula I F = to_cnf (tighten_mf I (remove_equalities F))\<close>

(*MIA_Formula.sat_tighten_mf: \<forall>x\<in>?I. ?v x \<in> \<int> \<Longrightarrow> sat_mf_struct ?v ?\<beta> (tighten_mf ?I ?f) = sat_mf_struct ?v ?\<beta> ?f*)
lemma preprocess_formula_correct: \<open>(\<forall>x \<in> I. v x \<in> \<int>) \<Longrightarrow> sat_mf_struct v \<beta> F \<longleftrightarrow> holds_cnf v \<beta> (preprocess_formula I F)\<close>
  by (metis preprocess_formula_def remove_equalities_correct sat_tighten_mf to_cnf_correct)

definition mia_\<T>_solver :: \<open>'c :: lira_solver_config \<Rightarrow> int_vars \<Rightarrow> var mia_atom literal list \<Rightarrow> bool\<close> where
  \<open>mia_\<T>_solver c Is = (\<lambda>Ms. \<not> Option.is_none (mixed_cs_solver c (constraint_list_of Ms) Is))\<close>

thm mixed_cs_solver_unsat
lemma mia_solver_correct: \<open>theory_problem.\<T>_solver_correct theory_check_mia (mia_\<T>_solver c Is) (int_vars_set Is) (preprocess_formula (int_vars_set Is) F)\<close>
proof (intro theory_problem.\<T>_solver_correctI[OF theory_mia.theory_problem_axioms])
  fix Ms
  assume cons:  \<open>consistent_interp (set Ms)\<close> 
      and atms: \<open>atm_of ` set Ms \<subseteq> atms_of_mm (mset (map mset (preprocess_formula (int_vars_set Is) F)))\<close>
  show \<open>mia_\<T>_solver c Is Ms \<longleftrightarrow> theory_check_mia (set Ms) (int_vars_set Is)\<close>
  proof
    assume \<open>mia_\<T>_solver c Is Ms\<close>
    then show \<open>theory_check_mia (set Ms) (int_vars_set Is)\<close>
      sorry
  next
    assume \<T>_cons: \<open>theory_check_mia (set Ms) (int_vars_set Is)\<close>
    then obtain v \<beta> where integral: \<open>(wf_integral v (int_vars_set Is))\<close> 
                         and holds: \<open>(\<forall>L \<in> (set Ms). holds_lit v \<beta> L)\<close>
      by (auto simp: theory_check_mia_def)
    show \<open>mia_\<T>_solver c Is Ms\<close>
    proof (rule ccontr)
      assume neg: \<open>\<not> mia_\<T>_solver c Is Ms\<close>
      then have noV: \<open>\<And>v. \<not> v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set (constraint_list_of Ms), int_vars_set Is)\<close> 
            and noW: \<open>\<And> w. \<not> w \<Turnstile>\<^sub>r\<^sub>m\<^sub>c\<^sub>s (set (constraint_list_of Ms), int_vars_set Is)\<close>
        using mixed_cs_solver_unsat(1) apply (metis Option.is_none_def mia_\<T>_solver_def)
        using mixed_cs_solver_unsat(2) neg
        by (metis Option.is_none_def mia_\<T>_solver_def) 
      then show \<open>False\<close>
        using neg integral holds unfolding mia_\<T>_solver_def
        using satisfies_real_mixed_constraints.simps sorry 
    qed
  qed
qed

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
  sorry

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