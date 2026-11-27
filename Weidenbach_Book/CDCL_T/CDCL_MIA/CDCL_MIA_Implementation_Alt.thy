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

fun is_EQ_c :: \<open>constraint \<Rightarrow> bool\<close> where
  \<open>is_EQ_c (EQ p r) = True\<close> |
  \<open>is_EQ_c _ = False\<close>

lemma is_EQ_c_EQ: \<open>is_EQ_c c \<Longrightarrow> (\<exists>p r. c = (EQ p r))\<close>
  by (cases c) auto

fun is_EQ_mf :: \<open>'b mia_formula \<Rightarrow> bool\<close> where
  \<open>is_EQ_mf (Lit b c) = is_EQ_c c\<close> |
  \<open>is_EQ_mf _ = False\<close>

lemma is_EQ_is_arith_atom_EQ: \<open>is_EQ_mf F \<Longrightarrow> \<exists>b p r. F = (Lit b (EQ p r))\<close>
  by (cases F; auto simp: is_EQ_c_EQ)

definition is_EQ_atom :: \<open>'b mia_atom \<Rightarrow> bool\<close> where
  \<open>is_EQ_atom a = (\<exists>p r. a = (ArithAtom (EQ p r)))\<close>

definition is_EQ_lit :: \<open>'b mia_atom literal \<Rightarrow> bool\<close> where
  \<open>is_EQ_lit L = is_EQ_atom (atm_of L)\<close>

lemma not_is_EQ_Lit_not_EQ_atom: \<open>\<not> (is_EQ_lit L) \<Longrightarrow> \<not> (is_EQ_atom (atm_of L))\<close>
  by (auto simp: is_EQ_lit_def is_EQ_atom_def)

definition is_Arith_atom :: \<open>'b mia_atom \<Rightarrow> bool\<close> where
  \<open>is_Arith_atom a = (\<exists>c. a = (ArithAtom c))\<close>

definition is_Arith_lit :: \<open>'b mia_atom literal \<Rightarrow> bool\<close> where
  \<open>is_Arith_lit L = (is_Arith_atom (atm_of L))\<close>

lemma is_Arith_lit_disj: \<open>is_Arith_lit L \<Longrightarrow> \<exists>c. ((L = Pos (ArithAtom c)) \<or> (L = Neg (ArithAtom c)))\<close>
  by (cases L) (auto simp: is_Arith_lit_def is_Arith_atom_def) 

fun no_EQ :: \<open>'b mia_formula \<Rightarrow> bool\<close> where
  \<open>no_EQ (Lit b c) = (\<not>(is_EQ_c c))\<close> |
  \<open>no_EQ (BVar _ _) = True\<close> |
  \<open>no_EQ (Conj FS) = (\<forall>F \<in> set FS. no_EQ F)\<close> | 
  \<open>no_EQ (Disj FS) = (\<forall>F \<in> set FS. no_EQ F)\<close>

fun remove_equalities :: \<open>'b mia_formula \<Rightarrow> 'b mia_formula\<close> where
  \<open>remove_equalities (Lit b c)  = (case c of (EQ p r) \<Rightarrow> translate_equality b p r | _ \<Rightarrow> (Lit b c))\<close>  |
  \<open>remove_equalities (BVar b x) = (BVar b x)\<close> |
  \<open>remove_equalities (Conj FS)  = Conj (map remove_equalities FS)\<close>  |
  \<open>remove_equalities (Disj FS)  = Disj (map remove_equalities FS)\<close>

lemma translate_equality_no_EQ: \<open>no_EQ (translate_equality b p r)\<close>
  by (cases b) auto

lemma remove_equalities_no_EQ: \<open>no_EQ (remove_equalities F)\<close>
proof (induction F)
  case (Conj x)
  then show ?case by auto
next
  case (Disj x)
  then show ?case by auto
next
  case (Lit x1a x2a)
  then show ?case by (cases x2a; auto simp: translate_equality_no_EQ)
next
  case (BVar x1a x2a)
  then show ?case by auto
qed

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

fun constraint_list_of :: \<open>'b mia_atom literal list \<Rightarrow> constraint list\<close> where
  \<open>constraint_list_of [] = []\<close> |
  \<open>constraint_list_of (L#Ms) = (case L of 
      Pos (BoolAtom _) \<Rightarrow> constraint_list_of Ms |
      Neg (BoolAtom _) \<Rightarrow> constraint_list_of Ms |
      Pos (ArithAtom c) \<Rightarrow> (if is_EQ_c c then constraint_list_of Ms else c # constraint_list_of Ms) |
      Neg (ArithAtom c) \<Rightarrow> (if is_EQ_c c then constraint_list_of Ms else negate_ineq c # constraint_list_of Ms))\<close>

lemma negate_ineq_no_EQ: \<open>\<not> (is_EQ_c c) \<Longrightarrow> \<not> (is_EQ_c (negate_ineq c))\<close>
  by (cases c) auto

lemma negate_ineq_correct: \<open>\<not> (is_EQ_c c) \<Longrightarrow> \<not> (v \<Turnstile>\<^sub>c c) \<longleftrightarrow> (v \<Turnstile>\<^sub>c (negate_ineq c))\<close>
  by (cases c) auto

lemma negate_ineq_idem: \<open>negate_ineq (negate_ineq c) = c\<close>
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

lemma pos_in_constraint_list: 
  assumes \<open>\<not> is_EQ_lit L\<close> and
          \<open>L = (Pos (ArithAtom c))\<close> and
          \<open>L \<in> set Ms\<close>
        shows \<open>c \<in> set (constraint_list_of Ms)\<close>
proof -
  have \<open>\<not> is_EQ_c c\<close> using assms
    by (metis is_EQ_atom_def is_EQ_c.elims(2) is_EQ_lit_def literal.sel(1))
  then show ?thesis using assms
  proof (induction Ms)
    case Nil
    then show ?case by auto
  next
    case (Cons a Ms)
    then show ?case by (auto split: literal.splits mia_atom.splits)
  qed
qed

lemma neg_in_constraint_list: 
  assumes \<open>\<not> is_EQ_lit L\<close> and
          \<open>L = (Neg (ArithAtom c))\<close> and
          \<open>L \<in> set Ms\<close>
        shows \<open>negate_ineq c \<in> set (constraint_list_of Ms)\<close>
proof -
  have \<open>\<not> is_EQ_c c\<close> using assms
    by (metis is_EQ_atom_def is_EQ_c.elims(2) is_EQ_lit_def literal.sel(2))
  then show ?thesis using assms
  proof (induction Ms)
    case Nil
    then show ?case by auto
  next
    case (Cons a Ms)
    then show ?case by (auto split: literal.splits mia_atom.splits)
  qed
qed

lemma lit_in_constraint_list_cs:
  assumes \<open>c \<in> set (constraint_list_of Ms)\<close>
        shows \<open>\<exists>L \<in> set Ms. (L = (Pos (ArithAtom c))) \<or> (L = Neg (ArithAtom (negate_ineq c)))\<close> 
  using assms proof (induction Ms)
  case Nil
  then show ?case by auto
next
  case (Cons a Ms)
  then show ?case apply simp apply (cases a)
    apply (smt (verit, ccfv_SIG) literal.case(1) mia_atom.case(1,2) mia_atom.exhaust set_ConsD)
    by (smt (verit, ccfv_SIG) literal.case(2) mia_atom.case(1,2) mia_atom.exhaust negate_ineq_idem set_ConsD) 
qed

lemma constraint_list_of_correct: 
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
      case (Pos a)
      then show ?thesis
        using A1 A2 A3 assms by (metis holds_atm.simps(1) holds_lit.simps(1) is_Arith_lit_disj literal.simps(4) pos_in_constraint_list) 
    next
      case (Neg a)
      then show ?thesis
        using A1 A2 A3 assms
        by (metis holds_atm.simps(1) holds_lit.simps(2) is_Arith_lit_disj is_EQ_atom_def is_EQ_c.elims(2) is_EQ_lit_def literal.sel(2) literal.simps(4) neg_in_constraint_list
            negate_ineq_correct) 
    qed
  qed
next
  assume B1: \<open>\<forall>L\<in>set Ms. is_Arith_lit L \<longrightarrow> holds_lit v \<beta> L\<close>
  then show \<open>v \<Turnstile>\<^sub>r\<^sub>c\<^sub>s set (constraint_list_of Ms)\<close>
  proof (intro ballI)
    fix c
    assume B2: \<open>c \<in> set (constraint_list_of Ms)\<close>
    then show \<open>v \<Turnstile>\<^sub>c c\<close> using B1
      by (metis constraint_list_of_no_EQ holds_atm.simps(1) holds_lit.simps(1,2) is_Arith_atom_def is_Arith_lit_def lit_in_constraint_list_cs literal.sel(1,2) negate_ineq_correct) 
  qed
qed

lemma is_EQ_c_not_is_no_EQ_lit: \<open>\<not>is_EQ_c c \<Longrightarrow> no_EQ (Lit b c)\<close>
  by (cases c) auto

lemma round_ineq_no_EQ: \<open>\<not>is_EQ_c c \<Longrightarrow> \<not>is_EQ_c (round_ineq c)\<close>
  by (cases c) auto

lemma false_no_EQ: \<open>no_EQ mf_false\<close>
  by (auto simp: mf_false_def)

lemma true_no_EQ: \<open>no_EQ mf_true\<close>
  by (auto simp: mf_true_def)

lemma tighten_lit_no_EQ: \<open>no_EQ (Lit b c) \<Longrightarrow> no_EQ (tighten_mf I (Lit b c))\<close>
  by (cases c) (auto simp: Let_def tighten_lit_def split: if_splits)

lemma no_EQ_disj_arg:
  assumes \<open>no_EQ F\<close>
  shows \<open>\<forall>G \<in> set (disj_arg F). no_EQ G\<close>
  using assms by (cases F) auto

lemma no_EQ_conj_arg:
  assumes \<open>no_EQ F\<close>
  shows \<open>\<forall>G \<in> set (conj_arg F). no_EQ G\<close>
  using assms by (cases F) auto

lemma no_EQ_concat_disj:
  assumes \<open>\<forall>F\<in>set FS. no_EQ F\<close>
  shows \<open>\<forall>G \<in> set (concat (map disj_arg FS)). no_EQ G\<close>
  using assms no_EQ_disj_arg by auto

lemma no_EQ_concat_conj:
  assumes \<open>\<forall>F\<in>set FS. no_EQ F\<close>
  shows \<open>\<forall>G \<in> set (concat (map conj_arg FS)). no_EQ G\<close>
  using assms no_EQ_conj_arg by auto

lemma no_EQ_mk_disj:
  assumes \<open>\<forall>F\<in>set FS. no_EQ F\<close>
  shows \<open>no_EQ (mk_disj FS)\<close>
  using assms
  by (metis mk_disj_cases no_EQ.simps(4) no_EQ_concat_disj true_no_EQ) 

lemma no_EQ_mk_conj:
  assumes \<open>\<forall>F\<in>set FS. no_EQ F\<close>
  shows \<open>no_EQ (mk_conj FS)\<close>
  using assms
  by (metis false_no_EQ mk_conj_cases no_EQ.simps(3) no_EQ_concat_conj)

lemma tighten_mf_no_EQ: \<open>no_EQ F \<Longrightarrow> no_EQ (tighten_mf I F)\<close>
proof (induction F)
  case (Conj x)
  then show ?case
    by (simp add: no_EQ_mk_conj) 
next
  case (Disj x)
  then show ?case 
    by (simp add: no_EQ_mk_disj) 
next
  case (Lit x1a x2a)
  then show ?case
    using tighten_lit_no_EQ by auto 
next
  case (BVar x1a x2a)
  then show ?case by auto
qed

definition clauses_no_EQ :: \<open>'b mia_atom literal list list \<Rightarrow> bool\<close> where
  \<open>clauses_no_EQ CS \<longleftrightarrow> (\<forall>C \<in> set CS. \<forall>L \<in> set C. \<not> is_EQ_lit L)\<close>

lemma cnf_disj_no_EQ:
  \<open>clauses_no_EQ A \<Longrightarrow> clauses_no_EQ B \<Longrightarrow> clauses_no_EQ (cnf_disj A B)\<close>
  by (auto simp: clauses_no_EQ_def cnf_disj_def)

lemma foldr_no_EQ_disj:
  \<open>\<forall>CS \<in> set CSS. clauses_no_EQ CS \<Longrightarrow> clauses_no_EQ (foldr cnf_disj CSS [[]])\<close>
  by (induction CSS) (auto simp: cnf_disj_no_EQ, simp add: clauses_no_EQ_def)

lemma to_cnf_no_EQ: \<open>no_EQ F \<Longrightarrow> clauses_no_EQ (to_cnf F)\<close>
proof (induction F)
  case (Conj x)
  then show ?case by (auto simp: clauses_no_EQ_def cnf_disj_no_EQ)
next
  case (Disj x)
  then show ?case by (auto simp: foldr_no_EQ_disj)
next
  case (Lit x1a x2a)
  then show ?case by (auto simp: clauses_no_EQ_def is_EQ_lit_def is_EQ_atom_def)
next
  case (BVar x1a x2a)
  then show ?case by (auto simp: clauses_no_EQ_def is_EQ_lit_def is_EQ_atom_def)
qed 

definition preprocess_formula :: \<open>var set \<Rightarrow> 'b mia_formula \<Rightarrow> 'b mia_atom literal list list\<close> where
  \<open>preprocess_formula I F = to_cnf (tighten_mf I (remove_equalities F))\<close>

lemma preprocess_formula_no_EQ: 
  assumes \<open>C \<in> set (preprocess_formula I F)\<close> and
          \<open>L \<in> set C\<close>
    shows \<open>\<not> (is_EQ_lit L)\<close>
   using assms to_cnf_no_EQ[OF tighten_mf_no_EQ[OF remove_equalities_no_EQ]]
   by (metis clauses_no_EQ_def preprocess_formula_def) 

lemma preprocess_formula_no_EQ_atom: 
  assumes \<open>a \<in> atms_of_mm (mset (map mset (preprocess_formula (int_vars_set Is) F)))\<close> 
  shows \<open>\<not>(is_EQ_atom a)\<close>
  using assms preprocess_formula_no_EQ
  by (fastforce simp: atms_of_ms_def atms_of_def is_EQ_lit_def)

(*MIA_Formula.sat_tighten_mf: \<forall>x\<in>?I. ?v x \<in> \<int> \<Longrightarrow> sat_mf_struct ?v ?\<beta> (tighten_mf ?I ?f) = sat_mf_struct ?v ?\<beta> ?f*)
lemma preprocess_formula_correct: \<open>(\<forall>x \<in> I. v x \<in> \<int>) \<Longrightarrow> sat_mf_struct v \<beta> F \<longleftrightarrow> holds_cnf v \<beta> (preprocess_formula I F)\<close>
  by (metis preprocess_formula_def remove_equalities_correct sat_tighten_mf to_cnf_correct)

definition mia_\<T>_solver :: \<open>'c :: lira_solver_config \<Rightarrow> int_vars \<Rightarrow> var mia_atom literal list \<Rightarrow> bool\<close> where
  \<open>mia_\<T>_solver c Is = (\<lambda>Ms. \<not> Option.is_none (mixed_cs_solver c (constraint_list_of Ms) Is))\<close>

(*AI Refactor of common proof parts*)
lemma holds_bool_lit_from_list:
  assumes \<open>consistent_interp (set Ms)\<close> and \<open>L \<in> set Ms\<close> and \<open>\<not> is_Arith_lit L\<close>
  shows \<open>holds_lit v (\<lambda>b. Pos (BoolAtom b) \<in> set Ms) L\<close>
  using assms
  by (cases L; rename_tac a; case_tac a) (*I have no idea what rename_tac is*)
     (auto simp: consistent_interp_def is_Arith_lit_def is_Arith_atom_def)

lemma mia_solver_model:
  assumes sol: \<open>mixed_cs_solver c (constraint_list_of Ms) Is = Some v\<close>
    and cons: \<open>consistent_interp (set Ms)\<close>
    and no_EQ: \<open>\<forall>L \<in> set Ms. \<not> is_EQ_lit L\<close>
  shows \<open>\<forall>L \<in> set Ms. holds_lit (of_rat_val v) (\<lambda>b. Pos (BoolAtom b) \<in> set Ms) L\<close>
    and \<open>wf_integral (of_rat_val v) (int_vars_set Is)\<close>
proof -
  have rmcs: \<open>of_rat_val v \<Turnstile>\<^sub>r\<^sub>m\<^sub>c\<^sub>s (set (constraint_list_of Ms), int_vars_set Is)\<close>
    using mixed_cs_solver_sat(2) sol by blast
  then show \<open>wf_integral (of_rat_val v) (int_vars_set Is)\<close>
    by auto
  have arith: \<open>\<forall>L \<in> set Ms. is_Arith_lit L \<longrightarrow> holds_lit (of_rat_val v) \<beta> L\<close> for \<beta>
    using constraint_list_of_correct[OF no_EQ] rmcs by auto
  show \<open>\<forall>L \<in> set Ms. holds_lit (of_rat_val v) (\<lambda>b. Pos (BoolAtom b) \<in> set Ms) L\<close>
    using arith holds_bool_lit_from_list[OF cons] by blast
qed
(* -------------------------------------------------------------------------------- *)

lemma mia_solver_correct: \<open>theory_problem.\<T>_solver_correct theory_check_mia (mia_\<T>_solver c Is) (int_vars_set Is) (preprocess_formula (int_vars_set Is) F)\<close>
proof (intro theory_problem.\<T>_solver_correctI[OF theory_mia.theory_problem_axioms])
  fix Ms
  assume cons:  \<open>consistent_interp (set Ms)\<close> 
      and atms: \<open>atm_of ` set Ms \<subseteq> atms_of_mm (mset (map mset (preprocess_formula (int_vars_set Is) F)))\<close>
  show \<open>mia_\<T>_solver c Is Ms \<longleftrightarrow> theory_check_mia (set Ms) (int_vars_set Is)\<close>
  proof
    define \<beta> where \<open>\<beta> = (\<lambda> b. Pos (BoolAtom b) \<in> set Ms)\<close>
    assume \<open>mia_\<T>_solver c Is Ms\<close>
    then obtain v where mcs:  \<open>v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set (constraint_list_of Ms), int_vars_set Is)\<close> 
                    and rmcs: \<open>of_rat_val v \<Turnstile>\<^sub>r\<^sub>m\<^sub>c\<^sub>s (set (constraint_list_of Ms), int_vars_set Is)\<close>
      using mixed_cs_solver_sat
      by (metis is_none_simps(1) mia_\<T>_solver_def option.exhaust) 
    then have integral: \<open>wf_integral (of_rat_val v) (int_vars_set Is)\<close>
      by auto 
    have \<open>\<forall>L\<in>set Ms. \<not> is_EQ_lit L\<close> using atms preprocess_formula_no_EQ_atom
        by (metis imageI is_EQ_lit_def subset_iff) 
    then have H: \<open>\<And>\<beta>. (\<forall>L \<in> set Ms. is_Arith_lit L \<longrightarrow> holds_lit (of_rat_val v) \<beta> L)\<close>
      using constraint_list_of_correct
      using rmcs satisfies_real_mixed_constraints.simps by blast 
    have \<open>\<forall>L \<in> set Ms. holds_lit (of_rat_val v) \<beta> L\<close>
      using H \<beta>_def cons holds_bool_lit_from_list by blast 
    then show \<open>theory_check_mia (set Ms) (int_vars_set Is)\<close>
      unfolding theory_check_mia_def using integral by auto 
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
      have \<open>\<forall>L\<in>set Ms. \<not> is_EQ_lit L\<close> using atms preprocess_formula_no_EQ_atom
        by (metis imageI is_EQ_lit_def subset_iff) 
      then show \<open>False\<close>
        using constraint_list_of_correct noV noW
        using holds integral by fastforce 
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
lemma final_trail:
  assumes N: \<open>N = preprocess_formula (int_vars_set II) F\<close>
    and run: \<open>DPLL_T_partial (mia_\<T>_solver c II) ([], N) = (M, N')\<close>
  shows \<open>consistent_interp (set (map lit_of M))\<close>
    and \<open>atm_of ` set (map lit_of M) \<subseteq> atms_of_mm (mset (map mset N))\<close>
    and \<open>N' = N\<close>
proof -
  have init: \<open>dpll\<^sub>W_all_inv (theory_mia.state\<^sub>\<T> (int_vars_set II) (toS [] N))\<close> and
       init': \<open>dpll\<^sub>W_all_inv (theory_mia.state\<^sub>\<T> (int_vars_set II) (toS' ([], N)))\<close>
    by (auto simp: dpll\<^sub>W_all_inv_def)
  have H1: \<open>N = N'\<close> and H2: \<open>(theory_mia.dpll\<^sub>\<T> (int_vars_set II))\<^sup>*\<^sup>* (toS' ([], N)) (toS' (M, N'))\<close> 
    using theory_problem.DPLL_T_partial_inv_fix[OF theory_mia.theory_problem_axioms init run]
      N mia_solver_correct by blast+
  then have final_inv: \<open>dpll\<^sub>W_all_inv (theory_mia.state\<^sub>\<T> (int_vars_set II) (toS' (M, N')))\<close>
    using theory_mia.dpll\<^sub>\<T>_inv_rtranclp[OF H2 init'] by auto
  show \<open>consistent_interp (set (map lit_of M))\<close>
    using final_inv set_lit_of_is_lits_of_l[of M] unfolding dpll\<^sub>W_all_inv_def by auto
  show \<open>atm_of ` set (map lit_of M) \<subseteq> atms_of_mm (mset (map mset N))\<close>
    using final_inv set_lit_of_is_lits_of_l[of M] unfolding dpll\<^sub>W_all_inv_def
    using H1 by (metis fst_eqD snd_eqD split_conv theory_mia.atms_of_mm_state\<^sub>\<T>_clauses_equals theory_mia.state\<^sub>\<T>_trail_equals_state)  
  show \<open>N' = N\<close>
    by (rule H1[symmetric])
qed

theorem dpll_mia_formula_sat: 
  assumes "dpll_mia c Is F = Some (v, \<beta>)"
  shows "sat_mf (of_rat_val v) Is \<beta> F"
proof -
  define II where \<open>II = int_vars_of_list Is\<close>
  define I where \<open>I = int_vars_set II\<close>
  define N where \<open>N = (preprocess_formula I F)\<close>
  obtain M N' where run: \<open>DPLL_T_partial (mia_\<T>_solver c II) ([], N) = (M, N')\<close>
    using assms using prod.exhaust by blast 
  define Ms where \<open>Ms = map lit_of M\<close>
  have sat: \<open>\<forall>C \<in> set N. \<exists>L \<in> set C. L \<in> set Ms\<close>
    using assms run unfolding dpll_mia_def N_def II_def I_def Ms_def
    by (auto simp: Let_def split: if_splits prod.splits)
  have vals: \<open>Some (v, \<beta>) = map_option (\<lambda>w. (w, \<lambda>b. Pos (BoolAtom b) \<in> set Ms)) (mixed_cs_solver c (constraint_list_of Ms) II)\<close>
    using assms run unfolding dpll_mia_def N_def II_def I_def Ms_def
    by (auto simp: Let_def split: if_splits prod.splits)
  then have someV: \<open>Some v = (mixed_cs_solver c (constraint_list_of Ms) II)\<close>
    by (smt (cvc5, dec_internal_enum_inst_sum) Pair_inject map_option_eq_Some) 
  then have mcs: \<open>v \<Turnstile>\<^sub>m\<^sub>c\<^sub>s (set (constraint_list_of Ms), I)\<close> 
       and rmcs: \<open>of_rat_val v \<Turnstile>\<^sub>r\<^sub>m\<^sub>c\<^sub>s (set (constraint_list_of Ms), I)\<close>
    using mixed_cs_solver_sat(1) using I_def apply metis using mixed_cs_solver_sat(2) someV
    using I_def by metis
  then have 1: \<open>of_rat_val v \<Turnstile>\<^sub>r\<^sub>m\<^sub>c\<^sub>s ({}, set Is)\<close> 
    using I_def II_def by auto
  have atms: \<open>atm_of ` set Ms \<subseteq> atms_of_mm (mset (map mset N))\<close> and 
       cons: \<open>consistent_interp (set Ms)\<close>
    using final_trail[of N II F c M N'] I_def Ms_def N_def run by blast+
  then have \<open>\<forall>L\<in>set Ms. \<not> is_EQ_lit L\<close> 
    using preprocess_formula_no_EQ_atom
    using I_def N_def by (metis in_set_image_subsetD is_EQ_lit_def)
  then have H: \<open>(\<forall>L \<in> set Ms. is_Arith_lit L \<longrightarrow> holds_lit (of_rat_val v) \<beta> L)\<close>
    using constraint_list_of_correct rmcs satisfies_real_mixed_constraints.simps by blast 
  then have \<open>\<forall>L \<in> set Ms. holds_lit (of_rat_val v) \<beta> L\<close> using cons vals someV
    by (metis Pair_inject holds_bool_lit_from_list option.inject option.map(2)) 
  then have \<open>holds_cnf (of_rat_val v) \<beta> N\<close> 
    using sat unfolding holds_cnf_def by blast 
  then have 2: \<open>sat_mf_struct (of_rat_val v) \<beta> F\<close>
    using N_def preprocess_formula_correct rmcs by auto 
  show ?thesis
    using 1 2 by (auto simp: sat_mf_def)
qed

theorem decide_mia_formula_unsat: 
  assumes "dpll_mia c Is F = None"
  shows "\<nexists> v \<beta>. sat_mf v Is \<beta> F"
proof -
  define II where \<open>II = int_vars_of_list Is\<close>
  define I where \<open>I = int_vars_set II\<close>
  define N where \<open>N = (preprocess_formula I F)\<close>
  obtain M N' where run: \<open>DPLL_T_partial (mia_\<T>_solver c II) ([], N) = (M, N')\<close>
    using assms using prod.exhaust by blast 
  define Ms where \<open>Ms = map lit_of M\<close>
  show ?thesis
  proof
    assume \<open>\<exists>v \<beta>. sat_mf v Is \<beta> F\<close>
    then obtain v \<beta> where sat: \<open>sat_mf v Is \<beta> F\<close>
      by auto
    then have clauses: \<open>holds_cnf v \<beta> N\<close>
      unfolding sat_mf_def N_def
      using II_def I_def by (metis int_vars_set_of_list preprocess_formula_correct satisfies_real_mixed_constraints.simps) 
    have integral: \<open>wf_integral v (set Is)\<close>
      using sat by (auto simp: sat_mf_def)
    have sat_t: \<open>theory_mia.satisfiable\<^sub>\<T> (set Is) (set_mset (mset (map mset N)))\<close>
      unfolding satisfiable\<^sub>\<T>_iff_model using integral clauses 
        by (intro exI[of _ v] exI[of _ \<beta>]) (auto simp: holds_cnf_def)
    have init: \<open>dpll\<^sub>W_all_inv (theory_mia.state\<^sub>\<T> (set Is) (toS [] N))\<close>
      by (rule theory_mia.dpll\<^sub>W_all_inv_state\<^sub>\<T>_init)
    have NN: \<open>N = N'\<close>
      using I_def N_def final_trail(3) run by blast 
    have dis: \<open>\<not>(\<forall>C \<in> set N. \<exists>L \<in> set C. L \<in> set Ms) \<or> ((mixed_cs_solver c (constraint_list_of Ms) II) = None)\<close>
      using run assms II_def I_def N_def Ms_def unfolding dpll_mia_def by (auto simp: Let_def split: if_splits prod.splits)
     have cons: \<open>consistent_interp (set Ms)\<close>
      and atms: \<open>atm_of ` set Ms \<subseteq> atms_of_mm (mset (map mset N))\<close>
       using final_trail[of N II F c M N'] run I_def N_def Ms_def by blast+
    have model: \<open>(M \<Turnstile>asm mset (map mset N) \<and> theory_check_mia (lits_of_l M) (set Is))\<close>
      using theory_problem.DPLL_T_partial_correct[OF theory_mia.theory_problem_axioms run, of M \<open>((mset (map mset N)))\<close> \<open>(set Is)\<close>]
      using II_def I_def NN N_def sat_t by (metis int_vars_set_of_list mia_solver_correct) 
    then have solver: \<open>mia_\<T>_solver c II Ms\<close>
      using cons atms II_def I_def Ms_def N_def 
      by (metis int_vars_set_of_list mia_solver_correct set_lit_of_is_lits_of_l theory_mia.theory_problem_axioms theory_problem.\<T>_solver_correctD) 
    then have not_none: \<open>\<not> Option.is_none (mixed_cs_solver c (constraint_list_of Ms) II)\<close>
      by (auto simp: mia_\<T>_solver_def)
    show \<open>False\<close>
      using dis proof (elim disjE)
      assume \<open>\<not> (\<forall>C\<in>set N. \<exists>L\<in>set C. L \<in> set Ms)\<close>
      then show \<open>False\<close> using model Ms_def 
      by (simp add: true_annots_true_cls true_clss_def true_cls_def lits_of_def; blast)
    next
      assume \<open>mixed_cs_solver c (constraint_list_of Ms) II = None\<close>
      then show \<open>False\<close> using not_none by auto
    qed
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

export_code dpll_mia in Haskell


definition F1 :: \<open>var mia_formula\<close> where
  \<open>F1 = Conj [(BVar True 0), Disj [(BVar False 0), (Lit True (GT (lp_monom 1 0) 5))]]\<close>

value \<open>map_option (\<lambda>(v, \<beta>). (v 0, \<beta> 0)) (dpll_mia Preprocess_Eqs [0] F1)\<close>


end