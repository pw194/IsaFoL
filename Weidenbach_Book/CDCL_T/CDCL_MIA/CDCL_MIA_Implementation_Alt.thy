theory CDCL_MIA_Implementation_Alt
  imports CDCL_MIA_Interp CDCL_T.DPLL_T_Implementation
begin

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

lemma lit_to_mf_correct: \<open>holds_lit v \<beta> L \<longleftrightarrow> sat_mf_struct v \<beta> (lit_to_mf L)\<close>
proof (cases L)
  case (Pos x1)
  then show ?thesis proof (cases x1)
    case (ArithAtom x1)
    then show ?thesis
      by (simp add: Pos) 
  next
    case (BoolAtom x2)
    then show ?thesis
      by (simp add: Pos)
  qed
next
  case (Neg x2)
  then show ?thesis proof (cases x2)
    case (ArithAtom x1)
    then show ?thesis 
      by (simp add: Neg)
  next
    case (BoolAtom x2)
    then show ?thesis 
      by (simp add: Neg)
  qed
qed

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

definition dpll_mia :: \<open>'c :: lira_solver_config \<Rightarrow> var list \<Rightarrow> var mia_formula \<Rightarrow> ((nat \<Rightarrow> rat) \<times> (nat \<Rightarrow> bool)) option\<close> where
  \<open>dpll_mia c Is F = (let N = to_cnf F;
      (M, _) = DPLL_T_partial (\<lambda>Ms. \<not> Option.is_none (mia_\<T>_solver c Is Ms)) ([], N);
      Ms = map lit_of M
    in if \<forall>C \<in> set N. \<exists>L \<in> set C. L \<in> set Ms then mia_\<T>_solver c Is Ms else None)\<close>

thm decide_mia_formula_sat decide_mia_formula_unsat
theorem dpll_mia_formula_sat: 
  assumes "dpll_mia c Is F = Some (v, \<beta>)"
  shows "sat_mf (of_rat_val v) Is \<beta> F"
proof -
  define N where \<open>N = to_cnf F\<close>
  obtain M N' where run: \<open>(M, N') = DPLL_T_partial (\<lambda>Ms. \<not> Option.is_none (mia_\<T>_solver c Is Ms)) ([], N)\<close>
    using assms N_def[symmetric] unfolding dpll_mia_def by (metis (lifting) prod.exhaust)
  define Ms where \<open>Ms = map lit_of M\<close>
  have sat: \<open>\<forall>C \<in> set N. \<exists>L \<in> set C. L \<in> set Ms\<close> 
  and vals: \<open>Some (v, \<beta>) = mia_\<T>_solver c Is Ms\<close>
    using assms run[symmetric]
    unfolding dpll_mia_def N_def[symmetric] Ms_def
    by (auto simp: Let_def split: if_splits prod.splits)
  then have some_vals: \<open>decide_mia_formula c Is (Conj (map lit_to_mf Ms)) = Some (v, \<beta>)\<close>
    by (simp add: mia_\<T>_solver_def) 
  then have satconjmf: \<open>sat_mf (of_rat_val v) Is \<beta> (Conj (map lit_to_mf Ms))\<close>
    by (rule decide_mia_formula_sat)
  then have satconj: \<open>sat_mf_struct (of_rat_val v) \<beta> (Conj (map lit_to_mf Ms))\<close>
    by (auto simp: sat_mf_def)
  then have all: \<open>(\<forall>L \<in> set Ms. holds_lit (of_rat_val v) \<beta> L)\<close>
    using sat_conj by blast
  show \<open>sat_mf (of_rat_val v) Is \<beta> F\<close>
    unfolding sat_mf_def
    using N_def all sat satconjmf by (metis holds_cnf_def sat_mf_def to_cnf_correct) 
qed
thm disjE
theorem decide_mia_formula_unsat: 
  assumes "dpll_mia c Is F = None"
  shows "\<nexists> v \<beta>. sat_mf v Is \<beta> F"
proof 
  define N where \<open>N = to_cnf F\<close>
  obtain M N' where run: \<open>(M, N') = DPLL_T_partial (\<lambda>Ms. \<not> Option.is_none (mia_\<T>_solver c Is Ms)) ([], N)\<close>
    using assms N_def[symmetric] unfolding dpll_mia_def by (metis (lifting) prod.exhaust)
  define Ms where \<open>Ms = map lit_of M\<close>
  have dis: \<open>\<not>(\<forall>C \<in> set N. \<exists>L \<in> set C. L \<in> set Ms) \<or> (mia_\<T>_solver c Is Ms = None)\<close>
    using run assms N_def[symmetric] Ms_def unfolding dpll_mia_def 
    by (auto simp: Let_def split: if_splits prod.splits)
  assume \<open>\<exists>v \<beta>. sat_mf v Is \<beta> F\<close>
  then obtain v \<beta> where sat: \<open>sat_mf v Is \<beta> F\<close> by auto
  from dis show \<open>False\<close>
  proof (elim disjE)
    assume \<open>\<not> (\<forall>C\<in>set N. \<exists>L\<in>set C. L \<in> set Ms)\<close>
    then show \<open>False\<close>
      sorry
  next
    assume \<open>mia_\<T>_solver c Is Ms = None\<close>
    then show \<open>False\<close>
      sorry
  qed
qed

end