theory CDCL_MIA_Atoms
  imports CDCL_T.DPLL_T MIA_Tactic.MIA_Formula_Solver
begin

section \<open>MIA Atoms\<close>
text 
\<open>
  I use my own atom type. Later on we would like to have a mapping from nat/int <=> 'b mia_atom,
  simply because my intuition tells me it is more efficient and more compatible with IsaSAT.
  A MIA atom is either a propositional variable or a mixed arithmetic constraint.
\<close>
datatype 'b mia_atom = ArithAtom \<open>constraint\<close> | BoolAtom 'b

text \<open>P = Is, where Is is the set of variables that are constrained to \<int>\<close>
type_synonym mia_problem = \<open>(var set)\<close>

fun lit_of_arith_atom :: \<open>bool \<Rightarrow> constraint \<Rightarrow> 'b mia_atom literal\<close> where
  \<open>lit_of_arith_atom False c = Neg (ArithAtom c)\<close> |
  \<open>lit_of_arith_atom True c = Pos (ArithAtom c)\<close>

lemma atm_of_arith_atom[simp]: \<open>atm_of (lit_of_arith_atom b c) = (ArithAtom c)\<close>
  by (cases b; auto)

fun lit_of_bool_atom :: \<open>bool \<Rightarrow> 'b \<Rightarrow> 'b mia_atom literal\<close> where
  \<open>lit_of_bool_atom False x = Neg (BoolAtom x)\<close> |
  \<open>lit_of_bool_atom True x = Pos (BoolAtom x)\<close>

lemma atm_of_bool_atom[simp]: \<open>atm_of (lit_of_bool_atom b x) = (BoolAtom x)\<close>
  by (cases b; auto)

fun holds_atm :: \<open>real valuation \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b mia_atom \<Rightarrow> bool\<close> where
  \<open>holds_atm v \<beta> (ArithAtom c) = (v \<Turnstile>\<^sub>c c)\<close> |
  \<open>holds_atm v \<beta> (BoolAtom x)  = \<beta> x\<close>

fun holds_lit :: \<open>real valuation \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b mia_atom literal \<Rightarrow> bool\<close> where
  \<open>holds_lit v \<beta> (Pos a) = (holds_atm v \<beta> a)\<close> |
  \<open>holds_lit v \<beta> (Neg a) = (\<not> (holds_atm v \<beta> a))\<close>

lemma holds_lit_conflict:
  assumes \<open>holds_lit v \<beta> L\<close> and \<open>holds_lit v \<beta> (-L)\<close>
  shows \<open>False\<close>
  using assms
proof (cases L)
  case (Pos x1)
  then show ?thesis
  proof (cases x1)
    case (ArithAtom x1)
    then show ?thesis
      using Pos assms by auto 
  next
    case (BoolAtom x2)
    then show ?thesis 
      using Pos assms by auto 
  qed
next
  case (Neg x2)
  then show ?thesis
  proof (cases x2)
    case (ArithAtom x1)
    then show ?thesis 
      using Neg assms by auto 
  next
    case (BoolAtom x2)
    then show ?thesis
       using Neg assms by auto 
  qed
qed

lemma holds_lit_neg: 
  assumes \<open>\<not> holds_lit v \<beta> L\<close>
  shows \<open>holds_lit v \<beta> (-L)\<close>
proof (cases L)
  case (Pos x1)
  then show ?thesis
  proof (cases x1)
    case (ArithAtom x1)
    then show ?thesis
      using Pos assms by auto 
  next
    case (BoolAtom x2)
    then show ?thesis 
      using Pos assms by auto 
  qed
next
  case (Neg x2)
  then show ?thesis
  proof (cases x2)
    case (ArithAtom x1)
    then show ?thesis 
      using Neg assms by auto 
  next
    case (BoolAtom x2)
    then show ?thesis
       using Neg assms by auto 
  qed
qed

lemma holds_lit_valid: \<open>holds_lit v \<beta> L \<or> holds_lit v \<beta> (- L)\<close>
  using holds_lit_neg by blast

fun lit_to_mf :: \<open>'b mia_atom literal \<Rightarrow> 'b mia_formula\<close> where
  \<open>lit_to_mf (Pos (ArithAtom c)) = Lit True c\<close>
| \<open>lit_to_mf (Neg (ArithAtom c)) = Lit False c\<close>
| \<open>lit_to_mf (Pos (BoolAtom b)) = BVar True b\<close>
| \<open>lit_to_mf (Neg (BoolAtom b)) = BVar False b\<close>

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

end
