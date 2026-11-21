theory CDCL_MIA_Models             
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

fun arith_atom :: \<open>bool \<Rightarrow> constraint \<Rightarrow> 'b mia_atom literal\<close> where
  \<open>arith_atom False c = Neg (ArithAtom c)\<close> |
  \<open>arith_atom True c = Pos (ArithAtom c)\<close>

fun bool_atom :: \<open>bool \<Rightarrow> 'b \<Rightarrow> 'b mia_atom literal\<close> where
  \<open>bool_atom False x = Neg (BoolAtom x)\<close> |
  \<open>bool_atom True x = Pos (BoolAtom x)\<close>

fun holds_atm :: \<open>real valuation \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b mia_atom \<Rightarrow> bool\<close> where
  \<open>holds_atm v \<beta> (ArithAtom c) = (v \<Turnstile>\<^sub>c c)\<close> |
  \<open>holds_atm v \<beta> (BoolAtom x)  = \<beta> x\<close>

fun holds_lit :: \<open>real valuation \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b mia_atom literal \<Rightarrow> bool\<close> where
  \<open>holds_lit v \<beta> (Pos a) = (holds_atm v \<beta> a)\<close> |
  \<open>holds_lit v \<beta> (Neg a) = (\<not> (holds_atm v \<beta> a))\<close>

fun lit_to_mf :: \<open>'b mia_atom literal \<Rightarrow> 'b mia_formula\<close> where
  \<open>lit_to_mf (Pos (ArithAtom c)) = Lit True c\<close>
| \<open>lit_to_mf (Neg (ArithAtom c)) = Lit False c\<close>
| \<open>lit_to_mf (Pos (BoolAtom b)) = BVar True b\<close>
| \<open>lit_to_mf (Neg (BoolAtom b)) = BVar False b\<close>

end