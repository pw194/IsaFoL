theory CDCL_MIA_Models             
  imports CDCL_T.DPLL_T MIA_Tactic.MIA_Formula_Solver
begin

text 
\<open>
  I use my own atm type. Later on we would like to have a mapping from nat/int => 'b mia_atom,
  simply because my intuition tells me it is more efficient and more compatible with IsaSAT.
  The mapping would then later on just contain an array that we index with the respective number,
  to obtain the atom
\<close>
datatype 'b mia_atom = ArithAtom \<open>constraint\<close> | BoolAtom 'b

text 
\<open>
  P = (Is, F) where Is is the list of integer variables and F a mia formula
\<close>
type_synonym 'b t_problem = \<open>(nat list) \<times> 'b mia_formula\<close>

fun arith_atom :: \<open>bool \<Rightarrow> constraint \<Rightarrow> 'b mia_atom literal\<close> where
  \<open>arith_atom False c = Neg (ArithAtom c)\<close> |
  \<open>arith_atom True c = Pos (ArithAtom c)\<close>

value \<open>arith_atom True (GT (lp_monom 2 0) 10) :: nat mia_atom literal\<close>

fun bool_atom :: \<open>bool \<Rightarrow> 'b \<Rightarrow> 'b mia_atom literal\<close> where
  \<open>bool_atom False x = Neg (BoolAtom x)\<close> |
  \<open>bool_atom True x = Pos (BoolAtom x)\<close>

value \<open>bool_atom True (0::nat)\<close>

fun holds_atm :: \<open>real valuation \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b mia_atom \<Rightarrow> bool\<close> where
  \<open>holds_atm v \<beta> (ArithAtom c) = (v \<Turnstile>\<^sub>c c)\<close> |
  \<open>holds_atm v \<beta> (BoolAtom x)  = \<beta> x\<close>

fun holds_lit :: \<open>real valuation \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b mia_atom literal \<Rightarrow> bool\<close> where
  \<open>holds_lit v \<beta> (Pos a) = (holds_atm v \<beta> a)\<close> |
  \<open>holds_lit v \<beta> (Neg a) = (\<not> (holds_atm v \<beta> a))\<close>

text \<open>A mia model consists of a real valuation paired with a boolean assignment\<close>
definition models_of :: \<open>'b mia_atom literal set \<Rightarrow> ((nat \<Rightarrow> real) \<times> ('b \<Rightarrow> bool)) set\<close> where
  \<open>models_of I = {(v, \<beta>). (\<forall>L \<in> I. holds_lit v \<beta> L)}\<close>

lemma models_of_in: \<open>(v, \<beta>) \<in> models_of I \<Longrightarrow> (\<forall>L\<in>I. holds_lit v \<beta> L)\<close> by (auto simp: models_of_def)


end