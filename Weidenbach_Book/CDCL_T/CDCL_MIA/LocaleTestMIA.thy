theory LocaleTestMIA
imports CDCL_T.DPLL_T MIA_Tactic.MIA_Formula_Solver
begin

term \<open>(Pos (0::nat))\<close>
term \<open>lp_monom\<close>
term \<open>Lit True (GT (lp_monom 2 0) 10)\<close>


(*
datatype constraint = LT linear_poly rat
  | GT linear_poly rat
  | LEQ linear_poly rat
  | GEQ linear_poly rat
  | EQ linear_poly rat
*)

(*
fun to_cnf :: \<open>'v flat_formula \<Rightarrow> 'v cnf\<close> where
  \<open>to_cnf (Flat_Atom x) = [[x]]\<close> |
  \<open>to_cnf (Flat_Conj FS) = concat (map to_cnf FS)\<close> |
  \<open>to_cnf (Flat_Disj FS) = foldr cnf_or (map to_cnf FS) [[]]\<close>
*)

(*
datatype 'b mia_formula =
    Conj "'b mia_formula list"
  | Disj "'b mia_formula list"
  | Lit bool constraint
  | BVar bool 'b
*)

datatype 'b mia_atom = ArithAtom \<open>constraint\<close> | BoolAtom 'b

type_synonym 'b t_problem = \<open>(nat list) \<times> 'b mia_formula\<close>

fun arith_atom :: \<open>bool \<Rightarrow> constraint \<Rightarrow> 'b mia_atom literal\<close> where
  \<open>arith_atom False c = Neg (ArithAtom c)\<close> |
  \<open>arith_atom True c = Pos (ArithAtom c)\<close>

fun bool_atom :: \<open>bool \<Rightarrow> 'b \<Rightarrow> 'b mia_atom literal\<close> where
  \<open>bool_atom False x = Neg (BoolAtom x)\<close> |
  \<open>bool_atom True x = Pos (BoolAtom x)\<close>

definition cnf_or :: \<open>_\<close> where
  \<open>cnf_or A B = [C1 @ C2. C1 \<leftarrow> A, C2 \<leftarrow> B]\<close>

fun to_cnf :: \<open>'b mia_formula \<Rightarrow> 'b mia_atom literal list list\<close> where
  \<open>to_cnf (Lit b c) = [[arith_atom b c]]\<close> |
  \<open>to_cnf (BVar b x) = [[bool_atom b x]]\<close> |
  \<open>to_cnf (Conj FS) = concat (map to_cnf FS)\<close> |
  \<open>to_cnf (Disj FS) = foldr cnf_or (map to_cnf FS) [[]]\<close>

fun holds_atm :: \<open>real valuation \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b mia_atom \<Rightarrow> bool\<close> where
  \<open>holds_atm v \<beta> (ArithAtom c) = (v \<Turnstile>\<^sub>c c)\<close> |
  \<open>holds_atm v \<beta> (BoolAtom x)  = \<beta> x\<close>

fun holds_lit :: \<open>real valuation \<Rightarrow> ('b \<Rightarrow> bool) \<Rightarrow> 'b mia_atom literal \<Rightarrow> bool\<close> where
  \<open>holds_lit v \<beta> (Pos a) = (holds_atm v \<beta> a)\<close> |
  \<open>holds_lit v \<beta> (Neg a) = (\<not> (holds_atm v \<beta> a))\<close>

fun testset :: \<open>'b mia_atom literal set \<Rightarrow> ((nat \<Rightarrow> real) \<times> ('b \<Rightarrow> bool)) set\<close> where
  \<open>testset I = {(v, \<beta>). (\<forall>L \<in> I. holds_lit v \<beta> L)}\<close>

definition tcheck :: \<open>'b mia_atom literal set \<Rightarrow> 'b t_problem \<Rightarrow> bool\<close> where
  \<open>tcheck I P = (\<exists>(v, \<beta>) \<in> testset I. (sat_mf v (fst P) \<beta> (snd P)))\<close>

definition tentails :: \<open>'b t_problem \<Rightarrow> 'b mia_atom clauses \<Rightarrow> bool\<close> where
  \<open>tentails P N = (\<forall>v \<beta>. sat_mf v (fst P) \<beta> (snd P) \<longrightarrow> (\<forall>C \<in># N. \<exists>L \<in># C. holds_lit v \<beta> L))\<close>

(*
    entail_add: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s add_mset C N\<close> and
    theory_model_found_or_conflict: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> I \<Turnstile>sm N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<and> C \<in> simple_clss (atm_of ` I))\<close> and
    theory_model_model_sat: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> satisfiable (set_mset N)\<close>
    theory_extendable: \<open>consistent_interp I \<Longrightarrow> atm_of ` I \<subseteq> atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> \<exists>J. J  \<Turnstile>\<^sub>\<T> P \<and>  I \<subseteq> J \<and> atm_of ` J = atms_of_mm N \<and> consistent_interp J\<close>
*)

lemma test: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> tentails P N \<Longrightarrow> tcheck I P \<Longrightarrow> I \<Turnstile>sm N\<close>
  sorry

lemma ax1: \<open>tentails P N \<Longrightarrow> tentails P {#C#} \<Longrightarrow> tentails P (add_mset C N)\<close>
  unfolding tentails_def by auto 

lemma ax2:
  assumes \<open>consistent_interp I\<close> 
          \<open>atm_of ` I = atms_of_mm N\<close>
          \<open>tentails P N\<close>
          \<open>tcheck I P\<close>
        shows \<open>satisfiable (set_mset N)\<close>
  unfolding satisfiable_def
  using assms by (meson satisfiable_carac' satisfiable_def test)


(*lemma ax3:
  assumes \<open>consistent_interp I\<close> \<open>atm_of ` I = atms_of_mm N\<close>*)

value \<open>arith_atom True (GT (lp_monom 2 0) 10) :: nat mia_atom literal\<close>

end