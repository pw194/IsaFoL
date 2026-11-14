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

value \<open>arith_atom True (GT (lp_monom 2 0) 10) :: nat mia_atom literal\<close>

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

definition testset :: \<open>'b mia_atom literal set \<Rightarrow> ((nat \<Rightarrow> real) \<times> ('b \<Rightarrow> bool)) set\<close> where
  \<open>testset I = {(v, \<beta>). (\<forall>L \<in> I. holds_lit v \<beta> L)}\<close>

lemma testsetlemma: \<open>(v, \<beta>) \<in> testset I \<Longrightarrow> (\<forall>L\<in>I. holds_lit v \<beta> L)\<close> by (auto simp: testset_def)

definition tcheck :: \<open>'b mia_atom literal set \<Rightarrow> 'b t_problem \<Rightarrow> bool\<close> where
  \<open>tcheck I P = (\<exists>(v, \<beta>) \<in> testset I. (sat_mf v (fst P) \<beta> (snd P)))\<close>

definition tentails :: \<open>'b t_problem \<Rightarrow> 'b mia_atom clauses \<Rightarrow> bool\<close> where
  \<open>tentails P N = (\<forall>v \<beta>. sat_mf v (fst P) \<beta> (snd P) \<longrightarrow> (\<forall>C \<in># N. \<exists>L \<in># C. holds_lit v \<beta> L))\<close>

lemma holds_lit_conflict:
  assumes p: \<open>holds_lit v \<beta> L\<close> and n: \<open>holds_lit v \<beta> (-L)\<close>
  shows \<open>False\<close>
  using assms
proof (induction L)
  case (Pos x)
  then show ?case 
  proof (cases x)
    case (ArithAtom x1)
    then show ?thesis using Pos by auto
  next
    case (BoolAtom x2)
    then show ?thesis using Pos by auto
  qed
next
  case (Neg x)
  then show ?case proof (cases x)
    case (ArithAtom x1)
    then show ?thesis using Neg by auto
  next
    case (BoolAtom x2)
    then show ?thesis using Neg by auto
  qed
qed

lemma theory_implies_prop: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> tentails P N \<Longrightarrow> tcheck I P \<Longrightarrow> I \<Turnstile>sm N\<close>
proof
  assume cons: \<open>consistent_interp I\<close> and atm: \<open>atm_of ` I = atms_of_mm N\<close> and ent: \<open>tentails P N\<close> and in_t: \<open>tcheck I P\<close>
  then obtain v \<beta> where model: \<open>(sat_mf v (fst P) \<beta> (snd P))\<close>
    by (auto simp: tcheck_def)
  then have H1: \<open>(\<forall>C \<in># N. \<exists>L \<in># C. holds_lit v \<beta> L)\<close>
    using ent tentails_def by blast
  then have mutual: \<open>(\<forall>C \<in># N. \<exists>L \<in># C. (L \<in> I \<and> -L \<notin> I) \<or> (-L \<in> I \<and> L \<notin> I))\<close>
    using atm cons
    by (metis atms_of_s_def consistent_interp_def mset_add total_over_set_atms_of_m total_over_set_literal_defined)
  have \<open>\<forall>C \<in># N. \<exists>L \<in># C. L \<in> I\<close>
  proof
    fix C
    assume A1: \<open>C \<in># N\<close>
    show \<open>\<exists>L\<in>#C. L \<in> I\<close>
    proof (rule ccontr)
      assume \<open>\<not> (\<exists>L\<in>#C. L \<in> I)\<close>
      then have \<open>(\<forall>L\<in>#C. L \<notin> I)\<close> by auto
      then have H2: \<open>(\<forall>L\<in>#C. -L \<in> I)\<close> using mutual A1 using atm by (metis atm_of_in_atm_of_set_in_uminus in_implies_atm_of_on_atms_of_ms) 
      then have \<open>(\<forall>L\<in>I. holds_lit v \<beta> L)\<close> using in_t unfolding tcheck_def using A1 ent by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD holds_lit_conflict split_beta tentails_def testset_def) 
      then show \<open>False\<close>
        using A1 H1 H2 holds_lit_conflict by blast 
    qed
  qed
  then show \<open>I \<Turnstile>m N\<close>
    by (simp add: true_cls_def true_cls_mset_def)
qed

lemma holds_lit_neg: \<open>\<not> holds_lit v \<beta> L \<Longrightarrow> holds_lit v \<beta> (-L)\<close>
proof (induction L)
  case (Pos x)
  then show ?case
    proof (cases x)
      case (ArithAtom x1)
      then show ?thesis using Pos by auto
    next
      case (BoolAtom x2)
      then show ?thesis using Pos by auto
    qed
next
  case (Neg x)
  then show ?case
    proof (cases x)
      case (ArithAtom x1)
      then show ?thesis using Neg by auto
    next
      case (BoolAtom x2)
      then show ?thesis using Neg by auto
    qed
qed

lemma ax1: \<open>tentails P N \<Longrightarrow> tentails P {#C#} \<Longrightarrow> tentails P (add_mset C N)\<close>
  unfolding tentails_def by auto 

lemma ax2:
  assumes \<open>consistent_interp I\<close> 
          \<open>atm_of ` I = atms_of_mm N\<close>
          \<open>tentails P N\<close>
          \<open>tcheck I P\<close>
        shows \<open>satisfiable (set_mset N)\<close>
  unfolding satisfiable_def
  using assms by (meson satisfiable_carac' satisfiable_def theory_implies_prop)

(*
    entail_add: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s add_mset C N\<close> and
    theory_model_found_or_conflict: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> I \<Turnstile>sm N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<and> C \<in> simple_clss (atm_of ` I))\<close> and
    theory_model_model_sat: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> satisfiable (set_mset N)\<close>
    theory_extendable: \<open>consistent_interp I \<Longrightarrow> atm_of ` I \<subseteq> atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> \<exists>J. J  \<Turnstile>\<^sub>\<T> P \<and>  I \<subseteq> J \<and> atm_of ` J = atms_of_mm N \<and> consistent_interp J\<close>
*)

lemma ax3:
  assumes cons: \<open>consistent_interp I\<close> and atm: \<open>atm_of ` I = atms_of_mm N\<close> and sat: \<open>I \<Turnstile>sm N\<close>
  shows \<open>tcheck I P \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> tentails P {#C#} \<and> C \<in> simple_clss (atm_of ` I))\<close>
proof (cases \<open>tcheck I P\<close>)
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis 
    unfolding tcheck_def
  proof(intro disjI2)
    let ?C = \<open>{#- L. L \<in># mset_set I#}\<close>
    assume A1: \<open>\<not> (\<exists>(v, \<beta>)\<in>testset I. sat_mf v (fst P) \<beta> (snd P))\<close>
    have \<open>finite (atm_of ` I)\<close> by (simp add: assms(2)) 
    moreover have \<open>I \<subseteq> Pos ` (atm_of ` I) \<union> Neg ` (atm_of ` I)\<close> by (smt (cvc5, interleave) Set.basic_monos(7) Un_subset_iff imageI imageI literal.exhaust_sel subsetI) 
    ultimately have fin: \<open>finite I\<close> using atm
      by (metis finite_imageI infinite_Un rev_finite_subset)
    have cnot: \<open>I \<Turnstile>s CNot ?C\<close> using cons by (simp add: fin true_clss_def_iff_negation_in_model) 
    have atmsub: \<open>atms_of ?C \<subseteq> atm_of ` I\<close> using fin by (metis atms_of_def atms_of_pNeg finite_set_mset_mset_set pNeg_def set_eq_subset)
    have dis: \<open>distinct_mset ?C\<close> by (metis distinct_mset_pNeg_iff is_mset_set pNeg_def)
    have taut: \<open>\<not>tautology ?C\<close> using assms(1) cnot consistent_CNot_not_tautology by blast 
    have tent: \<open>tentails P {#?C#}\<close>
      unfolding tentails_def
    proof(intro allI)
      fix v \<beta>
      show \<open>sat_mf v (fst P) \<beta> (snd P) \<longrightarrow> (\<forall>C\<in>#{#uminus `# mset_set I#}. Multiset.Bex C (holds_lit v \<beta>))\<close>
      proof (intro impI)
        assume A2: \<open>sat_mf v (fst P) \<beta> (snd P)\<close>
        have \<open>\<exists>L \<in># ?C. holds_lit v \<beta> L\<close>
        proof (rule ccontr)
          assume \<open>\<not> (\<exists>L\<in>#uminus `# mset_set I. holds_lit v \<beta> L)\<close>
          then have \<open>(\<forall>L\<in>#?C. \<not> holds_lit v \<beta> L)\<close> by auto
          then have \<open>(\<forall>L\<in>#?C. holds_lit v \<beta> (-L))\<close>
            using holds_lit_neg by blast
          then have \<open>(v, \<beta>) \<in> testset I\<close>
            using fin by (auto simp: testset_def)
          then show \<open>False\<close>
            using A1 A2 by blast
        qed
        then show \<open>\<forall>C\<in>#{#uminus `# mset_set I#}. Multiset.Bex C (holds_lit v \<beta>)\<close>
          by (metis in_multiset_nempty member_add_mset)
      qed
    qed
    then show \<open>\<exists>C. I \<Turnstile>s CNot C \<and> tentails P {#C#} \<and> C \<in> simple_clss (atm_of ` I)\<close>
      using atmsub cnot dis taut by (meson distinct_mset_not_tautology_implies_in_simple_clss in_mono simple_clss_mono)
  qed
qed

lemma ax4:
  assumes cons: \<open>consistent_interp I\<close> and atm: \<open>atm_of ` I \<subseteq> atms_of_mm N\<close> and tent: \<open>tentails P N\<close> and is_t: \<open>tcheck I P\<close> 
  shows \<open>\<exists>J. (tcheck J P) \<and> I \<subseteq> J \<and> (atm_of ` J = atms_of_mm N) \<and> consistent_interp J\<close>
proof -
  obtain v \<beta> where in_I: \<open>(v, \<beta>) \<in> testset I\<close> and sat: \<open>(sat_mf v (fst P) \<beta> (snd P))\<close> using is_t
    using tcheck_def by force
  let ?J = \<open>I \<union> {L. atm_of L \<in> atms_of_mm N \<and> atm_of L \<notin> (atm_of ` I) \<and> holds_lit v \<beta> L}\<close>
  have H1: \<open>I \<subseteq> ?J\<close> by auto
  have H2: \<open>(atm_of ` ?J = atms_of_mm N)\<close>
  proof
    show \<open>atm_of ` (I \<union> {L. atm_of L \<in> atms_of_mm N \<and> atm_of L \<notin> atm_of ` I \<and> holds_lit v \<beta> L}) \<subseteq> atms_of_mm N\<close>
    proof
      fix x
      assume \<open>x \<in> atm_of ` (I \<union> {L. atm_of L \<in> atms_of_mm N \<and> atm_of L \<notin> atm_of ` I \<and> holds_lit v \<beta> L})\<close>
      then show \<open>x \<in> atms_of_mm N\<close>
        using assms(2) by fastforce
    qed
    show \<open>atms_of_mm N \<subseteq> atm_of ` (I \<union> {L. atm_of L \<in> atms_of_mm N \<and> atm_of L \<notin> atm_of ` I \<and> holds_lit v \<beta> L})\<close>
    proof 
      fix x
      assume A: \<open>x \<in> atms_of_mm N\<close>
      then show \<open>x \<in> atm_of ` (I \<union> {L. atm_of L \<in> atms_of_mm N \<and> atm_of L \<notin> atm_of ` I \<and> holds_lit v \<beta> L})\<close>
        proof (cases \<open>x \<in> atm_of ` I\<close>)
          case True
          then show ?thesis
            by blast 
        next
          case False
          have \<open>holds_lit v \<beta> (Pos x) \<or> holds_lit v \<beta> (Neg x)\<close>
            by auto
          then show ?thesis
            using False A by (metis (lifting) Un_iff imageI literal.sel(1,2) mem_Collect_eq) 
        qed
      qed
    qed
  have all: \<open>\<forall>L \<in> ?J. holds_lit v \<beta> L\<close>
    using is_t using in_I testsetlemma by auto 
  then have H3: \<open>consistent_interp ?J\<close>
    unfolding consistent_interp_def using holds_lit_conflict by blast 
  have \<open>(v, \<beta>) \<in> testset ?J\<close>
    unfolding testset_def using all by blast 
  then have H4: \<open>tcheck ?J P\<close>
    unfolding tcheck_def using sat
    by auto 
  show \<open>\<exists>J. tcheck J P \<and> I \<subseteq> J \<and> atm_of ` J = atms_of_mm N \<and> consistent_interp J\<close>
    using H2 H3 H4 by blast 
qed


interpretation dpll_mia: theory_problem tentails tcheck
  apply (unfold_locales)
  subgoal for P N C using ax1 by blast
  subgoal for I N P using ax3 by blast 
  subgoal for I N P using ax2 by blast
  subgoal for I N P using ax4 by simp 
  done

thm dpll_mia.dpll\<^sub>\<T>_sound

end