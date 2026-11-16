theory CDCL_MIA_Interp
imports CDCL_MIA_Models
begin

section \<open>MIA theory_problem interpretation\<close>

subsection \<open>Model based acceptance and entailment\<close>
text \<open>This is our \<open>I \<Turnstile>\<^sub>\<T> P\<close>\<close>
definition theory_check_mia :: \<open>'b mia_atom literal set \<Rightarrow> 'b t_problem \<Rightarrow> bool\<close> where
  \<open>theory_check_mia I P = (\<exists>(v, \<beta>) \<in> models_of I. (sat_mf v (fst P) \<beta> (snd P)))\<close>

text \<open>This is our \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N\<close>\<close>
definition theory_entails_clauses_mia :: \<open>'b t_problem \<Rightarrow> 'b mia_atom clauses \<Rightarrow> bool\<close> where
  \<open>theory_entails_clauses_mia P N = (\<forall>v \<beta>. sat_mf v (fst P) \<beta> (snd P) \<longrightarrow> (\<forall>C \<in># N. \<exists>L \<in># C. holds_lit v \<beta> L))\<close>

subsection \<open>Lemmas needed for the interpretation\<close>
lemma holds_lit_conflict:
  assumes pos: \<open>holds_lit v \<beta> L\<close> and neg: \<open>holds_lit v \<beta> (-L)\<close>
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

lemma theory_implies_prop: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> theory_entails_clauses_mia P N \<Longrightarrow> theory_check_mia I P \<Longrightarrow> I \<Turnstile>sm N\<close>
proof
  assume cons: \<open>consistent_interp I\<close> and atm: \<open>atm_of ` I = atms_of_mm N\<close> and ent: \<open>theory_entails_clauses_mia P N\<close> and in_t: \<open>theory_check_mia I P\<close>
  then obtain v \<beta> where model: \<open>(sat_mf v (fst P) \<beta> (snd P))\<close>
    by (auto simp: theory_check_mia_def)
  then have H1: \<open>(\<forall>C \<in># N. \<exists>L \<in># C. holds_lit v \<beta> L)\<close>
    using ent theory_entails_clauses_mia_def by blast
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
      then have \<open>(\<forall>L\<in>I. holds_lit v \<beta> L)\<close> using in_t unfolding theory_check_mia_def using A1 ent 
        by (metis (mono_tags, lifting) Product_Type.Collect_case_prodD holds_lit_conflict split_beta theory_entails_clauses_mia_def models_of_def) 
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

subsection \<open>The interpretation\<close>
lemma ax1: \<open>theory_entails_clauses_mia P N \<Longrightarrow> theory_entails_clauses_mia P {#C#} \<Longrightarrow> theory_entails_clauses_mia P (add_mset C N)\<close>
  unfolding theory_entails_clauses_mia_def by auto 

lemma ax2:
  assumes \<open>consistent_interp I\<close> 
          \<open>atm_of ` I = atms_of_mm N\<close>
          \<open>theory_entails_clauses_mia P N\<close>
          \<open>theory_check_mia I P\<close>
        shows \<open>satisfiable (set_mset N)\<close>
  unfolding satisfiable_def
  using assms by (meson satisfiable_carac' satisfiable_def theory_implies_prop)

lemma ax3:
  assumes cons: \<open>consistent_interp I\<close> and atm: \<open>atm_of ` I = atms_of_mm N\<close> and sat: \<open>I \<Turnstile>sm N\<close>
  shows \<open>theory_check_mia I P \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> theory_entails_clauses_mia P {#C#} \<and> C \<in> simple_clss (atm_of ` I))\<close>
proof (cases \<open>theory_check_mia I P\<close>)
  case True
  then show ?thesis by auto
next
  case False
  then show ?thesis 
    unfolding theory_check_mia_def
  proof(intro disjI2)
    let ?C = \<open>{#- L. L \<in># mset_set I#}\<close>
    assume A1: \<open>\<not> (\<exists>(v, \<beta>)\<in>models_of I. sat_mf v (fst P) \<beta> (snd P))\<close>
    have \<open>finite (atm_of ` I)\<close> by (simp add: assms(2)) 
    moreover have \<open>I \<subseteq> Pos ` (atm_of ` I) \<union> Neg ` (atm_of ` I)\<close> by (smt (cvc5, interleave) Set.basic_monos(7) Un_subset_iff imageI imageI literal.exhaust_sel subsetI) 
    ultimately have fin: \<open>finite I\<close> using atm
      by (metis finite_imageI infinite_Un rev_finite_subset)
    have cnot: \<open>I \<Turnstile>s CNot ?C\<close> using cons by (simp add: fin true_clss_def_iff_negation_in_model) 
    have atmsub: \<open>atms_of ?C \<subseteq> atm_of ` I\<close> using fin by (metis atms_of_def atms_of_pNeg finite_set_mset_mset_set pNeg_def set_eq_subset)
    have dis: \<open>distinct_mset ?C\<close> by (metis distinct_mset_pNeg_iff is_mset_set pNeg_def)
    have taut: \<open>\<not>tautology ?C\<close> using assms(1) cnot consistent_CNot_not_tautology by blast 
    have tent: \<open>theory_entails_clauses_mia P {#?C#}\<close>
      unfolding theory_entails_clauses_mia_def
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
          then have \<open>(v, \<beta>) \<in> models_of I\<close>
            using fin by (auto simp: models_of_def)
          then show \<open>False\<close>
            using A1 A2 by blast
        qed
        then show \<open>\<forall>C\<in>#{#uminus `# mset_set I#}. Multiset.Bex C (holds_lit v \<beta>)\<close>
          by (metis in_multiset_nempty member_add_mset)
      qed
    qed
    then show \<open>\<exists>C. I \<Turnstile>s CNot C \<and> theory_entails_clauses_mia P {#C#} \<and> C \<in> simple_clss (atm_of ` I)\<close>
      using atmsub cnot dis taut by (meson distinct_mset_not_tautology_implies_in_simple_clss in_mono simple_clss_mono)
  qed
qed

lemma ax4:
  assumes cons: \<open>consistent_interp I\<close> and atm: \<open>atm_of ` I \<subseteq> atms_of_mm N\<close> and tent: \<open>theory_entails_clauses_mia P N\<close> and is_t: \<open>theory_check_mia I P\<close> 
  shows \<open>\<exists>J. (theory_check_mia J P) \<and> I \<subseteq> J \<and> (atm_of ` J = atms_of_mm N) \<and> consistent_interp J\<close>
proof -
  obtain v \<beta> where in_I: \<open>(v, \<beta>) \<in> models_of I\<close> and sat: \<open>(sat_mf v (fst P) \<beta> (snd P))\<close> using is_t
    using theory_check_mia_def by force
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
    using is_t using in_I models_of_in by auto 
  then have H3: \<open>consistent_interp ?J\<close>
    unfolding consistent_interp_def using holds_lit_conflict by blast 
  have \<open>(v, \<beta>) \<in> models_of ?J\<close>
    unfolding models_of_def using all by blast 
  then have H4: \<open>theory_check_mia ?J P\<close>
    unfolding theory_check_mia_def using sat
    by auto 
  show \<open>\<exists>J. theory_check_mia J P \<and> I \<subseteq> J \<and> atm_of ` J = atms_of_mm N \<and> consistent_interp J\<close>
    using H2 H3 H4 by blast 
qed


interpretation dpll_mia: theory_problem theory_entails_clauses_mia theory_check_mia
  apply (unfold_locales)
  subgoal for P N C using ax1 by blast
  subgoal for I N P using ax3 by blast 
  subgoal for I N P using ax2 by blast
  subgoal for I N P using ax4 by simp 
  done

subsection \<open>Soundness\<close>
lemma satisfiable\<^sub>\<T>_iff_sat_mf:
  assumes tent: \<open>theory_entails_clauses_mia (Is, F) N\<close>
  shows \<open>dpll_mia.satisfiable\<^sub>\<T> (Is, F) (set_mset N) \<longleftrightarrow> (\<exists>v \<beta>. sat_mf v Is \<beta> F)\<close>
proof
  assume \<open>dpll_mia.satisfiable\<^sub>\<T> (Is, F) (set_mset N)\<close>
  then show \<open>\<exists>v \<beta>. sat_mf v Is \<beta> F\<close>
    unfolding dpll_mia.satisfiable\<^sub>\<T>_def theory_check_mia_def models_of_def by auto 
next
  assume A1: \<open>\<exists>v \<beta>. sat_mf v Is \<beta> F\<close>
  let ?I = \<open>{}\<close>
  have H1: \<open>consistent_interp ?I\<close> by auto 
  have H2: \<open>atm_of ` ?I \<subseteq> atms_of_mm N\<close> by auto
  have H3: \<open>theory_check_mia ?I (Is, F)\<close> unfolding theory_check_mia_def using A1
    by (simp add: models_of_def) 
  then show \<open>dpll_mia.satisfiable\<^sub>\<T> (Is, F) (set_mset N)\<close>
    using dpll_mia.theory_extendable[OF H1 H2 tent H3]
    using assms by (metis dpll_mia.satisfiable\<^sub>\<T>_def theory_implies_prop)
qed

theorem dpll_mia_sound:
  assumes \<open>(dpll_mia.dpll\<^sub>\<T> (Is, F))\<^sup>*\<^sup>* ([], N) (M, N)\<close>
    and \<open>theory_entails_clauses_mia (Is, F) N\<close>
    and \<open>\<forall>S. \<not> dpll_mia.dpll\<^sub>\<T> (Is, F) (M, N) S\<close>
  shows \<open>(M \<Turnstile>asm N \<and> theory_check_mia (lits_of_l M) (Is, F)) \<longleftrightarrow> (\<exists>v \<beta>. sat_mf v Is \<beta> F)\<close>
  by (simp add: assms(1,2,3) dpll_mia.dpll\<^sub>\<T>_sound satisfiable\<^sub>\<T>_iff_sat_mf)

end