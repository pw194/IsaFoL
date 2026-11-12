theory LocaleTest
  imports CDCL_T.DPLL_T
begin

section \<open>Toy interpretations\<close>
text 
\<open>
  Here I perform some toy interpretations of the theory_problem locale in order to get more
  intuition behind its axioms and also show some things that do not follow from it
\<close>

locale theory_problem_test =
  fixes
    theory_entails_clauses :: \<open>'p \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<^sub>s\<close> 50) and
    theory_check           :: \<open>'v literal set \<Rightarrow> 'p \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<close> 50)

assumes
    entail_add: \<open>P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s add_mset C N\<close> and
    theory_model_found_or_conflict: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> I \<Turnstile>sm N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> P \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<and> C \<in> simple_clss (atm_of ` I))\<close> and
    theory_model_model_sat: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> satisfiable (set_mset N)\<close>
begin
end

subsection \<open>Trivial interpretation\<close>
text 
\<open>
  The purpose of this section is to make sure the locale can even be interpreted to begin with
\<close>
interpretation trivial: theory_problem_test \<open>\<lambda>_ _. False\<close> \<open>\<lambda>_ _. True\<close>
  apply (unfold_locales)
  apply auto
  done

subsection \<open>Partial model ==/> Total model\<close>
text 
\<open>
  This is a counterexample I came up with to show that we can not always extend a partial model
  to a total one, given the three original locale assumptions. The counterexample was constructed
  on paper and then formalized here. I noticed this issue during my formalization of
   \<^file>\<open>../DPLL_T.thy\<close>
\<close>

definition theory_entails_clauses :: \<open>nat clauses \<Rightarrow> nat clauses \<Rightarrow> bool\<close> where
  \<open>theory_entails_clauses P N = (\<forall>C \<in># N. \<exists>D \<in># P. (set_mset D) \<subseteq> (set_mset C))\<close>

definition t_check :: \<open>nat literal set \<Rightarrow> nat clauses \<Rightarrow> bool\<close> where
  \<open>t_check I P = (consistent_interp I \<and> (\<forall>C \<in># P. atms_of C \<subseteq> atm_of ` I \<longrightarrow> I \<Turnstile> C))\<close>

lemma t_check_conflict:
  assumes cons: \<open>consistent_interp I\<close> and no_t: \<open>\<not> t_check I P\<close>
  shows \<open>\<exists>C. I \<Turnstile>s CNot C \<and> theory_entails_clauses P {#C#} \<and> C \<in> simple_clss (atm_of ` I)\<close>
proof -
  obtain C where C: \<open>C \<in># P\<close> \<open>atms_of C \<subseteq> atm_of ` I\<close> \<open>\<not> I \<Turnstile> C\<close>
    using cons no_t unfolding t_check_def by auto
  then have taut: \<open>\<not>tautology (remdups_mset C)\<close>
    by (meson subset_iff tautology_def tautology_remdups_mset total_over_set_atm_of)
  moreover have \<open> I \<Turnstile>s CNot (remdups_mset C)\<close>
    using C(2,3) by (metis CNot_remdups_mset atms_of_ms_singleton atms_of_s_def total_not_CNot total_over_m_alt_def)
  moreover have \<open>theory_entails_clauses P {# remdups_mset C#}\<close>
    using C(1) theory_entails_clauses_def by auto 
  moreover have \<open>(remdups_mset C) \<in> simple_clss (atm_of ` I)\<close> using taut
    using C(2) by (metis CNot_remdups_mset atms_of_ms_CNot_atms_of distinct_mset_not_tautology_implies_in_simple_clss distinct_mset_remdups_mset simple_clss_mono subset_iff) 
  ultimately show ?thesis
    by blast
qed
  
locale no_extension = theory_problem_test theory_entails_clauses t_check

interpretation no_extension
proof unfold_locales
  fix P N C
  assume \<open>theory_entails_clauses P N\<close> and \<open>theory_entails_clauses P {#C#}\<close>
  then show \<open>theory_entails_clauses P (add_mset C N)\<close>
    unfolding theory_entails_clauses_def
    by auto 
next
  fix I :: \<open>nat literal set\<close> 
  fix N P
  assume \<open>consistent_interp I\<close> and \<open>atm_of ` I = atms_of_mm N\<close>  \<open>I \<Turnstile>sm N\<close>
  then show \<open>t_check I P \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> theory_entails_clauses P {#C#} \<and> C \<in> simple_clss (atm_of ` I))\<close>
    using t_check_conflict by blast
next
  fix I :: \<open>nat literal set\<close> 
  fix N P
  assume \<open>consistent_interp I\<close> and \<open>atm_of ` I = atms_of_mm N\<close> and \<open>theory_entails_clauses P N\<close> and \<open>t_check I P\<close>
  then show \<open>satisfiable (set_mset N) \<close>
    by (smt (cvc5, best) atms_of_atms_of_ms_mono lits_subseteq_imp_atms_subseteq satisfiable_carac subset_trans t_check_def theory_entails_clauses_def true_cls_mono_set_mset true_clss_def)
qed

context no_extension
begin

(*
    theory_extendable: \<open>consistent_interp I \<Longrightarrow> atm_of ` I \<subseteq> atms_of_mm N \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>s N \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> P \<Longrightarrow> \<exists>J. J  \<Turnstile>\<^sub>\<T> P \<and>  I \<subseteq> J \<and> atm_of ` J = atms_of_mm N \<and> consistent_interp J\<close>
*)

definition ex_N :: \<open>nat clauses\<close> where
  \<open>ex_N = {# {# Pos 0, Pos 1 #} #}\<close>

definition ex_P :: \<open>nat clauses\<close> where
  \<open>ex_P = {# {# Pos 0, Pos 1 #}, {# Neg 0, Neg 1 #}, {# Neg 0, Pos 1 #} #}\<close>

definition ex_I :: \<open>nat literal set\<close> where
  \<open>ex_I = {Pos 0} \<close>

lemma prems: \<open>consistent_interp ex_I\<close>
             \<open>atm_of ` ex_I \<subseteq> atms_of_mm ex_N\<close>  
             \<open>theory_entails_clauses ex_P ex_N\<close> 
             \<open>t_check ex_I ex_P\<close>
             \<open>ex_I \<Turnstile>sm ex_N\<close>
             \<open>satisfiable (set_mset ex_P)\<close>
proof goal_cases
  case 1
  then show ?case
    by (simp add: ex_I_def) 
next
  case 2
  then show ?case
    by (simp add: ex_I_def ex_N_def) 
next
  case 3
  then show ?case
    by (simp add: ex_N_def ex_P_def theory_entails_clauses_def) 
next
  case 4
  then show ?case by (auto simp: t_check_def ex_I_def ex_P_def)
next
  case 5
  then show ?case by (auto simp: ex_I_def ex_N_def)
next
  case 6
  have \<open>{Neg 0, Pos 1} \<Turnstile>sm ex_P\<close> unfolding ex_P_def true_clss_def by auto 
  moreover have \<open>consistent_interp {Neg (0::nat), Pos 1}\<close> by auto 
  moreover have \<open>total_over_m {Neg 0, Pos 1} (set_mset ex_P)\<close> by (simp add: ex_P_def) 
  ultimately show ?case unfolding satisfiable_def
    by auto  
qed

lemma helper:
  assumes \<open>consistent_interp I\<close> and \<open>atm_of ` I = {(0::nat), 1}\<close>
  shows \<open>(Neg (1::nat) \<in> I \<and> (\<not> (Pos (1::nat) \<in> I))) \<or> (Pos (1::nat) \<in> I \<and> (\<not> Neg (1::nat) \<in> I))\<close>
  using assms
  by (metis atms_of_s_def consistent_interp_def total_over_set_atms_of_m total_over_set_insert uminus_Pos) 

lemma no_extension_possible: \<open>\<not>(\<exists>J. t_check J ex_P \<and> ex_I \<subseteq> J \<and> atm_of ` J = atms_of_mm ex_N \<and> consistent_interp J)\<close>
proof 
  assume \<open>\<exists>J. t_check J ex_P \<and> ex_I \<subseteq> J \<and> atm_of ` J = atms_of_mm ex_N \<and> consistent_interp J\<close>
  then obtain I where is_t: \<open>t_check I ex_P\<close> and super: \<open>ex_I \<subseteq> I\<close> and atm: \<open>atm_of ` I = atms_of_mm ex_N\<close> and cons: \<open>consistent_interp I\<close>
    by auto
  have atms: \<open>atm_of ` I = {0, 1}\<close>
    by (simp add: \<open>atm_of ` I = atms_of_mm ex_N\<close> ex_N_def) 
  then have pos_zero: \<open>Pos 0 \<in> I\<close>
    using ex_I_def super by auto
  then have \<open>\<not> (I \<Turnstile> {#Neg (0::nat), Pos 1#} \<and> I \<Turnstile> {#Neg (0::nat), Neg 1#})\<close>
    apply simp using helper[OF cons atms]
    using cons by (metis consistent_interp_def uminus_Pos) 
  then have \<open>\<not>t_check I ex_P\<close> unfolding t_check_def ex_P_def
    using atms pos_zero
    by auto 
  then show \<open>False\<close>
    using is_t by auto
qed
  
end


end