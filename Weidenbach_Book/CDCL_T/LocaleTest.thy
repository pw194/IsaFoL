theory LocaleTest
  imports "DPLL_T"
begin

section \<open>Toy interpretations\<close>
text \<open>
  Here I perform some toy interpretations of the theory_problem locale in order to get more
  intuition behind its axioms and also show some things that do not follow from it
\<close>


subsection \<open>Trivial interpretation\<close>
interpretation trivial: theory_problem \<open>\<lambda>_ _. False\<close> \<open>\<lambda>_ _. True\<close>
  apply (unfold_locales)
  apply auto
  done

subsection \<open>Partial model ==/> Total model\<close>
(*
  fixes
    theory_entails_clauses :: \<open>'p \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<^sub>s\<close> 50) and
    theory_check           :: \<open>'v literal set \<Rightarrow> 'p \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<close> 50)
*)

definition theory_entails_clauses_nat :: \<open>'p \<Rightarrow> nat clauses \<Rightarrow> bool\<close> where
  \<open>theory_entails_clauses_nat _ N = (\<forall>C \<in># N. (C = {# Pos 0 #}) \<or> (C = {# Neg 0 #}) \<or> (C = {#Pos 0, Pos 1#}))\<close>

definition theory_check_nat :: \<open>nat literal set \<Rightarrow> 'p \<Rightarrow> bool\<close> where
  \<open>theory_check_nat I _ = ((1::nat) \<notin> atm_of ` I)\<close>

lemma confl: \<open>consistent_interp I \<Longrightarrow> \<close>

interpretation no_extension: theory_problem theory_entails_clauses_nat theory_check_nat
  apply (unfold_locales)
  subgoal by (simp add: theory_entails_clauses_nat_def) 
proof -
  fix I :: \<open>nat literal set\<close> 
  fix N 
  fix P :: \<open>'p\<close>
  assume A1: \<open>consistent_interp I\<close> and A2: \<open>atm_of ` I = atms_of_mm N\<close> and A3: \<open>I \<Turnstile>sm N\<close>
  then show \<open>theory_check_nat I P \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> theory_entails_clauses_nat P {#C#} \<and> C \<in> simple_clss (atm_of ` I))\<close>
  proof (cases \<open>(1::nat) \<in> (atm_of ` I)\<close>)
    case True
    then have \<open>\<not> theory_check_nat I P\<close> by (auto simp: theory_check_nat_def)
    then show ?thesis 
      sorry
  next
    case False
    then have \<open>theory_check_nat I P\<close> by (auto simp: theory_check_nat_def)
    then show ?thesis by auto
  qed



end