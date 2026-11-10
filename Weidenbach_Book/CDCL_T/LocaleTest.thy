theory LocaleTest
  imports "DPLL_T"
begin

definition theory_entails_clauses_nat :: \<open>nat clauses \<Rightarrow> bool\<close> where
  \<open>theory_entails_clauses_nat N = (\<forall>C \<in># N. set_mset C = {Pos 0})\<close>

lemma
  assumes H: "theory_entails_clauses_nat N"
  shows "atms_of_mm N = {0} \<or> atms_of_mm N = {}"
proof -
  have "atms_of_mm N \<subseteq> {0}"
  proof
    fix x
    assume "x \<in> atms_of_mm N"
    then obtain C L where C: "C \<in># N" and L: "L \<in># C" and x: "x = atm_of L"
      by (auto simp: atms_of_ms_def atms_of_def)
    have "L = Pos 0"
      using H C L unfolding theory_entails_clauses_nat_def by blast
    then show "x \<in> {0}"
      using x by simp
  qed
  then show ?thesis
    by (auto simp: subset_singleton_iff)
qed

interpretation test1: theory_problem \<open>\<lambda>_ _. False\<close> \<open>\<lambda>_ _. True\<close>
  apply (unfold_locales)
  apply auto
  done

interpretation test2: theory_problem \<open>\<lambda> _ N. theory_entails_clauses_nat N\<close> \<open>\<lambda>_ _. True\<close>
  apply (unfold_locales)
    apply auto
proof -
  fix N C
  assume A1: \<open>theory_entails_clauses_nat N\<close>
  assume A2: \<open>theory_entails_clauses_nat {#C#}\<close>
  show \<open>theory_entails_clauses_nat (add_mset C N)\<close>
    using A1 A2 theory_entails_clauses_nat_def by auto
next
  fix I :: \<open>nat literal set\<close>
  fix N
  assume A1: \<open>consistent_interp I\<close>
  assume A2: \<open>atm_of ` I = atms_of_mm N\<close>
  assume A3: \<open>theory_entails_clauses_nat N\<close>
  show \<open>satisfiable (set_mset N)\<close>
    unfolding satisfiable_def
  proof (intro exI[of _ \<open>{Pos 0}\<close>] conjI)
    show \<open>{Pos 0} \<Turnstile>s set_mset N\<close>
      using A3 by (auto simp: theory_entails_clauses_nat_def true_clss_def
          true_cls_def)
    show \<open>consistent_interp {Pos 0}\<close>
      by (auto simp: consistent_interp_def)
    show \<open>total_over_m {Pos 0} (set_mset N)\<close>
      using A3 by (auto simp: theory_entails_clauses_nat_def total_over_m_def
          total_over_set_def atms_of_ms_def atms_of_def)
  qed
qed

thm test1.dpll\<^sub>\<T>_sound
thm test2.dpll\<^sub>\<T>_sound

end