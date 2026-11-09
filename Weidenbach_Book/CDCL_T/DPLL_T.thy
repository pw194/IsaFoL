theory DPLL_T
imports CDCL.DPLL_W
begin

(*
locale theory_problem =
  fixes
    theory_entails_set :: \<open>'a \<Rightarrow> 'v clauses \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<^sub>s\<close> 90) and
    theory_entails :: \<open>'v literal set \<Rightarrow> 'a \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<close> 90)
  assumes
    entail_mono: \<open>N \<Turnstile>\<^sub>\<T>\<^sub>s N' \<Longrightarrow> N \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<Longrightarrow> N \<Turnstile>\<^sub>\<T>\<^sub>s add_mset C N'\<close> and
    theory_model_found_or_conflict: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N' \<Longrightarrow> I \<Turnstile>sm N' \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> N \<or> (\<exists>C. I \<Turnstile>s CNot C \<and> N \<Turnstile>\<^sub>\<T>\<^sub>s {#C#} \<and> atms_of C \<subseteq> atm_of ` I \<and> C \<in> simple_clss (atm_of ` I))\<close>and
    theory_model_model_sat: \<open>consistent_interp I \<Longrightarrow> atm_of ` I = atms_of_mm N' \<Longrightarrow> N \<Turnstile>\<^sub>\<T>\<^sub>s N' \<Longrightarrow>
      I \<Turnstile>\<^sub>\<T> N \<Longrightarrow> satisfiable (set_mset N')\<close>
*)
text \<open>
For the locale I am trying out single clause entailment for now, as everything else can be
easily derived by it anyways. The type 'p stands for the theory problem in question, which I
assume to be the formula prior to its propositional abstraction. The entailment operators
include the translation between the theory and the propositional side, while respecting the
induced valuation.
\<close>
locale theory_problem =
  fixes
    theory_entails_clause :: \<open>'p \<Rightarrow> 'v clause \<Rightarrow> bool\<close> (infix \<open>\<Turnstile>\<^sub>\<T>\<^sub>C\<close> 50) and
    theory_check :: \<open>'v literal set \<Rightarrow> 'p \<Rightarrow> bool\<close>   (infix \<open>\<Turnstile>\<^sub>\<T>\<close> 90)

  assumes prop_entail_is_theory_entail: \<open>(\<forall>C \<in># N. P \<Turnstile>\<^sub>\<T>\<^sub>C C) \<Longrightarrow> N \<Turnstile>pm C \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>C C\<close>
begin

text \<open>I try to simulate the behavior of a stupid implementation of plain DPLL with a theory
      consistency check on the already existing calculus to reuse proofs. Effectively, we
      build the set of all theory lemmas and consider them to be already part of the original
      clause set\<close>
inductive dpll\<^sub>\<T> :: \<open>'p \<Rightarrow> 'v dpll\<^sub>W_state \<Rightarrow> 'v dpll\<^sub>W_state \<Rightarrow> bool\<close> for P where
  dpll\<^sub>W_step: \<open>dpll\<^sub>W S S' \<Longrightarrow>  dpll\<^sub>\<T> P S S'\<close> |
  backtrack\<^sub>\<T>: \<open>backtrack_split (trail S) = (M', L # M) 
                \<Longrightarrow> is_decided L 
                \<Longrightarrow> P \<Turnstile>\<^sub>\<T>\<^sub>C D 
                \<Longrightarrow> trail S \<Turnstile>as CNot D 
                \<Longrightarrow> dpll\<^sub>\<T> P S (Propagated (- (lit_of L)) () # M, clauses S)\<close>

text \<open>This is the finite set of all theory lemmas\<close>
definition simple_clss_theory :: \<open>'p \<Rightarrow> 'v clauses \<Rightarrow> 'v clauses\<close> where
  \<open>simple_clss_theory P N = mset_set {C \<in> simple_clss (atms_of_mm N). P \<Turnstile>\<^sub>\<T>\<^sub>C C}\<close>

lemma simple_clss_theory_distinct: \<open>distinct_mset (simple_clss_theory P N)\<close>
  by (simp add: simple_clss_theory_def)

lemma set_mset_simple_clss_theory:
  \<open>set_mset (simple_clss_theory P N) = {C \<in> simple_clss (atms_of_mm N). P \<Turnstile>\<^sub>\<T>\<^sub>C C}\<close>
  unfolding simple_clss_theory_def using simple_clss_theory_distinct
  by (auto simp: simple_clss_finite)

text \<open>The normal dpll state gets extended by adding the theory lemmas to the clauses\<close>
definition state\<^sub>\<T> :: \<open>'p \<Rightarrow> 'v dpll\<^sub>W_state \<Rightarrow> 'v dpll\<^sub>W_state\<close> where
  \<open>state\<^sub>\<T> P S = (trail S, (clauses S) + (simple_clss_theory P (clauses S)))\<close>

lemma state\<^sub>\<T>_trail_equals_state[simp]: \<open>trail (state\<^sub>\<T> P S) = trail S\<close>
  by (auto simp: state\<^sub>\<T>_def)

lemma state\<^sub>\<T>_clauses_equals: \<open>clauses (state\<^sub>\<T> P S) = (clauses S + (simple_clss_theory P (clauses S)))\<close>
  by (auto simp: state\<^sub>\<T>_def)

lemma state_clauses_state\<^sub>\<T>_subset: \<open>clauses S \<subseteq># clauses (state\<^sub>\<T> P S)\<close>
  by (auto simp: state\<^sub>\<T>_def)

lemma dpll\<^sub>W_step_is_state\<^sub>\<T>_step: \<open>dpll\<^sub>W S S' \<Longrightarrow> dpll\<^sub>W (state\<^sub>\<T> P S) (state\<^sub>\<T> P S')\<close>
proof (induction rule: dpll\<^sub>W.induct)
  case (propagate L C S)
  have member: \<open>add_mset L C \<in># clauses (state\<^sub>\<T> P S)\<close> 
    using state_clauses_state\<^sub>\<T>_subset[of S P] propagate by auto
  have conf: \<open>trail (state\<^sub>\<T> P S) \<Turnstile>as CNot C\<close> 
    using propagate by auto
  have undef: \<open>undefined_lit (trail (state\<^sub>\<T> P S)) L\<close>
    using propagate by auto
  then show ?case using propagate member conf undef dpll\<^sub>W.propagate
    using state\<^sub>\<T>_def by (metis fst_eqD snd_eqD) 
next
  case (decided S L)
  then show ?case
    using state_clauses_state\<^sub>\<T>_subset theory_problem_axioms
    by (metis (no_types, lifting) atms_of_ms_mono basic_trans_rules(31) dpll\<^sub>W.decided fst_eqD set_mset_mono sndI theory_problem.state\<^sub>\<T>_def)
next
  case (backtrack S M' L M D)
  then show ?case
    using state\<^sub>\<T>_def
    using theory_problem_axioms by (metis (no_types, lifting) dpll\<^sub>W.backtrack mset_subset_eqD split_pairs2 theory_problem.state_clauses_state\<^sub>\<T>_subset)
qed

lemma dpll\<^sub>\<T>_step_is_dpll\<^sub>W_step: \<open>dpll\<^sub>\<T> P S S' \<Longrightarrow> dpll\<^sub>W_all_inv S \<Longrightarrow> dpll\<^sub>W (state\<^sub>\<T> P S) (state\<^sub>\<T> P S')\<close>
  proof(induction rule: dpll\<^sub>\<T>.induct)
    case (dpll\<^sub>W_step S S')
    then show ?case using dpll\<^sub>W_step_is_state\<^sub>\<T>_step by auto
  next
    case (backtrack\<^sub>\<T> S M' L M D)
    have atms: \<open>atms_of (remdups_mset D) \<subseteq> atms_of_mm(clauses S)\<close>
      using backtrack\<^sub>\<T>.hyps(4) backtrack\<^sub>\<T>.prems
      by (metis (no_types, opaque_lifting) CNot_remdups_mset atms_of_negate_ann_lits dpll\<^sub>W_all_inv_dest(2)
          entails_CNot_negate_ann_lits lits_subseteq_imp_atms_subseteq order.trans) 
    have taut: \<open>\<not>tautology (remdups_mset D)\<close>
      using backtrack\<^sub>\<T>.hyps(4) backtrack\<^sub>\<T>.prems
      by (meson consistent_CNot_not_tautology dpll\<^sub>W_all_inv_dest(3) tautology_remdups_mset
          true_annots_true_cls) 
    have remdups_entail: \<open>set_mset {#D#} \<Turnstile>p remdups_mset D\<close>
      by simp 
    have ent': \<open>P \<Turnstile>\<^sub>\<T>\<^sub>C remdups_mset D\<close>
      using backtrack\<^sub>\<T>.hyps(3) prop_entail_is_theory_entail remdups_entail
      by (metis set_mset_add_mset_insert set_mset_empty singletonD) 
    have tlemma: \<open>remdups_mset D \<in># simple_clss_theory P (clauses S)\<close>
      using ent' atms taut by (simp add: set_mset_simple_clss_theory simple_clss_def)
    then show ?case
      using backtrack\<^sub>\<T>.hyps(1,2,4) state\<^sub>\<T>_def by (metis CNot_remdups_mset backtrack fst_eqD snd_eqD union_iff)
  qed

end


end