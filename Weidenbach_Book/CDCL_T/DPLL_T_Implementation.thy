theory DPLL_T_Implementation
imports CDCL.DPLL_CDCL_W_Implementation DPLL_T "HOL-Library.Code_Target_Numeral"
begin

section \<open>Simple Implementation of DPLL_T\<close>

definition DPLL_step :: \<open>('v literal list \<Rightarrow> bool) \<Rightarrow> 'v dpll\<^sub>W_ann_lits \<times> 'v literal list list
  \<Rightarrow> 'v dpll\<^sub>W_ann_lits \<times> 'v literal list list\<close> where
\<open>DPLL_step \<T>_solver = (\<lambda>(Ms, N).
  (case find_first_unit_clause N Ms of
    Some (L, _) \<Rightarrow> (Propagated L () # Ms, N)
  | _ \<Rightarrow>
    if ((\<exists>C \<in> set N. (\<forall>c \<in> set C. -c \<in> lits_of_l Ms)) \<or> (\<not> (\<T>_solver (map lit_of Ms))))
    then
      (case backtrack_split Ms of
        (_, L # M) \<Rightarrow> (Propagated (- (lit_of L)) () # M, N)
      | (_, _) \<Rightarrow> (Ms, N)
      )
    else
    (case find_first_unused_var N (lits_of_l Ms) of
        Some a \<Rightarrow> (Decided a # Ms, N)
      | None \<Rightarrow> (Ms, N))))\<close>

abbreviation \<open>toS \<equiv> \<lambda>(Ms::('v, unit) ann_lits) (N::'v literal list list). (Ms, mset (map mset N))\<close>
abbreviation \<open>toS' \<equiv> \<lambda>((Ms::('v, unit) ann_lits), (N::'v literal list list)). (Ms, mset (map mset N))\<close>

locale theory_problem_impl = theory_problem theory_entails_clauses theory_check
  for theory_entails_clauses :: "'p \<Rightarrow> 'v clauses \<Rightarrow> bool"  (infix \<open>\<Turnstile>\<^sub>\<T>\<^sub>s\<close> 50)
  and theory_check :: "'v literal set \<Rightarrow> 'p \<Rightarrow> bool"        (infix \<open>\<Turnstile>\<^sub>\<T>\<close> 50)
  
begin
(*
lemma DPLL_step_is_a_dpll\<^sub>\<T>_step:
  assumes step: \<open>DPLL_step (Ms, N) = (Ms', N')\<close>
  and neq: \<open>(Ms, N) \<noteq> (Ms', N')\<close>
  shows "dpll\<^sub>\<T> P (toS Ms N) (toS Ms' N')"
  sorry
*)
end


(*
theory Scratch
imports CDCL.DPLL_CDCL_W_Implementation CDCL.DPLL_W "HOL-Library.Code_Target_Numeral"
begin

subsection \<open>Simple Implementation of DPLL\<close>

subsubsection \<open>Combining the propagate and decide: a DPLL step\<close>

definition DPLL_step :: "int dpll\<^sub>W_ann_lits \<times> int literal list list
  \<Rightarrow> int dpll\<^sub>W_ann_lits \<times> int literal list list" where
"DPLL_step = (\<lambda>(Ms, N).
  (case find_first_unit_clause N Ms of
    Some (L, _) \<Rightarrow> (Propagated L () # Ms, N)
  | _ \<Rightarrow>
    if \<exists>C \<in> set N. (\<forall>c \<in> set C. -c \<in> lits_of_l Ms)
    then
      (case backtrack_split Ms of
        (_, L # M) \<Rightarrow> (Propagated (- (lit_of L)) () # M, N)
      | (_, _) \<Rightarrow> (Ms, N)
      )
    else
    (case find_first_unused_var N (lits_of_l Ms) of
        Some a \<Rightarrow> (Decided a # Ms, N)
      | None \<Rightarrow> (Ms, N))))"

text \<open>Example of propagation:\<close>
value "DPLL_step ([Decided (Neg 1)], [[Pos (1::int), Neg 2]])"

text \<open>We define the conversion function between the states as defined in \<open>Prop_DPLL\<close> (with
  multisets) and here (with lists).\<close>
abbreviation "toS \<equiv> \<lambda>(Ms::(int, unit) ann_lits)
                      (N:: int literal list list). (Ms, mset (map mset N)) "
abbreviation "toS' \<equiv> \<lambda>(Ms::(int, unit) ann_lits,
                          N:: int literal list list). (Ms, mset (map mset N)) "

text \<open>Proof of correctness of @{term DPLL_step}\<close>
lemma DPLL_step_is_a_dpll\<^sub>W_step:
  assumes step: "(Ms', N') = DPLL_step (Ms, N)"
  and neq: "(Ms, N) \<noteq> (Ms', N')"
  shows "dpll\<^sub>W (toS Ms N) (toS Ms' N')"
proof -
  let ?S = "(Ms, mset (map mset N))"
  { fix L E
    assume unit: "find_first_unit_clause N Ms = Some (L, E)"
    then have Ms'N: "(Ms', N') = (Propagated L () # Ms, N)"
      using step unfolding DPLL_step_def by auto
    obtain C where
      C: "C \<in> set N" and
      Ms: "Ms \<Turnstile>as CNot (mset C - {#L#})" and
      undef: "undefined_lit Ms L" and
      "L \<in> set C" using find_first_unit_clause_some[OF unit] by metis
    have "dpll\<^sub>W (Ms, mset (map mset N))
         (Propagated L () # fst (Ms, mset (map mset N)), snd (Ms, mset (map mset N)))"
      apply (rule dpll\<^sub>W.propagate)
      using Ms undef C \<open>L \<in> set C\<close> by (auto simp add: C)
    then have ?thesis using Ms'N by auto
  }
  moreover
  { assume unit: "find_first_unit_clause N Ms = None"
    assume exC: "\<exists>C \<in> set N. Ms \<Turnstile>as CNot (mset C)"
    then obtain C where C: "C \<in> set N" and Ms: "Ms \<Turnstile>as CNot (mset C)" by auto
    then obtain L M M' where bt: "backtrack_split Ms = (M', L # M)"
      using step exC neq unfolding DPLL_step_def prod.case unit
      by (cases "backtrack_split Ms", rename_tac b, case_tac b) (auto simp: lits_of_l_unfold)
    then have "is_decided L" using backtrack_split_snd_hd_decided[of Ms] by auto
    have 1: "dpll\<^sub>W (Ms, mset (map mset N))
                  (Propagated (- lit_of L) () # M, snd (Ms, mset (map mset N)))"
      apply (rule dpll\<^sub>W.backtrack[OF _ \<open>is_decided L\<close>, of ])
      using C Ms bt by auto
    moreover have "(Ms', N') = (Propagated (- (lit_of L)) () # M, N)"
      using step exC unfolding DPLL_step_def bt prod.case unit by (auto simp: lits_of_l_unfold)
    ultimately have ?thesis by auto
  }
  moreover
  { assume unit: "find_first_unit_clause N Ms = None"
    assume exC: "\<not> (\<exists>C \<in> set N. Ms \<Turnstile>as CNot (mset C))"
    obtain L where unused: "find_first_unused_var N (lits_of_l Ms) = Some L"
      using step exC neq unfolding DPLL_step_def prod.case unit
      by (cases "find_first_unused_var N (lits_of_l Ms)") (auto simp: lits_of_l_unfold)
    have "dpll\<^sub>W (Ms, mset (map mset N))
               (Decided L # fst (Ms, mset (map mset N)), snd (Ms, mset (map mset N)))"
      apply (rule dpll\<^sub>W.decided[of ?S L])
      using find_first_unused_var_Some[OF unused]
      by (auto simp add: Decided_Propagated_in_iff_in_lits_of_l atms_of_ms_def)
    moreover have "(Ms', N') = (Decided L # Ms, N)"
      using step exC unfolding DPLL_step_def unused prod.case unit by (auto simp: lits_of_l_unfold)
    ultimately have ?thesis by auto
  }
  ultimately show ?thesis by (cases "find_first_unit_clause N Ms") auto
qed

lemma DPLL_step_stuck_final_state:
  assumes step: "(Ms, N) = DPLL_step (Ms, N)"
  shows "conclusive_dpll\<^sub>W_state (toS Ms N)"
proof -
  have unit: "find_first_unit_clause N Ms = None"
    using step unfolding DPLL_step_def by (auto split:option.splits)

  { assume n: "\<exists>C \<in> set N. Ms \<Turnstile>as CNot (mset C)"
    then have Ms: "(Ms, N) = (case backtrack_split Ms of (x, []) \<Rightarrow> (Ms, N)
                         | (x, L # M) \<Rightarrow> (Propagated (- lit_of L) () # M, N))"
      using step unfolding DPLL_step_def by (simp add: unit lits_of_l_unfold)

  have "snd (backtrack_split Ms) = []"
    proof (cases "backtrack_split Ms", cases "snd (backtrack_split Ms)")
      fix a b
      assume "backtrack_split Ms = (a, b)" and "snd (backtrack_split Ms) = []"
      then show "snd (backtrack_split Ms) = []" by blast
    next
      fix a b aa list
      assume
        bt: "backtrack_split Ms = (a, b)" and
        bt': "snd (backtrack_split Ms) = aa # list"
      then have Ms: "Ms = Propagated (- lit_of aa) () # list" using Ms by auto
      have "is_decided aa" using backtrack_split_snd_hd_decided[of Ms] bt bt' by auto
      moreover have "fst (backtrack_split Ms) @ aa # list = Ms"
        using backtrack_split_list_eq[of Ms] bt' by auto
      ultimately have False unfolding Ms by auto
      then show "snd (backtrack_split Ms) = []" by blast
    qed

    then have ?thesis
      using n backtrack_snd_empty_not_decided[of Ms] unfolding conclusive_dpll\<^sub>W_state_def
      by (cases "backtrack_split Ms") auto
  }
  moreover {
    assume n: "\<not> (\<exists>C \<in> set N. Ms \<Turnstile>as CNot (mset C))"
    then have "find_first_unused_var N (lits_of_l Ms) = None"
      using step unfolding DPLL_step_def by (simp add: unit lits_of_l_unfold split: option.splits)
    then have a: "\<forall>a \<in> set N. atm_of ` set a \<subseteq> atm_of ` (lits_of_l Ms)" by auto
    have "fst (toS Ms N) \<Turnstile>asm snd (toS Ms N)" unfolding true_annots_def CNot_def Ball_def
      proof clarify
        fix x
        assume x: "x \<in> set_mset (clauses (toS Ms N))"
        then have "\<not>Ms \<Turnstile>as CNot x" using n unfolding true_annots_def CNot_def Ball_def by auto
        moreover have "total_over_m (lits_of_l Ms) {x}"
          using a x image_iff in_mono atms_of_s_def
          unfolding total_over_m_def total_over_set_def lits_of_def by fastforce
        ultimately show "fst (toS Ms N) \<Turnstile>a x"
          using total_not_CNot[of "lits_of_l Ms" x] by (simp add: true_annot_def true_annots_true_cls)
      qed
    then have ?thesis unfolding conclusive_dpll\<^sub>W_state_def by blast
  }
  ultimately show ?thesis by blast
qed


subsubsection \<open>Adding invariants\<close>

paragraph \<open>Invariant tested in the function\<close>

lemma snd_DPLL_step[simp]:
  "snd (DPLL_step (Ms, N)) = N"
  unfolding DPLL_step_def by (auto split: if_split option.splits prod.splits list.splits)

lemma dpll\<^sub>W_all_inv_dpll\<^sub>W_tranclp_irrefl:
  assumes "dpll\<^sub>W_all_inv (Ms, N)"
  and "dpll\<^sub>W\<^sup>+\<^sup>+ (Ms, N) (Ms, N)"
  shows "False"
proof -
  have 1: "wf {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W\<^sup>+\<^sup>+ S S'}" using wf_dpll\<^sub>W_tranclp by auto
  have "((Ms, N), (Ms, N)) \<in> {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W\<^sup>+\<^sup>+ S S'}" using assms by auto
  then show False using wf_not_refl[OF 1] by blast
qed

lemma DPLL_step_obtains:
  obtains Ms' where "(Ms', N) = DPLL_step (Ms, N)"
  unfolding DPLL_step_def by (metis (no_types, lifting) DPLL_step_def prod.collapse snd_DPLL_step)

paragraph \<open>Embedding the invariant into the type\<close>
paragraph \<open>Defining the type\<close>
typedef dpll\<^sub>W_state =
    "{(M::(int, unit) ann_lits, N::int literal list list).
        dpll\<^sub>W_all_inv (toS M N)}"
  morphisms rough_state_of state_of
proof
    show "([],[]) \<in> {(M, N). dpll\<^sub>W_all_inv (toS M N)}" by (auto simp add: dpll\<^sub>W_all_inv_def)
qed

paragraph \<open>Some type classes\<close>
instantiation dpll\<^sub>W_state :: equal
begin
definition equal_dpll\<^sub>W_state :: "dpll\<^sub>W_state \<Rightarrow> dpll\<^sub>W_state \<Rightarrow> bool" where
 "equal_dpll\<^sub>W_state S S' = (rough_state_of S = rough_state_of S')"
instance
  by standard (simp add: rough_state_of_inject equal_dpll\<^sub>W_state_def)
end

paragraph \<open>DPLL\<close>
definition DPLL_step' :: "dpll\<^sub>W_state \<Rightarrow> dpll\<^sub>W_state" where
  "DPLL_step' S = state_of (DPLL_step (rough_state_of S))"

declare rough_state_of_inverse[simp]

lemma DPLL_step_dpll\<^sub>W_conc_inv:
  "DPLL_step (rough_state_of S) \<in> {(M, N). dpll\<^sub>W_all_inv (toS M N)}"
proof -
  obtain M N where
    S: \<open>rough_state_of S = (M, N)\<close>
    by (cases \<open>rough_state_of S\<close>)
  obtain M' N' where
    S': \<open>DPLL_step (rough_state_of S) = (M', N')\<close>
    by (cases \<open>DPLL_step (rough_state_of S)\<close>)
  have \<open>dpll\<^sub>W\<^sup>*\<^sup>*  (toS M N) (toS M' N')\<close>
    by (metis DPLL_step_is_a_dpll\<^sub>W_step S S' fst_conv r_into_rtranclp rtranclp.rtrancl_refl snd_conv)
  then show ?thesis
    using rough_state_of[of S] unfolding S' unfolding S by (auto intro: rtranclp_dpll\<^sub>W_all_inv)
qed

lemma rough_state_of_DPLL_step'_DPLL_step[simp]:
  "rough_state_of (DPLL_step' S) = DPLL_step (rough_state_of S)"
  using DPLL_step_dpll\<^sub>W_conc_inv DPLL_step'_def state_of_inverse by auto

function DPLL_tot:: "dpll\<^sub>W_state \<Rightarrow> dpll\<^sub>W_state" where
"DPLL_tot S =
  (let S' = DPLL_step' S in
   if S' = S then S else DPLL_tot S')"
  by fast+
termination
proof (relation "{(T', T).
     (rough_state_of T', rough_state_of T)
        \<in> {(S', S). (toS' S', toS' S)
              \<in> {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S S'}}}")
  show "wf {(b, a).
          (rough_state_of b, rough_state_of a)
            \<in> {(b, a). (toS' b, toS' a)
              \<in> {(b, a). dpll\<^sub>W_all_inv a \<and> dpll\<^sub>W a b}}}"
    using wf_if_measure_f[OF wf_if_measure_f[OF wf_dpll\<^sub>W, of "toS'"], of rough_state_of] .
next
  fix S x
  assume x: "x = DPLL_step' S"
  and "x \<noteq> S"
  have "dpll\<^sub>W_all_inv (case rough_state_of S of (Ms, N) \<Rightarrow> (Ms, mset (map mset N)))"
    by (metis (no_types, lifting) case_prodE mem_Collect_eq old.prod.case rough_state_of)
  moreover have "dpll\<^sub>W (case rough_state_of S of (Ms, N) \<Rightarrow> (Ms, mset (map mset N)))
                      (case rough_state_of (DPLL_step' S) of (Ms, N) \<Rightarrow> (Ms, mset (map mset N)))"
    proof -
      obtain Ms N where Ms: "(Ms, N) = rough_state_of S" by (cases "rough_state_of S") auto
      have "dpll\<^sub>W_all_inv (toS' (Ms, N))" using calculation unfolding Ms by blast
      moreover obtain Ms' N' where Ms': "(Ms', N') = rough_state_of (DPLL_step' S)"
        by (cases "rough_state_of (DPLL_step' S)") auto
      ultimately have "dpll\<^sub>W_all_inv (toS' (Ms', N'))" unfolding Ms'
        by (metis (no_types, lifting) case_prod_unfold mem_Collect_eq rough_state_of)

      have "dpll\<^sub>W (toS Ms N) (toS Ms' N')"
        apply (rule DPLL_step_is_a_dpll\<^sub>W_step[of Ms' N' Ms N])
        unfolding Ms Ms' using \<open>x \<noteq> S\<close> rough_state_of_inject x by fastforce+
      then show ?thesis unfolding Ms[symmetric] Ms'[symmetric] by auto
    qed
  ultimately show "(x, S) \<in> {(T', T). (rough_state_of T', rough_state_of T)
    \<in> {(S', S). (toS' S', toS' S) \<in> {(S', S). dpll\<^sub>W_all_inv S \<and> dpll\<^sub>W S S'}}}"
    by (auto simp add: x)
qed

lemma [code]:
"DPLL_tot S =
  (let S' = DPLL_step' S in
   if S' = S then S else DPLL_tot S')" by auto

definition DPLL_trail where
  \<open>DPLL_trail S = fst (rough_state_of S)\<close>

lemma DPLL_step'_eq_iff_trail_length: \<open>DPLL_step' S = S \<longleftrightarrow> count_decided (DPLL_trail S) = count_decided (DPLL_trail (DPLL_step' S)) \<and>
  length (DPLL_trail (DPLL_step' S)) = length (DPLL_trail S)\<close>
proof -
  have [dest]: \<open>backtrack_split x1 = (x1a, x21a # x22) \<Longrightarrow> count_decided x1 \<noteq> count_decided x22\<close> for x1 x1a x21a x22
    by (metis add.left_neutral backtrack_split_fst_not_decided
    backtrack_split_list_eq backtrack_split_snd_hd_decided
    cancel_comm_monoid_add_class.diff_cancel count_decided_0_iff
    count_decided_append count_decided_cons lessI list.sel(1) list.simps(3)
    not_gr0 prod.sel(2) zero_less_diff)
  let ?S' = \<open>rough_state_of S\<close>
  have H: \<open>dpll\<^sub>W_all_inv (toS (fst (DPLL_step ?S')) (snd (DPLL_step ?S')))\<close>
    using DPLL_step_dpll\<^sub>W_conc_inv[of S]
    by auto
  have [dest]: \<open>rough_state_of S = (x1, x2) \<Longrightarrow> state_of (x1, x2) = S\<close> for x1 x2
    by (metis rough_state_of_inverse)
  show ?thesis
    by (auto simp: Let_def  DPLL_step'_def DPLL_trail_def DPLL_step_def split: prod.splits option.splits list.splits simp del: DPLL_tot.simps)
      (use H in \<open>auto simp add: DPLL_step_def  dpll\<^sub>W_state.state_of_inverse split: prod.splits option.splits list.splits if_splits\<close>)
qed

lemma [code]:
"DPLL_tot S =
  (let k = count_decided (DPLL_trail S); S' = DPLL_step' S in
  if length (DPLL_trail S') = length (DPLL_trail S) \<and> count_decided (DPLL_trail S') = k then S else DPLL_tot S')"
  by (subst DPLL_tot.simps)
   (auto simp: Let_def DPLL_step'_eq_iff_trail_length  simp del: DPLL_tot.simps)

lemma DPLL_tot_DPLL_step_DPLL_tot[simp]: "DPLL_tot (DPLL_step' S) = DPLL_tot S"
  apply (cases "DPLL_step' S = S")
  apply simp
  unfolding DPLL_tot.simps[of S] by (simp del: DPLL_tot.simps)

lemma DOPLL_step'_DPLL_tot[simp]:
  "DPLL_step' (DPLL_tot S) = DPLL_tot S"
  by (rule DPLL_tot.induct[of "\<lambda>S. DPLL_step' (DPLL_tot S) = DPLL_tot S" S])
     (metis (full_types) DPLL_tot.simps)

lemma DPLL_tot_final_state:
  assumes "DPLL_tot S = S"
  shows "conclusive_dpll\<^sub>W_state (toS' (rough_state_of S))"
proof -
  have "DPLL_step' S = S" using assms[symmetric] DOPLL_step'_DPLL_tot by metis
  then have "DPLL_step (rough_state_of S) = (rough_state_of S)"
    unfolding DPLL_step'_def using DPLL_step_dpll\<^sub>W_conc_inv rough_state_of_inverse
    by (metis rough_state_of_DPLL_step'_DPLL_step)
  then show ?thesis
    by (metis (mono_tags, lifting) DPLL_step_stuck_final_state old.prod.exhaust split_conv)
qed

lemma DPLL_tot_star:
  assumes "rough_state_of (DPLL_tot S) = S'"
  shows "dpll\<^sub>W\<^sup>*\<^sup>* (toS' (rough_state_of S)) (toS' S')"
  using assms
proof (induction arbitrary: S' rule: DPLL_tot.induct)
  case (1 S S')
  let ?x = "DPLL_step' S"
  { assume "?x = S"
    then have ?case using 1(2) by simp
  }
  moreover {
    assume S: "?x \<noteq> S"
    have ?case
      apply (cases "DPLL_step' S = S")
        using S apply blast
      by (smt "1.IH" "1.prems" DPLL_step_is_a_dpll\<^sub>W_step DPLL_tot.simps case_prodE2
        rough_state_of_DPLL_step'_DPLL_step rtranclp.rtrancl_into_rtrancl rtranclp.rtrancl_refl
        rtranclp_idemp split_conv)
  }
  ultimately show ?case by auto
qed

lemma rough_state_of_rough_state_of_Nil[simp]:
  "rough_state_of (state_of ([], N)) = ([], N)"
  apply (rule dpll\<^sub>W_state.state_of_inverse)
  unfolding dpll\<^sub>W_all_inv_def by auto

text \<open>Same clauses\<close>
lemma snd_DPLL_tot:
  assumes \<open>rough_state_of (DPLL_tot S) = S'\<close>
  shows \<open>snd (rough_state_of S) = (snd S')\<close>
  using assms 
proof (induction rule: DPLL_tot.induct)
  case (1 S)
  then show ?case
    by (metis (mono_tags, lifting) DPLL_tot.elims rough_state_of_DPLL_step'_DPLL_step snd_DPLL_step surjective_pairing) 
qed


text \<open>Theorem of correctness\<close>
lemma DPLL_tot_correct:
  assumes "rough_state_of (DPLL_tot (state_of (([], N)))) = (M, N')"
  and "(M', N'') = toS' (M, N')"
  shows "M' \<Turnstile>asm N'' \<longleftrightarrow> satisfiable (set_mset N'')"
proof -
  have "dpll\<^sub>W\<^sup>*\<^sup>* (toS' ([], N)) (toS' (M, N'))" using DPLL_tot_star[OF assms(1)] by auto
  moreover have "conclusive_dpll\<^sub>W_state (toS' (M, N'))"
    using DPLL_tot_final_state by (metis (mono_tags, lifting) DOPLL_step'_DPLL_tot DPLL_tot.simps
      assms(1))
  moreover have \<open>N = N'\<close>
    using assms(1) by (metis rough_state_of_rough_state_of_Nil snd_DPLL_tot snd_eqD) 
  ultimately show ?thesis using dpll\<^sub>W_conclusive_state_correct
    using assms(2) by fastforce 
qed


subsubsection \<open>Code export\<close>

paragraph \<open>A conversion to @{typ dpll\<^sub>W_state}\<close>
definition Con :: "(int, unit) ann_lits \<times> int literal list list
                     \<Rightarrow> dpll\<^sub>W_state" where
  "Con xs = state_of (if dpll\<^sub>W_all_inv (toS (fst xs) (snd xs)) then xs else ([], []))"
lemma [code abstype]:
  "Con (rough_state_of S) = S"
  using rough_state_of[of S] unfolding Con_def by auto

  declare rough_state_of_DPLL_step'_DPLL_step[code abstract]

lemma Con_DPLL_step_rough_state_of_state_of[simp]:
  "Con (DPLL_step (rough_state_of s)) = state_of (DPLL_step (rough_state_of s))"
  unfolding Con_def by (metis (mono_tags, lifting) DPLL_step_dpll\<^sub>W_conc_inv mem_Collect_eq
    prod.case_eq_if)

text \<open>A slightly different version of @{term DPLL_tot} where the returned boolean indicates the
  result.\<close>
definition DPLL_tot_rep where
"DPLL_tot_rep S =
  (let (M, N) = (rough_state_of (DPLL_tot S)) in (\<forall>A \<in> set N. (\<exists>a\<in>set A. a \<in> lits_of_l M), M))"

text \<open>One version of the generated SML code is here, but not included in the generated document.
  The only differences are:
  \<^item> export @{typ "'a literal"} from the SML Module \<open>Clausal_Logic\<close>;
  \<^item> export the constructor @{term Con} from \<open>DPLL_W_Implementation\<close>;
  \<^item> export the @{term int} constructor from \<open>Arith\<close>.

  All these allows to test on the code on some examples.
  \<close>

end

*)

end
