/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import Architect
import LeanBandits.SequentialLearning.FiniteActions

/-!
# Regret, gap, best arm

-/

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal

namespace Bandits

variable {α Ω : Type*} [DecidableEq α] {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
  {ν : Kernel α ℝ}
  {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}
  {ω : Ω} {m n t : ℕ} {a : α}

/-- Gap of an action `a`: difference between the highest mean of the actions and the mean of `a`. -/
@[blueprint
  "def:gap"
  (statement := /-- For an arm $a \in \mathcal{A}$, its gap is defined as the difference between the
    mean of the best arm and the mean of that arm: $\Delta_a = \mu^* - \mu_a$. -/)]
noncomputable
def gap (ν : Kernel α ℝ) (a : α) : ℝ := (⨆ i, (ν i)[id]) - (ν a)[id]

omit [DecidableEq α] in
lemma gap_nonneg [Fintype α] : 0 ≤ gap ν a := by
  rw [gap, sub_nonneg]
  exact le_ciSup (f := fun i ↦ (ν i)[id]) (by simp) a

/-- Regret of a sequence of pulls `k : ℕ → α` at time `t` for the reward kernel `ν ; Kernel α ℝ`. -/
@[blueprint
  "def:regret"
  (title := "Regret")
  (statement := /-- The regret $R_T$ of a sequence of arms $A_0, \ldots, A_{T-1}$ after $T$ pulls is
    the difference between the cumulative reward of always playing the best arm and the cumulative
    reward of the sequence:
    \begin{align*}
      R_T = T \mu^* - \sum_{t=0}^{T-1} \mu_{A_t} \: .
    \end{align*} -/)]
noncomputable
def regret (ν : Kernel α ℝ) (A : ℕ → Ω → α) (t : ℕ) (ω : Ω) : ℝ :=
  t * (⨆ a, (ν a)[id]) - ∑ s ∈ range t, (ν (A s ω))[id]

omit [DecidableEq α] in
lemma regret_eq_sum_gap : regret ν A t ω = ∑ s ∈ range t, gap ν (A s ω) := by
  simp [regret, gap]

omit [DecidableEq α] in
lemma regret_nonneg [Fintype α] : 0 ≤ regret ν A t ω := by
  rw [regret_eq_sum_gap]
  exact sum_nonneg (fun _ _ ↦ gap_nonneg)

omit [DecidableEq α] in
lemma gap_eq_zero_of_regret_eq_zero [Fintype α] (hr : regret ν A t ω = 0) {s : ℕ} (hs : s < t) :
    gap ν (A s ω) = 0 := by
  rw [regret_eq_sum_gap] at hr
  exact (sum_eq_zero_iff_of_nonneg fun _ _ ↦ gap_nonneg).1 hr s (mem_range.2 hs)

@[blueprint
  "lem:regret_eq_sum_pullCount_mul_gap"
  (statement := /-- For $\mathcal{A}$ finite, the regret $R_T$ can be expressed as a sum over the
    arms and their gaps:
    \begin{align*}
      R_T = \sum_{a \in \mathcal{A}} N_{T,a} \Delta_a \: .
    \end{align*} -/)
  (proof := /-- Apply Lemma~\ref{lem:sum_pullCount_mul} with $f(a) = \Delta_a$ to obtain:
    \begin{align*}
      \sum_{a \in \mathcal{A}} N_{T,a} \Delta_a
      &= \sum_{s=0}^{T-1} \Delta_{A_s}
      \\
      &= \sum_{s=0}^{T-1} \mu^* - \sum_{s=0}^{T-1} \mu_{A_s}
      \\
      &= R_T
      \: .
    \end{align*} -/)
  (latexEnv := "lemma")]
lemma regret_eq_sum_pullCount_mul_gap [Fintype α] :
    regret ν A t ω = ∑ a, pullCount A a t ω * gap ν a := by
  simp_rw [regret_eq_sum_gap, sum_pullCount_mul]

section bestArm

variable [Fintype α] [Nonempty α]

/-- action with the highest mean. -/
noncomputable def bestArm (ν : Kernel α ℝ) : α :=
  (exists_max_image univ (fun a ↦ (ν a)[id]) (univ_nonempty_iff.mpr inferInstance)).choose

omit [DecidableEq α] in
lemma le_bestArm (a : α) : (ν a)[id] ≤ (ν (bestArm ν))[id] :=
  (exists_max_image univ (fun a ↦ (ν a)[id])
    (univ_nonempty_iff.mpr inferInstance)).choose_spec.2 _ (mem_univ a)

omit [DecidableEq α] in
lemma gap_eq_bestArm_sub : gap ν a = (ν (bestArm ν))[id] - (ν a)[id] := by
  rw [gap]
  congr
  refine le_antisymm ?_ (le_ciSup (f := fun a ↦ (ν a)[id]) (by simp) (bestArm ν))
  exact ciSup_le le_bestArm

omit [DecidableEq α] in
@[simp]
lemma gap_bestArm : gap ν (bestArm ν) = 0 := by
  rw [gap_eq_bestArm_sub, sub_self]

omit [DecidableEq α] in
lemma integral_eq_of_gap_eq_zero (hg : gap ν a = 0) : (ν (bestArm ν))[id] = (ν a)[id] := by
  rwa [← sub_eq_zero, ← gap_eq_bestArm_sub]

end bestArm

section Asymptotics

omit [DecidableEq α] in
/-- If the regret is sublinear, the average mean reward tends to the highest mean of the arms. -/
lemma avg_mean_reward_tendsto_of_sublinear_regret
    (hr : (regret ν A · ω) =o[atTop] fun t ↦ (t : ℝ)) :
    Tendsto (fun t ↦ (∑ s ∈ range t, (ν (A s ω))[id]) / (t : ℝ))
      atTop (nhds (⨆ a, (ν a)[id])) := by
  have ht : Tendsto (fun t ↦ (⨆ a, (ν a)[id]) - regret ν A t ω / t)
      atTop (nhds (⨆ a, (ν a)[id])) := by
    simpa using tendsto_const_nhds.sub hr.tendsto_div_nhds_zero
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with t ht
  rw [regret]
  field_simp
  ring

/-- If the regret is sublinear, the rate of suboptimal arm pulls tends to zero. -/
lemma pullCount_rate_tendsto_of_sublinear_regret [Fintype α]
    (hr : (regret ν A · ω) =o[atTop] fun t ↦ (t : ℝ)) (hg : 0 < gap ν a) :
    Tendsto (fun t ↦ (pullCount A a t ω : ℝ) / t) atTop (nhds 0) := by
  have hb (t : ℕ) : (pullCount A a t ω : ℝ) * gap ν a ≤ regret ν A t ω := by
    rw [regret_eq_sum_pullCount_mul_gap]
    exact single_le_sum (f := fun a ↦ pullCount A a t ω * gap ν a)
      (fun _ _ ↦ mul_nonneg (Nat.cast_nonneg _) gap_nonneg) (mem_univ a)
  have hb' (t : ℕ) : (pullCount A a t ω : ℝ) / t ≤ regret ν A t ω / t / gap ν a := by
    obtain ht | ht := eq_or_ne t 0
    · simp [ht]
    · calc (pullCount A a t ω : ℝ) / t
          = pullCount A a t ω * gap ν a / gap ν a / t := by field_simp
        _ ≤ regret ν A t ω / gap ν a / t := by gcongr; exact hb t
        _ = regret ν A t ω / t / gap ν a := by ring
  apply squeeze_zero' (Eventually.of_forall fun _ ↦ by positivity) (Eventually.of_forall hb')
  simpa using hr.tendsto_div_nhds_zero.div_const (gap ν a)

end Asymptotics

end Bandits
