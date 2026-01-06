/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.Bandit.Bandit
import LeanBandits.SequentialLearning.FiniteActions

/-!
# Regret

-/

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal

namespace Bandits

variable {α : Type*} [DecidableEq α] {mα : MeasurableSpace α} {ν : Kernel α ℝ}
  {h : ℕ → α × ℝ} {m n t : ℕ} {a : α}

/-! ### Definitions of gaps, regret, pull counts -/

/-- Gap of an arm `a`: difference between the highest mean of the arms and the mean of `a`. -/
noncomputable
def gap (ν : Kernel α ℝ) (a : α) : ℝ := (⨆ i, (ν i)[id]) - (ν a)[id]

omit [DecidableEq α] in
lemma gap_nonneg [Fintype α] : 0 ≤ gap ν a := by
  rw [gap, sub_nonneg]
  exact le_ciSup (f := fun i ↦ (ν i)[id]) (by simp) a

/-- Regret of a sequence of pulls `k : ℕ → α` at time `t` for the reward kernel `ν ; Kernel α ℝ`. -/
noncomputable
def regret (ν : Kernel α ℝ) (t : ℕ) (h : ℕ → α × ℝ) : ℝ :=
  t * (⨆ a, (ν a)[id]) - ∑ s ∈ range t, (ν (arm s h))[id]

omit [DecidableEq α] in
lemma regret_eq_sum_gap : regret ν t h = ∑ s ∈ range t, gap ν (arm s h) := by
  simp [regret, gap]

omit [DecidableEq α] in
lemma regret_nonneg [Fintype α] : 0 ≤ regret ν t h := by
  rw [regret_eq_sum_gap]
  exact sum_nonneg (fun _ _ ↦ gap_nonneg)

omit [DecidableEq α] in
lemma gap_eq_zero_of_regret_eq_zero [Fintype α] (hr : regret ν t h = 0) {s : ℕ} (hs : s < t) :
    gap ν (arm s h) = 0 := by
  rw [regret_eq_sum_gap] at hr
  exact (sum_eq_zero_iff_of_nonneg fun _ _ ↦ gap_nonneg).1 hr s (mem_range.2 hs)

lemma arm_stepsUntil (hm : m ≠ 0) (h_exists : ∃ s, pullCount a (s + 1) h = m) :
    arm (stepsUntil a m h).toNat h = a := by
  exact action_stepsUntil hm h_exists

lemma arm_eq_of_stepsUntil_eq_coe {ω : ℕ → α × ℝ} (hm : m ≠ 0)
    (h : stepsUntil a m ω = n) :
    arm n ω = a := by
  exact action_eq_of_stepsUntil_eq_coe hm h

section RewardByCount

lemma regret_eq_sum_pullCount_mul_gap [Fintype α] :
    regret ν t h = ∑ a, pullCount a t h * gap ν a := by
  simp_rw [regret_eq_sum_gap, sum_pullCount_mul, arm, action]

end RewardByCount

section BestArm

variable [Fintype α] [Nonempty α]

/-- Arm with the highest mean. -/
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
lemma integral_id_eq_of_gap_eq_zero (hg : gap ν a = 0) : (ν a)[id] = (ν (bestArm ν))[id] := by
  rw [gap_eq_bestArm_sub, sub_eq_zero] at hg
  exact hg.symm

omit [DecidableEq α] in
@[simp]
lemma gap_bestArm : gap ν (bestArm ν) = 0 := by
  rw [gap_eq_bestArm_sub, sub_self]

/-- Number of times an optimal arm was chosen up to time `t` (excluding `t`). -/
noncomputable
def bestPullCount (ν : Kernel α ℝ) (t : ℕ) (h : ℕ → α × ℝ) : ℕ :=
  #(filter (fun s ↦ gap ν (arm s h) = 0) (range t))

omit [DecidableEq α] [Nonempty α] in
lemma bestPullCount_eq_of_regret_eq_zero (hr : regret ν t h = 0) : bestPullCount ν t h = t := by
  rw [bestPullCount, filter_true_of_mem, card_range]
  exact fun s hs ↦ gap_eq_zero_of_regret_eq_zero hr (mem_range.1 hs)

end BestArm

section Asymptotics

omit [DecidableEq α] in
lemma tendsto_highest_mean_of_sublinear_regret (hr : (regret ν · h) =o[atTop] fun t ↦ (t : ℝ)) :
    Tendsto (fun t ↦ (∑ s ∈ range t, (ν (arm s h))[id]) / (t : ℝ))
      atTop (nhds (⨆ a, (ν a)[id])) := by
  have ht : Tendsto (fun t ↦ (⨆ a, (ν a)[id]) - regret ν t h / t)
      atTop (nhds (⨆ a, (ν a)[id])) := by
    simpa using (tendsto_const_nhds.sub hr.tendsto_div_nhds_zero)
  apply ht.congr'
  filter_upwards [eventually_ne_atTop 0] with t ht
  rw [regret]
  field_simp
  ring

end Asymptotics

end Bandits
