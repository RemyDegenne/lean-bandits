/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.SequentialLearning.FiniteActions

/-!
# Regret

-/

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal

namespace Bandits

variable {α Ω : Type*} [DecidableEq α] {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
  {ν : Kernel α ℝ}
  {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ}
  {ω : Ω} {m n t : ℕ} {a : α}

/-! ### Definitions of regret, gaps, pull counts -/

/-- Regret of a sequence of pulls `k : ℕ → α` at time `t` for the reward kernel `ν ; Kernel α ℝ`. -/
noncomputable
def regret (ν : Kernel α ℝ) (A : ℕ → Ω → α) (t : ℕ) (ω : Ω) : ℝ :=
  t * (⨆ a, (ν a)[id]) - ∑ s ∈ range t, (ν (A s ω))[id]

/-- Gap of an action `a`: difference between the highest mean of the actions and the mean of `a`. -/
noncomputable
def gap (ν : Kernel α ℝ) (a : α) : ℝ := (⨆ i, (ν i)[id]) - (ν a)[id]

omit [DecidableEq α] in
lemma gap_nonneg [Fintype α] : 0 ≤ gap ν a := by
  rw [gap, sub_nonneg]
  exact le_ciSup (f := fun i ↦ (ν i)[id]) (by simp) a

section RewardByCount

lemma regret_eq_sum_pullCount_mul_gap [Fintype α] :
    regret ν A t ω = ∑ a, pullCount A a t ω * gap ν a := by
  simp [sum_pullCount_mul, regret, gap, sum_sub_distrib]

end RewardByCount

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

end bestArm

end Bandits
