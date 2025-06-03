/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib

/-!
# Regret

-/

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Bandits

variable {α : Type*} {mα : MeasurableSpace α} {ν : Kernel α ℝ} {k : ℕ → α} {t : ℕ} {a : α}

/-! ### Definitions of regret, gaps, pull counts -/

/-- Regret of a sequence of pulls `k : ℕ → α` at time `t` for the reward kernel `ν ; Kernel α ℝ`. -/
noncomputable
def regret (ν : Kernel α ℝ) (k : ℕ → α) (t : ℕ) : ℝ :=
  t * (⨆ a, (ν a)[id]) - ∑ s ∈ range t, (ν (k s))[id]

/-- Gap of an arm `a`: difference between the highest mean of the arms and the mean of `a`. -/
noncomputable
def gap (ν : Kernel α ℝ) (a : α) : ℝ := (⨆ i, (ν i)[id]) - (ν a)[id]

lemma gap_nonneg [Fintype α] : 0 ≤ gap ν a := by
  rw [gap, sub_nonneg]
  exact le_ciSup (f := fun i ↦ (ν i)[id]) (by simp) a

open Classical in
/-- Number of times arm `a` was pulled up to time `t`. -/
noncomputable def pullCount (k : ℕ → α) (a : α) (t : ℕ) : ℕ := #(filter (fun s ↦ k s = a) (range t))

lemma sum_pullCount_mul [Fintype α] (k : ℕ → α) (f : α → ℝ) (t : ℕ) :
    ∑ a, pullCount k a t * f a = ∑ s ∈ range t, f (k s) := by
  unfold pullCount
  classical
  simp_rw [card_eq_sum_ones]
  push_cast
  simp_rw [sum_mul, one_mul]
  exact sum_fiberwise' (range t) k f

lemma sum_pullCount [Fintype α] : ∑ a, pullCount k a t = t := by
  suffices ∑ a, pullCount k a t * (1 : ℝ) = t by norm_cast at this; simpa
  rw [sum_pullCount_mul]
  simp

lemma regret_eq_sum_pullCount_mul_gap [Fintype α] :
    regret ν k t = ∑ a, pullCount k a t * gap ν a := by
  simp_rw [sum_pullCount_mul, regret, gap, sum_sub_distrib]
  simp

section BestArm

variable [Fintype α] [Nonempty α]

/-- Arm with the highest mean. -/
noncomputable def bestArm (ν : Kernel α ℝ) : α :=
  (exists_max_image univ (fun a ↦ (ν a)[id]) (univ_nonempty_iff.mpr inferInstance)).choose

lemma le_bestArm (a : α) : (ν a)[id] ≤ (ν (bestArm ν))[id] :=
  (exists_max_image univ (fun a ↦ (ν a)[id])
    (univ_nonempty_iff.mpr inferInstance)).choose_spec.2 _ (mem_univ a)

lemma gap_eq_bestArm_sub : gap ν a = (ν (bestArm ν))[id] - (ν a)[id] := by
  rw [gap]
  congr
  refine le_antisymm ?_ (le_ciSup (f := fun a ↦ (ν a)[id]) (by simp) (bestArm ν))
  exact ciSup_le le_bestArm

end BestArm

end Bandits
