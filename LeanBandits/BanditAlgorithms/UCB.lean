/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.AlgorithmBuilding
import LeanBandits.Bandit.Regret

/-!
# UCB algorithm

-/

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal

namespace Bandits

variable {α : Type*} {mα : MeasurableSpace α} {ν : Kernel α ℝ} {t : ℕ} {a : α}

section Algorithm

variable [Nonempty α] [DecidableEq α] [Finite α] [Encodable α] [MeasurableSingletonClass α]

/-- The exploration bonus of the UCB algorithm, which corresponds to the width of
a confidence interval. -/
noncomputable def ucbWidth' (c : ℝ) (n : ℕ) (h : Iic n → α × ℝ) (a : α) : ℝ :=
  √(c * log (n + 1) / (pullCount' n h a))

open Classical in
/-- Arm pulled by the UCB algorithm at time `n + 1`. -/
noncomputable
def ucbNextArm (c : ℝ) (n : ℕ) (h : Iic n → α × ℝ) : α :=
  measurableArgmax (fun h a ↦ empMean' n h a + ucbWidth' c n h a) h

@[fun_prop]
lemma measurable_ucbNextArm (c : ℝ) (n : ℕ) : Measurable (ucbNextArm c n (α := α)) := by
  classical
  refine measurable_measurableArgmax fun a ↦ ?_
  unfold ucbWidth'
  fun_prop

/-- The UCB algorithm. -/
noncomputable
def ucbAlgorithm (c : ℝ) : Algorithm α ℝ :=
  detAlgorithm (ucbNextArm c) (by fun_prop) (Classical.arbitrary α)

end Algorithm

variable [Fintype α] [Nonempty α] {c : ℝ} {μ : α → ℝ} {N : α → ℕ} {a : α}

/-- The exploration bonus of the UCB algorithm, which corresponds to the width of
a confidence interval. -/
noncomputable def ucbWidth (c : ℝ) (N : α → ℕ) (t : ℕ) (a : α) : ℝ := √(c * log t / N a)

/-- The arm pulled by the UCB algorithm. -/
noncomputable
def ucbArm (c : ℝ) (μ : α → ℝ) (N : α → ℕ) (t : ℕ) : α :=
  (exists_max_image univ (fun a ↦ μ a + ucbWidth c N t a)
    (univ_nonempty_iff.mpr inferInstance)).choose

lemma le_ucb (a : α) :
    μ a + ucbWidth c N t a ≤ μ (ucbArm c μ N t) + ucbWidth c N t (ucbArm c μ N t) :=
  (exists_max_image univ (fun a ↦ μ a + ucbWidth c N t a)
    (univ_nonempty_iff.mpr inferInstance)).choose_spec.2 _ (mem_univ a)

lemma gap_ucbArm_le_two_mul_ucbWidth
    (h_best : (ν (bestArm ν))[id] ≤ μ (bestArm ν) + ucbWidth c N t (bestArm ν))
    (h_ucb : μ (ucbArm c μ N t) - ucbWidth c N t (ucbArm c μ N t) ≤ (ν (ucbArm c μ N t))[id]) :
    gap ν (ucbArm c μ N t) ≤ 2 * ucbWidth c N t (ucbArm c μ N t) := by
  rw [gap_eq_bestArm_sub, sub_le_iff_le_add']
  calc (ν (bestArm ν))[id]
  _ ≤ μ (bestArm ν) + ucbWidth c N t (bestArm ν) := h_best
  _ ≤ μ (ucbArm c μ N t) + ucbWidth c N t (ucbArm c μ N t) := le_ucb _
  _ ≤ (ν (ucbArm c μ N t))[id] + 2 * ucbWidth c N t (ucbArm c μ N t) := by
    rw [two_mul, ← add_assoc]
    gcongr
    rwa [sub_le_iff_le_add] at h_ucb

lemma N_ucbArm_le
    (h_best : (ν (bestArm ν))[id] ≤ μ (bestArm ν) + ucbWidth c N t (bestArm ν))
    (h_ucb : μ (ucbArm c μ N t) - ucbWidth c N t (ucbArm c μ N t) ≤ (ν (ucbArm c μ N t))[id]) :
    N (ucbArm c μ N t) ≤ 4 * c * log t / gap ν (ucbArm c μ N t) ^ 2 := by
  have h_gap := gap_ucbArm_le_two_mul_ucbWidth h_best h_ucb
  rw [ucbWidth] at h_gap
  sorry

end Bandits
