/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.AlgorithmAndRandomVariables
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.ForMathlib.SubGaussian
import LeanBandits.RewardByCountMeasure

/-!
# UCB algorithm

-/

open MeasureTheory ProbabilityTheory Filter Real Finset Learning

open scoped ENNReal NNReal

namespace Bandits

variable {K : ℕ}

section Algorithm

/-- The exploration bonus of the UCB algorithm, which corresponds to the width of
a confidence interval. -/
noncomputable def ucbWidth' (c : ℝ) (n : ℕ) (h : Iic n → Fin K × ℝ) (a : Fin K) : ℝ :=
  √(c * log (n + 2) / pullCount' n h a)

open Classical in
/-- Arm pulled by the UCB algorithm at time `n + 1`. -/
noncomputable
def UCB.nextArm (hK : 0 < K) (c : ℝ) (n : ℕ) (h : Iic n → Fin K × ℝ) : Fin K :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  if n < K - 1 then ⟨(n + 1) % K, Nat.mod_lt _ hK⟩ else
  measurableArgmax (fun h a ↦ empMean' n h a + ucbWidth' c n h a) h

@[fun_prop]
lemma UCB.measurable_nextArm (hK : 0 < K) (c : ℝ) (n : ℕ) : Measurable (nextArm hK c n) := by
  refine Measurable.ite (by simp) (by fun_prop) ?_
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  refine measurable_measurableArgmax fun a ↦ ?_
  unfold ucbWidth'
  fun_prop

/-- The UCB algorithm. -/
noncomputable
def ucbAlgorithm (hK : 0 < K) (c : ℝ) : Algorithm (Fin K) ℝ :=
  detAlgorithm (UCB.nextArm hK c) (by fun_prop) ⟨0, hK⟩

end Algorithm

namespace UCB

variable {hK : 0 < K} {c : ℝ} {ν : Kernel (Fin K) ℝ} [IsMarkovKernel ν] {n : ℕ} {h : ℕ → Fin K × ℝ}

noncomputable def ucbWidth (c : ℝ) (a : Fin K) (n : ℕ) (h : ℕ → Fin K × ℝ) : ℝ :=
  √(c * log (n + 1) / pullCount a n h)

lemma ucbWidth_eq_ucbWidth' (c : ℝ) (a : Fin K) (n : ℕ) (h : ℕ → Fin K × ℝ) (hn : n ≠ 0) :
    ucbWidth c a n h = ucbWidth' c (n - 1) (fun i ↦ h i) a := by
  simp only [ucbWidth, pullCount_eq_pullCount' hn, Nat.cast_nonneg, sqrt_div', ucbWidth']
  congr 4
  norm_cast
  grind

local notation "𝔓t" => Bandit.trajMeasure (ucbAlgorithm hK c) ν
local notation "𝔓" => Bandit.measure (ucbAlgorithm hK c) ν

lemma arm_zero : arm 0 =ᵐ[𝔓t] fun _ ↦ ⟨0, hK⟩ := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact arm_zero_detAlgorithm

lemma arm_ae_eq_ucbNextArm (n : ℕ) :
    arm (n + 1) =ᵐ[𝔓t] fun h ↦ nextArm hK c n (fun i ↦ h i) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact arm_detAlgorithm_ae_eq n

lemma ucbIndex_le_ucbIndex_arm (a : Fin K) (hn : K ≤ n) :
    ∀ᵐ h ∂𝔓t, empMean a n h + ucbWidth c a n h ≤
      empMean (arm n h) n h + ucbWidth c (arm n h) n h := by
  filter_upwards [arm_ae_eq_ucbNextArm (n - 1)] with h h_arm
  have : n - 1 + 1 = n := by grind
  have h_not_lt : ¬ n - 1 < K - 1 := by grind
  simp only [this, nextArm, h_not_lt, ↓reduceIte] at h_arm
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  simp_rw [h_arm, empMean_eq_empMean' (by grind : n ≠ 0),
    ucbWidth_eq_ucbWidth' _ _ _ _ (by grind : n ≠ 0)]
  exact isMaxOn_measurableArgmax (fun h a ↦ empMean' (n - 1) h a + ucbWidth' c (n - 1) h a)
    (fun i ↦ h i) a

omit [IsMarkovKernel ν] in
lemma gap_arm_le_two_mul_ucbWidth [Nonempty (Fin K)]
    (h_best : (ν (bestArm ν))[id] ≤ empMean (bestArm ν) n h + ucbWidth c (bestArm ν) n h)
    (h_arm : empMean (arm n h) n h - ucbWidth c (arm n h) n h ≤ (ν (arm n h))[id])
    (h_le : empMean (bestArm ν) n h + ucbWidth c (bestArm ν) n h ≤
      empMean (arm n h) n h + ucbWidth c (arm n h) n h) :
    gap ν (arm n h) ≤ 2 * ucbWidth c (arm n h) n h := by
  rw [gap_eq_bestArm_sub, sub_le_iff_le_add']
  calc (ν (bestArm ν))[id]
  _ ≤ empMean (bestArm ν) n h + ucbWidth c (bestArm ν) n h := h_best
  _ ≤ empMean (arm n h) n h + ucbWidth c (arm n h) n h := h_le
  _ ≤ (ν (arm n h))[id] + 2 * ucbWidth c (arm n h) n h := by
    rw [two_mul, ← add_assoc]
    gcongr
    rwa [sub_le_iff_le_add] at h_arm

omit [IsMarkovKernel ν] in
lemma pullCount_arm_le [Nonempty (Fin K)] (hc : 0 ≤ c)
    (h_best : (ν (bestArm ν))[id] ≤ empMean (bestArm ν) n h + ucbWidth c (bestArm ν) n h)
    (h_arm : empMean (arm n h) n h - ucbWidth c (arm n h) n h ≤ (ν (arm n h))[id])
    (h_le : empMean (bestArm ν) n h + ucbWidth c (bestArm ν) n h ≤
      empMean (arm n h) n h + ucbWidth c (arm n h) n h)
    (h_gap_pos : 0 < gap ν (arm n h)) (h_pull_pos : 0 < pullCount (arm n h) n h) :
    pullCount (arm n h) n h ≤ 4 * c * log (n + 1) / gap ν (arm n h) ^ 2 := by
  have h_gap_le := gap_arm_le_two_mul_ucbWidth h_best h_arm h_le
  rw [ucbWidth] at h_gap_le
  have h2 : (gap ν (arm n h)) ^ 2 ≤ (2 * √(c * log (n + 1) / pullCount (arm n h) n h)) ^ 2 := by
    gcongr
  rw [mul_pow, sq_sqrt] at h2
  · have : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [this] at h2
    field_simp at h2 ⊢
    exact h2
  · have : 0 ≤ log (n + 1) := by simp [log_nonneg]
    positivity

/-- Bound on the expectation of the number of pulls of each arm by the UCB algorithm. -/
lemma expectation_pullCount_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (a : Fin K) (n : ℕ) :
    𝔓t[fun ω ↦ (pullCount a n ω : ℝ)] ≤ log n / gap ν a ^ 2 + 1 := by
  simp_rw [pullCount_eq_sum]
  sorry

/-- Regret bound for the UCB algorithm. -/
lemma regret_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a)) (n : ℕ) :
    𝔓t[regret ν n] ≤ ∑ a, (log n / gap ν a + gap ν a) := by -- todo: fix that bound
  simp_rw [regret_eq_sum_pullCount_mul_gap]
  rw [integral_finset_sum]
  swap; · sorry -- exact fun i _ ↦ (integrable_pullCount i n).mul_const _
  gcongr with a
  rw [integral_mul_const]
  sorry

end UCB

end Bandits
