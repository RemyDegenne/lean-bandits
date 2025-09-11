/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.SubGaussian
import LeanBandits.AlgorithmBuilding
import LeanBandits.Regret

/-! # The Explore-Then-Commit Algorithm

-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Bandits

variable {K : ℕ}

/-- Arm pulled by the ETC algorithm at time `n + 1`. -/
noncomputable
def ETC.nextArm (hK : 0 < K) (m n : ℕ) (h : Iic n → Fin K × ℝ) : Fin K :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  if hn : n < K * m - 1 then
    ⟨(n + 1) % K, Nat.mod_lt _ hK⟩ -- for `n = 0` we have pulled arm 0 already, and we pull arm 1
  else
    if hn_eq : n = K * m - 1 then measurableArgmax (empMean' n) h
    else (h ⟨n - 1, by simp⟩).1

@[fun_prop]
lemma ETC.measurable_nextArm (hK : 0 < K) (m n : ℕ) : Measurable (nextArm hK m n) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  unfold nextArm
  simp only [dite_eq_ite]
  refine Measurable.ite (by simp) (by fun_prop) ?_
  refine Measurable.ite (by simp) ?_ (by fun_prop)
  exact measurable_measurableArgmax fun a ↦ by fun_prop

/-- The Explore-Then-Commit algorithm. -/
noncomputable
def etcAlgorithm (hK : 0 < K) (m : ℕ) : Algorithm (Fin K) ℝ :=
  detAlgorithm (ETC.nextArm hK m) (by fun_prop) ⟨0, hK⟩

namespace ETC

variable {hK : 0 < K} {m : ℕ} {ν : Kernel (Fin K) ℝ} [IsMarkovKernel ν]

local notation "𝔓b" => Bandit.trajMeasure (etcAlgorithm hK m) ν
local notation "𝔓" => Bandit.measure (etcAlgorithm hK m) ν

lemma arm_zero : arm 0 =ᵐ[𝔓b] fun _ ↦ ⟨0, hK⟩ := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact arm_zero_detAlgorithm

lemma arm_ae_eq_etcNextArm (n : ℕ) :
    arm (n + 1) =ᵐ[𝔓b] fun h ↦ nextArm hK m n (fun i ↦ h i) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact arm_detAlgorithm_ae_eq n

lemma pullCount_mul (a : Fin K) :
    (fun ω ↦ pullCount (arm · ω) a (K * m)) =ᵐ[𝔓b] fun _ ↦ m := by
  sorry

lemma pullCount_of_ge (a : Fin K) {n : ℕ} (hn : K * m ≤ n) :
    (fun ω ↦ pullCount (arm · ω) a n)
      =ᵐ[𝔓b] fun ω ↦ m + (n - K * m) * {ω' | arm (K * m) ω' = a}.indicator (fun _ ↦ 1) ω := by
  sorry

lemma prob_arm_mul_eq_le (a : Fin K) :
    (𝔓b).real {ω | arm (K * m) ω = a} ≤ Real.exp (- (m : ℝ) * gap ν a ^ 2 / 4) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  suffices (𝔓).real {ω | arm (K * m) ω.1 = a} ≤ Real.exp (- (m : ℝ) * gap ν a ^ 2 / 4) by
    sorry
  calc (𝔓).real {ω | arm (K * m) ω.1 = a}
  _ ≤ (𝔓).real {ω | ∑ s ∈ range (K * m), (if (arm s ω.1) = bestArm ν then (reward s ω.1) else 0)
      ≤ ∑ s ∈ range (K * m), if (arm s ω.1) = a then (reward s ω.1) else 0} := by
    sorry
  _ = (𝔓).real {ω | ∑ s ∈ Icc 1 (pullCount (arm · ω.1) (bestArm ν) (K * m)),
        rewardByCount (bestArm ν) s ω.1 ω.2
      ≤ ∑ s ∈ Icc 1 (pullCount (arm · ω.1) a (K * m)), rewardByCount a s ω.1 ω.2} := by
    sorry
  _ = (𝔓).real {ω | ∑ s ∈ Icc 1 m, rewardByCount (bestArm ν) s ω.1 ω.2
      ≤ ∑ s ∈ Icc 1 m, rewardByCount a s ω.1 ω.2} := by
    sorry
  _ = (𝔓).real {ω | ∑ s ∈ Icc 1 m, ω.2 s (bestArm ν) ≤ ∑ s ∈ Icc 1 m, ω.2 s a} := by
    sorry
  _ = (𝔓).real {ω | gap ν a
      ≤ ∑ s ∈ Icc 1 m, ((ω.2 s a - (ν a)[id]) - (ω.2 s (bestArm ν) - (ν (bestArm ν))[id]))} := by
    sorry
  _ = (𝔓).real {ω | gap ν a
      ≤ ∑ s ∈ range m, ((ω.2 s a - (ν a)[id]) - (ω.2 s (bestArm ν) - (ν (bestArm ν))[id]))} := by
    sorry
  _ ≤ Real.exp (-↑m * gap ν a ^ 2 / 4) := by
    sorry

lemma expectation_pullCount_le (a : Fin K) {n : ℕ} (hn : K * m ≤ n) :
    𝔓b[fun ω ↦ (pullCount (arm · ω) a n : ℝ)]
      ≤ m + (n - K * m) * Real.exp (- (m : ℝ) * gap ν a ^ 2 / 4) := by
  have : (fun ω ↦ (pullCount (arm · ω) a n : ℝ))
      =ᵐ[𝔓b] fun ω ↦ m + (n - K * m) * {ω' | arm (K * m) ω' = a}.indicator (fun _ ↦ 1) ω := by
    filter_upwards [pullCount_of_ge a hn] with ω h
    simp only [h, Set.indicator_apply, Set.mem_setOf_eq, mul_ite, mul_one, mul_zero, Nat.cast_add,
      Nat.cast_ite, CharP.cast_eq_zero, add_right_inj]
    norm_cast
  rw [integral_congr_ae this, integral_add (integrable_const _), integral_const_mul]
  swap
  · refine Integrable.const_mul ?_ _
    rw [integrable_indicator_iff]
    · exact integrableOn_const
    · exact (measurableSet_singleton _).preimage (by fun_prop)
  simp only [integral_const, measureReal_univ_eq_one, smul_eq_mul, one_mul, neg_mul,
    add_le_add_iff_left, ge_iff_le]
  gcongr
  · norm_cast
    simp
  rw [integral_indicator_const, smul_eq_mul, mul_one]
  · rw [← neg_mul]
    exact prob_arm_mul_eq_le a
  · exact (measurableSet_singleton _).preimage (by fun_prop)

lemma regret_le (n : ℕ) (hn : K * m ≤ n) : -- todo: remove hn
    𝔓b[fun ω ↦ regret ν (arm · ω) n]
      ≤ ∑ a, gap ν a * (m + (n - K * m) * Real.exp (- (m : ℝ) * gap ν a ^ 2 / 4)) := by
  simp_rw [regret_eq_sum_pullCount_mul_gap]
  rw [integral_finset_sum]
  swap
  · refine fun i _ ↦ Integrable.mul_const ?_ _
    sorry
  gcongr with a
  rw [mul_comm (gap _ _), integral_mul_const]
  gcongr
  · exact gap_nonneg
  · exact expectation_pullCount_le a hn

end ETC

end Bandits
