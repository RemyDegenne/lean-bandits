/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.SubGaussian
import LeanBandits.AlgorithmBuilding
import LeanBandits.ForMathlib.SubGaussian
import LeanBandits.Regret

/-! # The Explore-Then-Commit Algorithm

-/

open MeasureTheory ProbabilityTheory Finset Learning
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
    else (h ⟨n, by simp⟩).1

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

local notation "𝔓t" => Bandit.trajMeasure (etcAlgorithm hK m) ν
local notation "𝔓" => Bandit.measure (etcAlgorithm hK m) ν

lemma arm_zero : arm 0 =ᵐ[𝔓t] fun _ ↦ ⟨0, hK⟩ := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact arm_zero_detAlgorithm

lemma arm_ae_eq_etcNextArm (n : ℕ) :
    arm (n + 1) =ᵐ[𝔓t] fun h ↦ nextArm hK m n (fun i ↦ h i) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact arm_detAlgorithm_ae_eq n

lemma arm_of_lt {n : ℕ} (hn : n < K * m) :
    arm n =ᵐ[𝔓t] fun _ ↦ ⟨n % K, Nat.mod_lt _ hK⟩ := by
  cases n with
  | zero => exact arm_zero
  | succ n =>
    filter_upwards [arm_ae_eq_etcNextArm n] with h hn_eq
    rw [hn_eq, nextArm, dif_pos]
    grind

lemma arm_mul (hm : m ≠ 0) :
    have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
    arm (K * m) =ᵐ[𝔓t] fun h ↦ measurableArgmax (empMean' (K * m - 1)) (fun i ↦ h i) := by
  have : K * m = (K * m - 1) + 1 := by
    have : 0 < K * m := Nat.mul_pos hK hm.bot_lt
    grind
  rw [this]
  filter_upwards [arm_ae_eq_etcNextArm (K * m - 1)] with h hn_eq
  rw [hn_eq, nextArm, dif_neg (by simp), dif_pos rfl]
  exact this ▸ rfl

lemma arm_add_one_of_ge {n : ℕ} (hm : m ≠ 0) (hn : K * m ≤ n) :
    arm (n + 1) =ᵐ[𝔓t] fun ω ↦ arm n ω := by
  filter_upwards [arm_ae_eq_etcNextArm n] with ω hn_eq
  rw [hn_eq, nextArm, dif_neg (by grind), dif_neg]
  · rfl
  · have : 0 < K * m := Nat.mul_pos hK hm.bot_lt
    grind

lemma arm_of_ge {n : ℕ} (hm : m ≠ 0) (hn : K * m ≤ n) : arm n =ᵐ[𝔓t] arm (K * m) := by
  have h_ae n : K * m ≤ n → arm (n + 1) =ᵐ[𝔓t] fun ω ↦ arm n ω := arm_add_one_of_ge hm
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at h_ae
  filter_upwards [h_ae] with ω h_ae
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hmn h_ind => rw [h_ae n hmn, h_ind]

lemma pullCount_mul (a : Fin K) : pullCount a (K * m) =ᵐ[𝔓t] fun _ ↦ m := by
  rw [Filter.EventuallyEq]
  simp_rw [pullCount_eq_sum]
  have h_arm (n : range (K * m)) : arm n =ᵐ[𝔓t] fun _ ↦ ⟨n % K, Nat.mod_lt _ hK⟩ :=
    arm_of_lt (mem_range.mp n.2)
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at h_arm
  filter_upwards [h_arm] with ω h_arm
  have h_arm' {i : ℕ} (hi : i ∈ range (K * m)) : arm i ω = ⟨i % K, Nat.mod_lt _ hK⟩ := h_arm ⟨i, hi⟩
  calc (∑ s ∈ range (K * m), if arm s ω = a then 1 else 0)
  _ = (∑ s ∈ range (K * m), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) :=
    sum_congr rfl fun s hs ↦ by rw [h_arm' hs]
  _ = m := by
    sorry

lemma pullCount_add_one_of_ge (a : Fin K) (hm : m ≠ 0) {n : ℕ} (hn : K * m ≤ n) :
    pullCount a (n + 1)
      =ᵐ[𝔓t] fun ω ↦ pullCount a n ω + {ω' | arm (K * m) ω' = a}.indicator (fun _ ↦ 1) ω := by
  simp_rw [Filter.EventuallyEq, pullCount_add_one]
  filter_upwards [arm_of_ge hm hn] with ω h_arm
  congr

lemma pullCount_of_ge (a : Fin K) (hm : m ≠ 0) {n : ℕ} (hn : K * m ≤ n) :
    pullCount a n
      =ᵐ[𝔓t] fun ω ↦ m + (n - K * m) * {ω' | arm (K * m) ω' = a}.indicator (fun _ ↦ 1) ω := by
  have h_ae n : K * m ≤ n → pullCount a (n + 1)
      =ᵐ[𝔓t] fun ω ↦ pullCount a n ω + {ω' | arm (K * m) ω' = a}.indicator (fun _ ↦ 1) ω :=
    pullCount_add_one_of_ge a hm
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at h_ae
  have h_ae_Km : pullCount a (K * m) =ᵐ[𝔓t] fun _ ↦ m := pullCount_mul a
  filter_upwards [h_ae_Km, h_ae] with ω h_Km h_ae
  induction n, hn using Nat.le_induction with
  | base => simp [h_Km]
  | succ n hmn h_ind =>
    rw [h_ae n hmn, h_ind, add_assoc, ← add_one_mul]
    congr
    grind

lemma prob_arm_mul_eq_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a)) (a : Fin K) :
    (𝔓t).real {ω | arm (K * m) ω = a} ≤ Real.exp (- (m : ℝ) * gap ν a ^ 2 / 4) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  -- extend the probability space to include the stream of independent rewards
  suffices (𝔓).real {ω | arm (K * m) ω.1 = a} ≤ Real.exp (- (m : ℝ) * gap ν a ^ 2 / 4) by
    suffices (𝔓t).real {ω | arm (K * m) ω = a} = (𝔓).real {ω | arm (K * m) ω.1 = a} by
      rwa [this]
    calc (𝔓t).real {ω | arm (K * m) ω = a}
    _ = ((𝔓).fst).real {ω | arm (K * m) ω = a} := by simp
    _ = (𝔓).real {ω | arm (K * m) ω.1 = a} := by
      rw [Measure.fst, map_measureReal_apply (by fun_prop)]
      · rfl
      · exact (measurableSet_singleton _).preimage (by fun_prop)
  calc (𝔓).real {ω | arm (K * m) ω.1 = a}
  _ ≤ (𝔓).real {ω | ∑ s ∈ range (K * m), (if (arm s ω.1) = bestArm ν then (reward s ω.1) else 0)
      ≤ ∑ s ∈ range (K * m), if (arm s ω.1) = a then (reward s ω.1) else 0} := by
    sorry
  _ = (𝔓).real {ω | ∑ s ∈ Icc 1 (pullCount (bestArm ν) (K * m) ω.1),
        rewardByCount (bestArm ν) s ω.1 ω.2
      ≤ ∑ s ∈ Icc 1 (pullCount a (K * m) ω.1), rewardByCount a s ω.1 ω.2} := by
    sorry
  _ = (𝔓).real {ω | ∑ s ∈ Icc 1 m, rewardByCount (bestArm ν) s ω.1 ω.2
      ≤ ∑ s ∈ Icc 1 m, rewardByCount a s ω.1 ω.2} := by
    sorry
  _ = (𝔓).real {ω | ∑ s ∈ range m, ω.2 s (bestArm ν) ≤ ∑ s ∈ range m, ω.2 s a} := by
    sorry
  _ = (𝔓).real {ω | m * gap ν a
      ≤ ∑ s ∈ range m, ((ω.2 s a - (ν a)[id]) - (ω.2 s (bestArm ν) - (ν (bestArm ν))[id]))} := by
    congr with ω
    simp only [gap_eq_bestArm_sub, id_eq, sum_sub_distrib, sum_const, card_range, nsmul_eq_mul]
    ring_nf
    simp
  _ ≤ Real.exp (-↑m * gap ν a ^ 2 / 4) := by
    refine (HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun (c := 2) (ε := m * gap ν a)
      ?_ ?_ ?_).trans_eq ?_
    · suffices iIndepFun (fun s ω ↦ ω s a - (ν a)[id] - (ω s (bestArm ν) - (ν (bestArm ν))[id]))
          (Bandit.streamMeasure ν) by
        sorry
      sorry
    · intro i him
      rw [← one_add_one_eq_two]
      refine HasSubgaussianMGF.sub_of_indepFun ?_ ?_ ?_
      · sorry
      · sorry
      · sorry
    · have : 0 ≤ gap ν a := gap_nonneg
      positivity
    · congr 1
      field_simp
      simp_rw [mul_assoc]
      simp only [NNReal.coe_ofNat, neg_inj, mul_eq_mul_left_iff, ne_eq, OfNat.ofNat_ne_zero,
        not_false_eq_true, pow_eq_zero_iff, Nat.cast_eq_zero]
      norm_num

lemma expectation_pullCount_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a))
    (a : Fin K) (hm : m ≠ 0) {n : ℕ} (hn : K * m ≤ n) :
    𝔓t[fun ω ↦ (pullCount a n ω : ℝ)]
      ≤ m + (n - K * m) * Real.exp (- (m : ℝ) * gap ν a ^ 2 / 4) := by
  have : (fun ω ↦ (pullCount a n ω : ℝ))
      =ᵐ[𝔓t] fun ω ↦ m + (n - K * m) * {ω' | arm (K * m) ω' = a}.indicator (fun _ ↦ 1) ω := by
    filter_upwards [pullCount_of_ge a hm hn] with ω h
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
    exact prob_arm_mul_eq_le hν a
  · exact (measurableSet_singleton _).preimage (by fun_prop)

lemma regret_le (hν : ∀ a, HasSubgaussianMGF (fun x ↦ x - (ν a)[id]) 1 (ν a)) (hm : m ≠ 0)
    (n : ℕ) (hn : K * m ≤ n) :
    𝔓t[regret ν n] ≤ ∑ a, gap ν a * (m + (n - K * m) * Real.exp (- (m : ℝ) * gap ν a ^ 2 / 4)) := by
  simp_rw [regret_eq_sum_pullCount_mul_gap]
  rw [integral_finset_sum]
  swap
  · refine fun i _ ↦ Integrable.mul_const ?_ _
    sorry
  gcongr with a
  rw [mul_comm (gap _ _), integral_mul_const]
  gcongr
  · exact gap_nonneg
  · exact expectation_pullCount_le hν a hm hn

end ETC

end Bandits
