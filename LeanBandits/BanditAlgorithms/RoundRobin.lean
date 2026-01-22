/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.BanditAlgorithms.AuxSums
import LeanBandits.SequentialLearning.Deterministic
import LeanBandits.SequentialLearning.FiniteActions
import LeanBandits.SequentialLearning.StationaryEnv

/-! # Round-Robin algorithm

That algorithm pulls each arm in a round-robin fashion.

-/

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal NNReal

namespace Bandits

variable {K : ℕ}

section AlgorithmDefinition

/-- Arm pulled by the Round-Robin algorithm at time `n + 1`. This is arm `n % K`. -/
noncomputable
def RoundRobin.nextArm (hK : 0 < K) (n : ℕ) : Fin K := ⟨(n + 1) % K, Nat.mod_lt _ hK⟩

/-- The Round-Robin algorithm: deterministic algorithm that chooses the next arm according
to `RoundRobin.nextArm`. -/
noncomputable
def roundRobinAlgorithm (hK : 0 < K) : Algorithm (Fin K) ℝ :=
  detAlgorithm (fun n _ ↦ RoundRobin.nextArm hK n) (by fun_prop) ⟨0, hK⟩

end AlgorithmDefinition

namespace RoundRobin

variable {hK : 0 < K} {ν : Kernel (Fin K) ℝ} [IsMarkovKernel ν]
  {Ω : Type*} {mΩ : MeasurableSpace Ω}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {A : ℕ → Ω → Fin K} {R : ℕ → Ω → ℝ}

lemma arm_zero [Nonempty (Fin K)]
    (h : IsAlgEnvSeqUntil A R (roundRobinAlgorithm hK) (stationaryEnv ν) P 0) :
    A 0 =ᵐ[P] fun _ ↦ ⟨0, hK⟩ := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  exact h.action_zero_detAlgorithm

lemma arm_ae_eq_roundRobinNextArm [Nonempty (Fin K)] (n : ℕ)
    (h : IsAlgEnvSeqUntil A R (roundRobinAlgorithm hK) (stationaryEnv ν) P (n + 1)) :
    A (n + 1) =ᵐ[P] fun _ ↦ nextArm hK n :=
  h.action_detAlgorithm_ae_eq (by grind)

/-- The arm pulled at time `n` is the arm `n % K`. -/
lemma arm_ae_eq [Nonempty (Fin K)] (n : ℕ)
    (h : IsAlgEnvSeqUntil A R (roundRobinAlgorithm hK) (stationaryEnv ν) P n) :
    A n =ᵐ[P] fun _ ↦ ⟨n % K, Nat.mod_lt _ hK⟩ := by
  cases n with
  | zero => exact arm_zero h
  | succ n =>
    filter_upwards [arm_ae_eq_roundRobinNextArm n h] with h hn_eq
    rw [hn_eq, nextArm]

/-- At time `K * m`, the number of pulls of each arm is equal to `m`. -/
lemma pullCount_mul [Nonempty (Fin K)] (m : ℕ)
    (h : IsAlgEnvSeqUntil A R (roundRobinAlgorithm hK) (stationaryEnv ν) P (K * m - 1))
    (a : Fin K) :
    pullCount A a (K * m) =ᵐ[P] fun _ ↦ m := by
  rw [Filter.EventuallyEq]
  simp_rw [pullCount_eq_sum]
  have h_arm (n : range (K * m)) : A n =ᵐ[P] fun _ ↦ ⟨n % K, Nat.mod_lt _ hK⟩ :=
    arm_ae_eq n (h.mono (by have := n.2; simp only [mem_range] at this; grind))
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at h_arm
  filter_upwards [h_arm] with ω h_arm
  have h_arm' {i : ℕ} (hi : i ∈ range (K * m)) : A i ω = ⟨i % K, Nat.mod_lt _ hK⟩ := h_arm ⟨i, hi⟩
  calc (∑ s ∈ range (K * m), if A s ω = a then 1 else 0)
  _ = (∑ s ∈ range (K * m), if ⟨s % K, Nat.mod_lt _ hK⟩ = a then 1 else 0) :=
    sum_congr rfl fun s hs ↦ by rw [h_arm' hs]
  _ = m := sum_mod_range_mul hK m a

lemma pullCount_eq_one [Nonempty (Fin K)]
    (h : IsAlgEnvSeqUntil A R (roundRobinAlgorithm hK) (stationaryEnv ν) P (K - 1))
    (a : Fin K) :
    pullCount A a K =ᵐ[P] fun _ ↦ 1 := by
  suffices pullCount A a (K * 1) =ᵐ[P] fun _ ↦ 1 by simpa using this
  refine pullCount_mul 1 (P := P) (ν := ν) (R := R) (hK := hK) ?_ a
  simpa

lemma time_gt_of_pullCount_gt_one [Nonempty (Fin K)]
    (h : IsAlgEnvSeqUntil A R (roundRobinAlgorithm hK) (stationaryEnv ν) P (K - 1)) (a : Fin K) :
    ∀ᵐ ω ∂P, ∀ n, 1 < pullCount A a n ω → K < n := by
  filter_upwards [pullCount_eq_one h a] with h h_eq n hn
  rw [← h_eq] at hn
  by_contra! h_lt
  exact hn.not_ge (pullCount_mono _ h_lt _)

lemma pullCount_pos_of_time_ge [Nonempty (Fin K)]
    (h : IsAlgEnvSeqUntil A R (roundRobinAlgorithm hK) (stationaryEnv ν) P (K - 1)) :
    ∀ᵐ ω ∂P, ∀ n, K ≤ n → ∀ b : Fin K, 0 < pullCount A b n ω := by
  have h_ae a := pullCount_eq_one h a
  simp_rw [Filter.EventuallyEq, ← ae_all_iff] at h_ae
  filter_upwards [h_ae] with ω hω n hn a
  refine Nat.one_pos.trans_le ?_
  rw [← hω a]
  exact pullCount_mono _ hn _

lemma pullCount_pos_of_pullCount_gt_one [Nonempty (Fin K)]
    (h : IsAlgEnvSeqUntil A R (roundRobinAlgorithm hK) (stationaryEnv ν) P (K - 1)) (a : Fin K) :
    ∀ᵐ ω ∂P, ∀ n, 1 < pullCount A a n ω → ∀ b : Fin K, 0 < pullCount A b n ω := by
  filter_upwards [time_gt_of_pullCount_gt_one h a, pullCount_pos_of_time_ge h] with ω h1 h2 n h_gt a
  exact h2 n (h1 n h_gt).le a

end RoundRobin

end Bandits
