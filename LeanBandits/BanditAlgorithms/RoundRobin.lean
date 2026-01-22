/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.Bandit.SumRewards
import LeanBandits.BanditAlgorithms.AuxSums
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.SequentialLearning.Deterministic

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
def RoundRobin.nextArm (hK : 0 < K) (n : ℕ) (_h : Iic n → Fin K × ℝ) : Fin K :=
  ⟨(n + 1) % K, Nat.mod_lt _ hK⟩ -- for `n = 0` we have pulled arm 0 already, and we pull arm 1

/-- The next arm pulled by Round-Robin is chosen in a measurable way. -/
@[fun_prop]
lemma RoundRobin.measurable_nextArm (hK : 0 < K) (n : ℕ) : Measurable (nextArm hK n) := by
  unfold nextArm
  fun_prop

/-- The Round-Robin algorithm: deterministic algorithm that chooses the next arm according
to `RoundRobin.nextArm`. -/
noncomputable
def roundRobinAlgorithm (hK : 0 < K) : Algorithm (Fin K) ℝ :=
  detAlgorithm (RoundRobin.nextArm hK) (by fun_prop) ⟨0, hK⟩

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
    A (n + 1) =ᵐ[P] fun ω ↦ nextArm hK n (IsAlgEnvSeq.hist A R n ω) :=
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
    (h : IsAlgEnvSeqUntil A R (roundRobinAlgorithm hK) (stationaryEnv ν) P (K * m)) (a : Fin K) :
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

end RoundRobin

end Bandits
