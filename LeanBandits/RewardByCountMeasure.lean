/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.Bandit
import LeanBandits.Regret

/-! # Laws of `stepsUntil` and `rewardByCount`
-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Bandits

variable {α : Type*} {mα : MeasurableSpace α} [DecidableEq α] [MeasurableSingletonClass α]

@[fun_prop]
lemma measurable_pullCount (a : α) (t : ℕ) : Measurable (fun k ↦ pullCount k a t) := by
  simp_rw [pullCount_eq_sum]
  have h_meas s : Measurable (fun k : ℕ → α ↦ if k s = a then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_stepsUntil (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν]
    (a : α) (m : ℕ) :
    Measurable (fun k ↦ stepsUntil k a m) := by
  sorry

lemma measurable_stepsUntil'' (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν]
    (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × ℝ) ↦ stepsUntil (arm · ω) a m) :=
  (measurable_stepsUntil alg ν a m).comp (by fun_prop)

lemma measurable_stepsUntil' (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν]
    (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ stepsUntil (arm · ω.1) a m) :=
  (measurable_stepsUntil'' alg ν a m).comp measurable_fst

lemma measurable_toNat : Measurable (fun n : ℕ∞ ↦ n.toNat) :=
  measurable_to_countable fun _ ↦ by simp

omit [DecidableEq α] [MeasurableSingletonClass α] in
@[fun_prop]
lemma _root_.Measurable.toNat {f : α → ℕ∞} (hf : Measurable f) : Measurable (fun a ↦ (f a).toNat) :=
  measurable_toNat.comp hf

@[fun_prop]
lemma measurable_rewardByCount (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν]
    (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ rewardByCount a m ω.1 ω.2) := by
  simp_rw [rewardByCount_eq_ite]
  refine Measurable.ite ?_ ?_ ?_
  · exact (measurableSet_singleton _).preimage <| measurable_stepsUntil' alg ν a m
  · fun_prop
  · change Measurable ((fun p : ℕ × (ℕ → α × ℝ) ↦ reward p.1 p.2)
      ∘ (fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ ((stepsUntil (arm · ω.1) a m).toNat, ω.1)))
    have : Measurable fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦
        ((stepsUntil (arm · ω.1) a m).toNat, ω.1) :=
      (measurable_stepsUntil' alg ν a m).toNat.prodMk (by fun_prop)
    exact Measurable.comp (by fun_prop) this

/-- The reward received at the `m`-th pull of arm `a` has law `ν a`. -/
lemma hasLaw_rewardByCount (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν]
    (a : α) (m : ℕ) :
    HasLaw (fun ω ↦ rewardByCount a m ω.1 ω.2) (ν a) (Bandit.measure alg ν) where
  aemeasurable := (measurable_rewardByCount alg ν a m).aemeasurable
  map_eq := by
    sorry

lemma iIndepFun_rewardByCount (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν] :
    iIndepFun (fun (p : α × ℕ) ω ↦ rewardByCount p.1 p.2 ω.1 ω.2) (Bandit.measure alg ν) := by
  sorry

lemma identDistrib_rewardByCount (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν]
    (a : α) (n m : ℕ) :
    IdentDistrib (fun ω ↦ rewardByCount a n ω.1 ω.2) (fun ω ↦ rewardByCount a m ω.1 ω.2)
      (Bandit.measure alg ν) (Bandit.measure alg ν) where
  aemeasurable_fst := (measurable_rewardByCount alg ν a n).aemeasurable
  aemeasurable_snd := (measurable_rewardByCount alg ν a m).aemeasurable
  map_eq := by
    sorry

end Bandits
