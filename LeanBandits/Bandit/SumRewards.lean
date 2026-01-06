/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.Bandit.Regret

/-! # Law of the sum of rewards
-/

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal NNReal

namespace Bandits

namespace ArrayModel

variable {α : Type*} {mα : MeasurableSpace α} [DecidableEq α] [StandardBorelSpace α] [Nonempty α]
  {alg : Algorithm α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]

local notation "A" => action alg
local notation "R" => reward alg

lemma identDistrib_sum_Icc_rewardByCount_pullCount' [Countable α] (a : α) (n : ℕ) :
    IdentDistrib (fun ω ↦ ∑ i ∈ Icc 1 (pullCount A a n ω.1), rewardByCount A R a i ω)
      (fun ω ↦ ∑ i ∈ Icc 1 (pullCount A a n ω), ω.2 (i - 1) a)
      ((arrayMeasure ν).prod (Bandit.streamMeasure ν)) (arrayMeasure ν) where
  aemeasurable_fst := sorry -- the issue is the random bound
  aemeasurable_snd := sorry
  map_eq := by
    by_cases hn : n = 0
    · simp [hn]
    have h_eq (i : ℕ) (ω : probSpace α ℝ × (ℕ → α → ℝ)) (hi : i ∈ Icc 1 (pullCount A a n ω.1)) :
        rewardByCount A R a i ω = ω.1.2 (i - 1) a := by
      rw [rewardByCount_of_stepsUntil_ne_top]
      · simp only [reward_eq]
        have h_exists : ∃ s, pullCount A a (s + 1) ω.1 = i :=
          exists_pullCount_eq_of_le (n := n - 1) (by grind) (by grind)
        have h_action : A (stepsUntil A a i ω.1).toNat ω.1 = a :=
          action_stepsUntil («A» := A) (by grind) h_exists
        congr!
        rw [h_action, pullCount_stepsUntil (by grind) h_exists]
      · have : stepsUntil A a (pullCount A a (n + 1) ω.1) ω.1 ≠ ⊤ := by
          refine ne_top_of_le_ne_top ?_ (stepsUntil_pullCount_le _ _ _)
          simp
        refine ne_top_of_le_ne_top this ?_
        refine stepsUntil_mono a ω.1 (by grind) ?_
        simp only [mem_Icc] at hi
        refine hi.2.trans ?_
        exact pullCount_mono _ (by grind) _
    have h_sum_eq (ω : probSpace α ℝ × (ℕ → α → ℝ)) :
        ∑ i ∈ Icc 1 (pullCount A a n ω.1), rewardByCount A R a i ω =
        ∑ i ∈ Icc 1 (pullCount A a n ω.1), ω.1.2 (i - 1) a :=
      Finset.sum_congr rfl fun i hi ↦ h_eq i ω hi
    simp_rw [h_sum_eq]
    conv_rhs => rw [← Measure.fst_prod (μ := arrayMeasure ν) (ν := Bandit.streamMeasure ν),
      Measure.fst]
    rw [AEMeasurable.map_map_of_aemeasurable _ (by fun_prop)]
    · rfl
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
    sorry

lemma identDistrib_sum_Icc_rewardByCount_pullCount [Countable α] (a : α) (n : ℕ) :
    IdentDistrib (fun ω ↦ ∑ i ∈ Icc 1 (pullCount A a n ω.1), rewardByCount A R a i ω)
      (fun ω ↦ ∑ i ∈ range (pullCount A a n ω), ω.2 i a)
      ((arrayMeasure ν).prod (Bandit.streamMeasure ν)) (arrayMeasure ν) := by
  convert identDistrib_sum_Icc_rewardByCount_pullCount' a n using 2 with ω
  swap; · infer_instance
  sorry

lemma identDistrib_sumRewards_pullCount [Countable α] (a : α) (n : ℕ) :
    IdentDistrib (sumRewards A R a n) (fun ω ↦ ∑ i ∈ range (pullCount A a n ω), ω.2 i a)
      (arrayMeasure ν) (arrayMeasure ν) := by
  suffices IdentDistrib (fun ω ↦ sumRewards A R a n ω.1)
      (fun ω ↦ ∑ i ∈ range (pullCount A a n ω), ω.2 i a)
      ((arrayMeasure ν).prod (Bandit.streamMeasure ν)) (arrayMeasure ν) by
    sorry
  simp_rw [← sum_rewardByCount_eq_sumRewards]
  exact identDistrib_sum_Icc_rewardByCount_pullCount a n

end ArrayModel

end Bandits
