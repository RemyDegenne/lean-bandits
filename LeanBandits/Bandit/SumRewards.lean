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

lemma measurable_sum_range_of_le {α : Type*} {mα : MeasurableSpace α}
    {f : ℕ → α → ℝ} {g : α → ℕ} {n : ℕ} (hg_le : ∀ a, g a ≤ n) (hf : ∀ i, Measurable (f i))
    (hg : Measurable g) :
    Measurable (fun a ↦ ∑ i ∈ range (g a), f i a) := by
  have h_eq : (fun a ↦ ∑ i ∈ range (g a), f i a)
      = fun a ↦ ∑ i ∈ range (n + 1), if g a = i then ∑ j ∈ range i, f j a else 0 := by
    ext ω
    rw [sum_ite_eq_of_mem]
    grind
  rw [h_eq]
  refine measurable_sum _ fun n hn ↦ ?_
  refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
  exact (measurableSet_singleton _).preimage (by fun_prop)

lemma measurable_sum_Icc_of_le {α : Type*} {mα : MeasurableSpace α}
    {f : ℕ → α → ℝ} {g : α → ℕ} {n : ℕ} (hg_le : ∀ a, g a ≤ n) (hf : ∀ i, Measurable (f i))
    (hg : Measurable g) :
    Measurable (fun a ↦ ∑ i ∈ Icc 1 (g a), f i a) := by
  have h_eq : (fun a ↦ ∑ i ∈ Icc 1 (g a), f i a)
      = fun a ↦ ∑ i ∈ range (n + 1), if g a = i then ∑ j ∈ Icc 1 i, f j a else 0 := by
    ext ω
    rw [sum_ite_eq_of_mem]
    grind
  rw [h_eq]
  refine measurable_sum _ fun n hn ↦ ?_
  refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
  exact (measurableSet_singleton _).preimage (by fun_prop)

namespace Bandits

namespace ArrayModel

variable {α : Type*} {mα : MeasurableSpace α} [DecidableEq α] [StandardBorelSpace α] [Nonempty α]
  {alg : Algorithm α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]

local notation "A" => action alg
local notation "R" => reward alg
local notation "𝔓" => arrayMeasure ν

lemma identDistrib_pullCount_prod_sum_Icc_rewardByCount' [Countable α] (n : ℕ) :
    IdentDistrib (fun ω a ↦ (pullCount A a n ω.1,
        ∑ i ∈ Icc 1 (pullCount A a n ω.1), rewardByCount A R a i ω))
      (fun ω a ↦ (pullCount A a n ω, ∑ i ∈ Icc 1 (pullCount A a n ω), ω.2 (i - 1) a))
      ((𝔓).prod (Bandit.streamMeasure ν)) 𝔓 where
  aemeasurable_fst := by
    refine Measurable.aemeasurable ?_
    rw [measurable_pi_iff]
    refine fun a ↦ Measurable.prod (by fun_prop) ?_
    exact measurable_sum_Icc_of_le (n := n) (pullCount_le _ _) (by fun_prop) (by fun_prop)
  aemeasurable_snd := by
    refine Measurable.aemeasurable ?_
    rw [measurable_pi_iff]
    refine fun a ↦ Measurable.prod (by fun_prop) ?_
    exact measurable_sum_Icc_of_le (n := n) (pullCount_le _ _) (by fun_prop) (by fun_prop)
  map_eq := by
    by_cases hn : n = 0
    · simp [hn]
    have h_eq (a : α) (i : ℕ) (ω : probSpace α ℝ × (ℕ → α → ℝ))
        (hi : i ∈ Icc 1 (pullCount A a n ω.1)) :
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
    have h_sum_eq (a : α) (ω : probSpace α ℝ × (ℕ → α → ℝ)) :
        ∑ i ∈ Icc 1 (pullCount A a n ω.1), rewardByCount A R a i ω =
        ∑ i ∈ Icc 1 (pullCount A a n ω.1), ω.1.2 (i - 1) a :=
      Finset.sum_congr rfl fun i hi ↦ h_eq a i ω hi
    simp_rw [h_sum_eq]
    conv_rhs => rw [← Measure.fst_prod (μ := 𝔓) (ν := Bandit.streamMeasure ν),
      Measure.fst]
    rw [AEMeasurable.map_map_of_aemeasurable _ (by fun_prop)]
    · rfl
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
    refine Measurable.aemeasurable ?_
    rw [measurable_pi_iff]
    refine fun a ↦ Measurable.prod (by fun_prop) ?_
    exact measurable_sum_Icc_of_le (n := n) (pullCount_le _ _) (by fun_prop) (by fun_prop)

lemma identDistrib_pullCount_prod_sum_Icc_rewardByCount [Countable α] (n : ℕ) :
    IdentDistrib (fun ω a ↦ (pullCount A a n ω.1,
        ∑ i ∈ Icc 1 (pullCount A a n ω.1), rewardByCount A R a i ω))
      (fun ω a ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a))
      ((𝔓).prod (Bandit.streamMeasure ν)) 𝔓 := by
  convert identDistrib_pullCount_prod_sum_Icc_rewardByCount' n using 2 with ω
  rotate_left
  · infer_instance
  · infer_instance
  ext a : 1
  congr 1
  sorry

lemma identDistrib_pullCount_prod_sumRewards [Countable α] (n : ℕ) :
    IdentDistrib (fun ω a ↦ (pullCount A a n ω, sumRewards A R a n ω))
      (fun ω a ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a)) 𝔓 𝔓 := by
  suffices IdentDistrib (fun ω a ↦ (pullCount A a n ω.1, sumRewards A R a n ω.1))
      (fun ω a ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a))
      ((𝔓).prod (Bandit.streamMeasure ν)) 𝔓 by
    sorry
  simp_rw [← sum_rewardByCount_eq_sumRewards]
  exact identDistrib_pullCount_prod_sum_Icc_rewardByCount n

lemma identDistrib_pullCount_prod_sumRewards_arm [Countable α] (a : α) (n : ℕ) :
    IdentDistrib (fun ω ↦ (pullCount A a n ω, sumRewards A R a n ω))
      (fun ω ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a)) 𝔓 𝔓 := by
  have h1 : (fun ω ↦ (pullCount A a n ω, sumRewards A R a n ω)) =
    (fun p ↦ p a) ∘ (fun ω a ↦ (pullCount A a n ω, sumRewards A R a n ω)) := rfl
  have h2 : (fun ω ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a)) =
      (fun p ↦ p a) ∘
        (fun ω a ↦ (pullCount A a n ω, ∑ i ∈ range (pullCount A a n ω), ω.2 i a)) := rfl
  rw [h1, h2]
  refine (identDistrib_pullCount_prod_sumRewards n).comp ?_
  fun_prop

lemma identDistrib_sumRewards [Countable α] (n : ℕ) :
    IdentDistrib (fun ω a ↦ sumRewards A R a n ω)
      (fun ω a ↦ ∑ i ∈ range (pullCount A a n ω), ω.2 i a) 𝔓 𝔓 := by
  have h_ident := identDistrib_pullCount_prod_sumRewards (ν := ν) (alg := alg) n
  exact h_ident.comp (u := fun p a ↦ (p a).2) (by fun_prop)

lemma identDistrib_sumRewards_arm [Countable α] (a : α) (n : ℕ) :
    IdentDistrib (sumRewards A R a n)
      (fun ω ↦ ∑ i ∈ range (pullCount A a n ω), ω.2 i a) 𝔓 𝔓 := by
  have h1 : sumRewards A R a n = (fun p ↦ p a) ∘ (fun ω a ↦ sumRewards A R a n ω) := rfl
  have h2 : (fun ω ↦ ∑ i ∈ range (pullCount A a n ω), ω.2 i a) =
      (fun p ↦ p a) ∘ (fun ω a ↦ ∑ i ∈ range (pullCount A a n ω), ω.2 i a) := rfl
  rw [h1, h2]
  refine (identDistrib_sumRewards n).comp ?_
  fun_prop

lemma todo'' [Countable α] (a : α) (n : ℕ)
    {s : Set ℕ} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) {B : Set ℝ} (hB : MeasurableSet B) :
    𝔓 {ω | pullCount A a n ω ∈ s ∧ sumRewards A R a n ω ∈ B} ≤
      ∑ k ∈ (range (n + 1)).filter (· ∈ s),
        Bandit.streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ B} := by
  have h_ident := identDistrib_pullCount_prod_sumRewards_arm a n (ν := ν) (alg := alg)
  have : 𝔓 {ω | pullCount A a n ω ∈ s ∧ sumRewards A R a n ω ∈ B} =
      (𝔓).map (fun ω ↦ (pullCount A a n ω, sumRewards A R a n ω)) (s ×ˢ B) := by
    rw [Measure.map_apply (by fun_prop) (hs.prod hB), Set.mk_preimage_prod]
    rfl
  rw [this, h_ident.map_eq, Measure.map_apply ?_ (hs.prod hB)]
  swap
  · refine Measurable.prod (by fun_prop) ?_
    exact measurable_sum_range_of_le (n := n) (pullCount_le _ _) (by fun_prop) (by fun_prop)
  rw [Set.mk_preimage_prod]
  calc 𝔓 {ω | pullCount A a n ω ∈ s ∧ ∑ i ∈ range (pullCount A a n ω), ω.2 i a ∈ B}
  _ ≤ 𝔓 {ω | ∃ k ≤ n, k ∈ s ∧ ∑ i ∈ range k, ω.2 i a ∈ B} := by
    refine measure_mono fun ω hω ↦ ?_
    simp only [Set.mem_setOf_eq] at hω ⊢
    exact ⟨pullCount A a n ω, pullCount_le _ _ _, hω⟩
  _ = 𝔓 (⋃ k ∈ (range (n + 1)).filter (· ∈ s), {ω | ∑ i ∈ range k, ω.2 i a ∈ B}) := by
    congr 1
    ext ω
    simp
    grind
  _ ≤ ∑ k ∈ (range (n + 1)).filter (· ∈ s), 𝔓 {ω | ∑ i ∈ range k, ω.2 i a ∈ B} :=
    measure_biUnion_finset_le _ _
  _ = ∑ k ∈ (range (n + 1)).filter (· ∈ s),
      (Bandit.streamMeasure ν) {ω | ∑ i ∈ range k, ω i a ∈ B} := by
    congr with k
    sorry

end ArrayModel

variable {α Ω Ω' : Type*} [DecidableEq α] {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω}
  {mΩ' : MeasurableSpace Ω'}
  {P : Measure Ω} [IsProbabilityMeasure P] {P' : Measure Ω'} [IsProbabilityMeasure P']
  {alg : Algorithm α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]
  {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {A₂ : ℕ → Ω' → α} {R₂ : ℕ → Ω' → ℝ}
  {ω : Ω} {m n t : ℕ} {a : α}

variable [StandardBorelSpace α] [Nonempty α]

omit [Nonempty α] in
lemma sumRewards_eq_comp :
    sumRewards A R a n =
     (fun p ↦ ∑ i ∈ range n, if (p i).1 = a then (p i).2 else 0) ∘ (fun ω n ↦ (A n ω, R n ω)) := by
  ext
  simp [sumRewards]

omit [Nonempty α] in
lemma pullCount_eq_comp :
    pullCount A a n =
      (fun p ↦ ∑ i ∈ range n, if (p i).1 = a then 1 else 0) ∘ (fun ω n ↦ (A n ω, R n ω)) := by
  ext
  simp [pullCount]

lemma _root_.Learning.IsAlgEnvSeq.law_sumRewards_unique
    (h1 : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (h2 : IsAlgEnvSeq A₂ R₂ alg (stationaryEnv ν) P') :
    P.map (sumRewards A R a n) = P'.map (sumRewards A₂ R₂ a n) := by
  have hA := h1.measurable_A
  have hR := h1.measurable_R
  have hA2 := h2.measurable_A
  have hR2 := h2.measurable_R
  have h_unique := isAlgEnvSeq_unique h1 h2
  rw [sumRewards_eq_comp, sumRewards_eq_comp, ← Measure.map_map, h_unique, Measure.map_map,
    ← sumRewards_eq_comp]
  · refine measurable_sum _ fun i hi ↦ Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  · rw [measurable_pi_iff]
    exact fun n ↦ Measurable.prodMk (hA2 n) (hR2 n)
  · refine measurable_sum _ fun i hi ↦ Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  · rw [measurable_pi_iff]
    exact fun n ↦ Measurable.prodMk (hA n) (hR n)

lemma _root_.Learning.IsAlgEnvSeq.law_pullCount_sumRewards_unique
    (h1 : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (h2 : IsAlgEnvSeq A₂ R₂ alg (stationaryEnv ν) P') :
    P.map (fun ω ↦ (pullCount A a n ω, sumRewards A R a n ω)) =
      P'.map (fun ω ↦ (pullCount A₂ a n ω, sumRewards A₂ R₂ a n ω)) := by
  have hA := h1.measurable_A
  have hR := h1.measurable_R
  have hA2 := h2.measurable_A
  have hR2 := h2.measurable_R
  have h_unique := isAlgEnvSeq_unique h1 h2
  let f := fun p : ℕ → α × ℝ ↦ (∑ i ∈ range n, if (p i).1 = a then 1 else 0,
    ∑ i ∈ range n, if (p i).1 = a then (p i).2 else 0)
  have hf : Measurable f := by
    refine Measurable.prod ?_ ?_
    · simp only [f]
      refine measurable_sum _ fun i hi ↦ Measurable.ite ?_ (by fun_prop) (by fun_prop)
      exact (measurableSet_singleton _).preimage (by fun_prop)
    · simp only [f]
      refine measurable_sum _ fun i hi ↦ Measurable.ite ?_ (by fun_prop) (by fun_prop)
      exact (measurableSet_singleton _).preimage (by fun_prop)
  have h_eq_comp : (fun ω ↦ (pullCount A a n ω, sumRewards A R a n ω))
      = f ∘ (fun ω n ↦ (A n ω, R n ω)) := by
    ext ω : 1
    rw [pullCount_eq_comp (R := R), sumRewards_eq_comp]
    grind
  have h_eq_comp2 : (fun ω ↦ (pullCount A₂ a n ω, sumRewards A₂ R₂ a n ω))
      = f ∘ (fun ω n ↦ (A₂ n ω, R₂ n ω)) := by
    ext ω : 1
    rw [pullCount_eq_comp (R := R₂), sumRewards_eq_comp]
    grind
  rw [h_eq_comp, h_eq_comp2, ← Measure.map_map hf, h_unique, Measure.map_map hf,
    ← h_eq_comp2]
  · rw [measurable_pi_iff]
    exact fun n ↦ Measurable.prodMk (hA2 n) (hR2 n)
  · rw [measurable_pi_iff]
    exact fun n ↦ Measurable.prodMk (hA n) (hR n)

lemma todo2 [Countable α] (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {s : Set ℕ} [DecidablePred (· ∈ s)] (hs : MeasurableSet s) {B : Set ℝ} (hB : MeasurableSet B) :
    P {ω | pullCount A a n ω ∈ s ∧ sumRewards A R a n ω ∈ B} ≤
      ∑ k ∈ (range (n + 1)).filter (· ∈ s),
        Bandit.streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ B} := by
  have hA := h.measurable_A
  have hR := h.measurable_R
  calc P {ω | pullCount A a n ω ∈ s ∧ sumRewards A R a n ω ∈ B}
  _ = (P.map (fun ω ↦ (pullCount A a n ω, sumRewards A R a n ω))) (s ×ˢ B) := by
      rw [Measure.map_apply (by fun_prop) (hs.prod hB)]; rfl
  _ = ((ArrayModel.arrayMeasure ν).map
      (fun ω ↦ (pullCount (ArrayModel.action alg) a n ω,
        sumRewards (ArrayModel.action alg) (ArrayModel.reward alg) a n ω))) (s ×ˢ B) := by
    rw [h.law_pullCount_sumRewards_unique (ArrayModel.isAlgEnvSeq_arrayMeasure alg ν)]
  _ = (ArrayModel.arrayMeasure ν) {ω | pullCount (ArrayModel.action alg) a n ω ∈ s ∧
      sumRewards (ArrayModel.action alg) (ArrayModel.reward alg) a n ω ∈ B} := by
    rw [Measure.map_apply (by fun_prop) (hs.prod hB)]; rfl
  _ ≤ ∑ k ∈ (range (n + 1)).filter (· ∈ s), Bandit.streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ B} :=
    ArrayModel.todo'' a n hs hB

lemma todo [Countable α] (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    {B : Set ℝ} (hB : MeasurableSet B) :
    P (sumRewards A R a n ⁻¹' B) ≤
      ∑ k ∈ range (n + 1), Bandit.streamMeasure ν {ω | ∑ i ∈ range k, ω i a ∈ B} := by
  classical
  have h_le := todo2 h .univ hB (a := a) (n := n)
  simpa using h_le

end Bandits
