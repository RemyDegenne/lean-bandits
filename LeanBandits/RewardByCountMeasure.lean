/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.Bandit.Bandit
import LeanBandits.Bandit.Regret
import LeanBandits.ForMathlib.IdentDistrib
import LeanBandits.ForMathlib.IndepFun

/-! # Laws of `stepsUntil` and `rewardByCount`
-/

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal NNReal

namespace Bandits

variable {α : Type*} {mα : MeasurableSpace α} [DecidableEq α] [MeasurableSingletonClass α]

@[fun_prop]
lemma measurable_pullCount (a : α) (t : ℕ) : Measurable (fun h ↦ pullCount a t h) := by
  simp_rw [pullCount_eq_sum]
  have h_meas s : Measurable (fun h : ℕ → α × ℝ ↦ if arm s h = a then 1 else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

lemma integrable_pullCount {alg : Algorithm α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]
    (a : α) (n : ℕ) :
    Integrable (fun ω ↦ (pullCount a n ω : ℝ)) (Bandit.trajMeasure alg ν) := by
  refine integrable_of_le_of_le (g₁ := 0) (g₂ := fun _ ↦ n) (by fun_prop)
    (ae_of_all _ fun ω ↦ by simp) (ae_of_all _ fun ω ↦ ?_) (integrable_const _) (integrable_const _)
  simp only [Nat.cast_le]
  exact pullCount_le a n ω

@[fun_prop]
lemma measurable_sumRewards (a : α) (t : ℕ) : Measurable (sumRewards a t) := by
  unfold sumRewards
  have h_meas s : Measurable (fun h : ℕ → α × ℝ ↦ if arm s h = a then reward s h else 0) := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    exact (measurableSet_singleton _).preimage (by fun_prop)
  fun_prop

@[fun_prop]
lemma measurable_stepsUntil (a : α) (m : ℕ) : Measurable (fun h ↦ stepsUntil a m h) := by
  classical
  have h_union : {h' | ∃ s, pullCount a (s + 1) h' = m}
      = ⋃ s : ℕ, {h' | pullCount a (s + 1) h' = m} := by ext; simp
  have h_meas_set : MeasurableSet {h' | ∃ s, pullCount a (s + 1) h' = m} := by
    rw [h_union]
    exact MeasurableSet.iUnion fun s ↦ (measurableSet_singleton _).preimage (by fun_prop)
  simp_rw [stepsUntil_eq_dite]
  suffices Measurable fun k ↦ if h : k ∈ {k' | ∃ s, pullCount a (s + 1) k' = m}
      then (Nat.find h : ℕ∞) else ⊤ by convert this
  refine Measurable.dite (s := {k' : ℕ → α × ℝ | ∃ s, pullCount a (s + 1) k' = m})
    (f := fun x ↦ (Nat.find x.2 : ℕ∞)) (g := fun _ ↦ ⊤) ?_ (by fun_prop) h_meas_set
  refine Measurable.coe_nat_enat ?_
  refine measurable_find _ fun k ↦ ?_
  suffices MeasurableSet {x : ℕ → α × ℝ | pullCount a (k + 1) x = m} by
    have : Subtype.val ''
          {x : {k' : ℕ → α × ℝ | ∃ s, pullCount a (s + 1) k' = m} | pullCount a (k + 1) x = m}
        = {x : ℕ → α × ℝ | pullCount a (k + 1) x = m} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.coe_setOf, Set.mem_image, Subtype.exists, exists_and_left,
        exists_prop, exists_eq_right_right, and_iff_left_iff_imp]
      exact fun h ↦ ⟨_, h⟩
    refine (MeasurableEmbedding.subtype_coe h_meas_set).measurableSet_image.mp ?_
    rw [this]
    exact (measurableSet_singleton _).preimage (by fun_prop)
  exact (measurableSet_singleton _).preimage (by fun_prop)

lemma measurable_stepsUntil' (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ stepsUntil a m ω.1) :=
  (measurable_stepsUntil a m).comp measurable_fst

@[fun_prop]
lemma measurable_rewardByCount (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ rewardByCount a m ω) := by
  simp_rw [rewardByCount_eq_ite]
  refine Measurable.ite ?_ ?_ ?_
  · exact (measurableSet_singleton _).preimage <| measurable_stepsUntil' a m
  · fun_prop
  · change Measurable ((fun p : ℕ × (ℕ → α × ℝ) ↦ reward p.1 p.2)
      ∘ (fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ ((stepsUntil a m ω.1).toNat, ω.1)))
    have : Measurable fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ ((stepsUntil a m ω.1).toNat, ω.1) :=
      (measurable_stepsUntil' a m).toNat.prodMk (by fun_prop)
    exact Measurable.comp (by fun_prop) this

variable {alg : Algorithm α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]

omit [DecidableEq α] [MeasurableSingletonClass α] in
lemma hasLaw_Z (a : α) (m : ℕ) :
  HasLaw (fun ω ↦ ω.2 m a) (ν a) (Bandit.measure alg ν) where
  map_eq := by
    calc ((Bandit.trajMeasure alg ν).prod (Bandit.streamMeasure ν)).map (fun ω ↦ ω.2 m a)
    _ = (((Bandit.trajMeasure alg ν).prod (Bandit.streamMeasure ν)).map (fun ω ↦ ω.2)).map
        (fun ω ↦ ω m a) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (Bandit.streamMeasure ν).map (fun ω ↦ ω m a) := by simp [Measure.map_snd_prod]
    _ = ((Measure.infinitePi fun _ ↦ Measure.infinitePi ν).map (fun ω ↦ ω m)).map
        (fun ω ↦ ω a) := by
      rw [Bandit.streamMeasure, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = ν a := by simp_rw [(measurePreserving_eval_infinitePi _ _).map_eq]

/-- Law of `Y` conditioned on the event `s`.-/
notation "𝓛[" Y " | " s "; " μ "]" => Measure.map Y (μ[|s])
/-- Law of `Y` conditioned on the event that `X` is in `s`. -/
notation "𝓛[" Y " | " X " in " s "; " μ "]" => Measure.map Y (μ[|X ⁻¹' s])
/-- Law of `Y` conditioned on the event that `X` equals `x`. -/
notation "𝓛[" Y " | " X " ← " x "; " μ "]" => Measure.map Y (μ[|X ⁻¹' {x}])

omit [DecidableEq α] [MeasurableSingletonClass α] in
lemma condDistrib_reward'' [StandardBorelSpace α] [Nonempty α] (n : ℕ) :
    𝓛[fun ω ↦ reward n ω.1 | fun ω ↦ arm n ω.1; Bandit.measure alg ν]
      =ᵐ[(Bandit.measure alg ν).map (fun ω ↦ arm n ω.1)] ν := by
  let μ := Bandit.measure alg ν
  have h_ra' : 𝓛[reward n | arm n; Bandit.trajMeasure alg ν]
      =ᵐ[(Bandit.trajMeasure alg ν).map (arm n)] ν := condDistrib_reward alg ν n
  have h_law : μ.map (fun ω ↦ arm n ω.1) = (Bandit.trajMeasure alg ν).map (arm n) := by
    calc μ.map (fun ω ↦ arm n ω.1)
    _ = (μ.map (fun ω ↦ ω.1)).map (fun ω ↦ arm n ω) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = _ := by unfold μ Bandit.measure; simp [Measure.map_fst_prod]
  rw [h_law]
  have h_prod : 𝓛[fun ω ↦ reward n ω.1 | fun ω ↦ arm n ω.1; μ]
      =ᵐ[(Bandit.trajMeasure alg ν).map (arm n)] 𝓛[reward n | arm n; Bandit.trajMeasure alg ν] :=
    condDistrib_fst_prod _ (by fun_prop) _
  filter_upwards [h_ra', h_prod] with ω h_eq h_prod
  rw [h_prod, h_eq]

omit [DecidableEq α] in
lemma reward_cond_arm [StandardBorelSpace α] [Nonempty α] [Countable α] (a : α) (n : ℕ)
    (hμa : (Bandit.measure alg ν).map (fun ω ↦ arm n ω.1) {a} ≠ 0) :
    𝓛[fun ω ↦ reward n ω.1 | fun ω ↦ arm n ω.1 ← a; Bandit.measure alg ν] = ν a := by
  let μ := Bandit.measure alg ν
  have h_ra : 𝓛[fun ω ↦ reward n ω.1 | fun ω ↦ arm n ω.1; μ] =ᵐ[μ.map (fun ω ↦ arm n ω.1)] ν :=
    condDistrib_reward'' n
  have h_eq := condDistrib_ae_eq_cond (μ := μ)
    (X := fun ω ↦ arm n ω.1) (Y := fun ω ↦ reward n ω.1) (by fun_prop) (by fun_prop)
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h_ra h_eq
  specialize h_ra a hμa
  specialize h_eq a hμa
  rw [h_ra] at h_eq
  exact h_eq.symm

-- after the Mathlib stopping time refactor, we will be able to prove that stepsUntil is a
-- stopping time
lemma measurable_comap_indicator_stepsUntil_eq (a : α) (m n : ℕ) :
    Measurable[MeasurableSpace.comap (fun ω : ℕ → α × ℝ ↦ (hist (n-1) ω, arm n ω)) inferInstance]
      ({ω | stepsUntil a m ω = ↑n}.indicator fun _ ↦ 1) := by
  let k : ((Iic (n - 1) → α × ℝ) × α) → (ℕ → α × ℝ) := fun x i ↦
    if hi : i ∈ Iic (n - 1) then (x.1 ⟨i, hi⟩) else if i = n then (x.2, 0) else (a, 0)
  have hk : Measurable k := by
    unfold k
    rw [measurable_pi_iff]
    intro i
    split_ifs <;> fun_prop
  let φ : ((Iic (n - 1) → α × ℝ) × α) → ℕ := fun x ↦ if stepsUntil a m (k x) = ↑n then 1 else 0
  have hφ : Measurable φ :=
    Measurable.ite ((measurableSet_singleton _).preimage (by fun_prop)) (by fun_prop) (by fun_prop)
  suffices {ω | stepsUntil a m ω = ↑n}.indicator (fun x ↦ 1)
      = φ ∘ fun ω ↦ (hist (n - 1) ω, arm n ω) from this ▸ measurable_comp_comap _ hφ
  ext ω
  classical
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Function.comp_apply, φ]
  congr 1
  rw [stepsUntil_eq_congr]
  intro i hin
  simp only [arm, mem_Iic, hist, dite_eq_ite, k]
  grind

lemma measurable_indicator_stepsUntil_eq (a : α) (m n : ℕ) :
    Measurable ({ω | stepsUntil a m ω = ↑n}.indicator fun _ ↦ 1) := by
  refine (measurable_comap_indicator_stepsUntil_eq a m n).mono ?_ le_rfl
  refine Measurable.comap_le ?_
  fun_prop

lemma measurableSet_stepsUntil_eq (a : α) (m n : ℕ) :
    MeasurableSet[MeasurableSpace.comap (fun ω : ℕ → α × ℝ ↦ (hist (n-1) ω, arm n ω)) inferInstance]
      {ω : ℕ → α × ℝ | stepsUntil a m ω = ↑n} := by
  let mProd := MeasurableSpace.comap (fun ω : ℕ → α × ℝ ↦ (hist (n-1) ω, arm n ω)) inferInstance
  suffices Measurable[mProd] ({ω | stepsUntil a m ω = ↑n}.indicator fun x ↦ 1) by
    rwa [measurable_indicator_const_iff] at this
  exact measurable_comap_indicator_stepsUntil_eq a m n

lemma condIndepFun_reward_stepsUntil_arm' [StandardBorelSpace α] [Countable α] [Nonempty α]
    (a : α) (m n : ℕ) (hm : m ≠ 0) :
    CondIndepFun (mα.comap (arm n)) (measurable_arm n).comap_le
      (reward n) ({ω | stepsUntil a m ω = ↑n}.indicator (fun _ ↦ 1))
      (Bandit.trajMeasure alg ν) := by
  -- the indicator of `stepsUntil ... = n` is a function of
  -- `hist (n-1)` and `arm n`.
  -- It thus suffices to prove the independence of `reward n` and `hist (n-1)` conditionally
  -- on `arm n`.
  by_cases hn : n = 0
  · simp only [hn, CharP.cast_eq_zero]
    simp only [stepsUntil_eq_zero_iff, hm, ne_eq, false_and, false_or]
    by_cases hm1 : m = 1
    · simp only [hm1, true_and]
      have h_indep := condIndepFun_self_right (X := reward 0) (Z := arm 0)
        (mβ := inferInstance) (mβ' := inferInstance) (μ := Bandit.trajMeasure alg ν)
        (by fun_prop) (by fun_prop)
      have : {ω : ℕ → α × ℝ | arm 0 ω = a}.indicator (fun x ↦ 1)
          = {b | b = a}.indicator (fun _ ↦ 1) ∘ arm 0 := by ext; simp [Set.indicator]
      rw [this]
      exact h_indep.comp measurable_id (by fun_prop)
    · simp only [hm1, false_and, Set.setOf_false, Set.indicator_empty]
      exact condIndepFun_const_right (reward 0) 0
  have h_indep : CondIndepFun (mα.comap (arm n)) (measurable_arm n).comap_le (reward n)
      (hist (n - 1)) (Bandit.trajMeasure alg ν) := by
    convert condIndepFun_reward_hist_arm (alg := alg) (ν := ν) (n - 1)
      <;> rw [Nat.sub_add_cancel (by grind)]
  have h_indep' : CondIndepFun (mα.comap (arm n)) (measurable_arm n).comap_le (reward n)
      (fun ω ↦ (hist (n - 1) ω, arm n ω)) (Bandit.trajMeasure alg ν) :=
    h_indep.prod_right (by fun_prop) (by fun_prop) (by fun_prop)
  obtain ⟨φ, hφ_meas, h_eq⟩ : ∃ φ : ((Iic (n - 1) → α × ℝ) × α) → ℕ, Measurable φ ∧
      {ω | stepsUntil a m ω = ↑n}.indicator (fun _ ↦ 1) = φ ∘ (fun ω ↦ (hist (n - 1) ω, arm n ω)) :=
    (measurable_comap_indicator_stepsUntil_eq a m n).exists_eq_measurable_comp
  rw [h_eq]
  exact h_indep'.comp measurable_id hφ_meas

lemma condIndepFun_reward_stepsUntil_arm [StandardBorelSpace α] [Countable α] [Nonempty α]
    (a : α) (m n : ℕ) (hm : m ≠ 0) :
    CondIndepFun (mα.comap (fun ω ↦ arm n ω.1)) ((measurable_arm n).comp measurable_fst).comap_le
      (fun ω ↦ reward n ω.1) ({ω | stepsUntil a m ω.1 = ↑n}.indicator (fun _ ↦ 1))
      (Bandit.measure alg ν) :=
  condIndepFun_fst_prod (ν := Bandit.streamMeasure ν)
    (measurable_indicator_stepsUntil_eq a m n) (by fun_prop) (by fun_prop)
    (condIndepFun_reward_stepsUntil_arm' a m n hm)

lemma reward_cond_stepsUntil [StandardBorelSpace α] [Countable α] [Nonempty α] (a : α) (m n : ℕ)
    (hm : m ≠ 0)
    (hμn : (Bandit.measure alg ν) ((fun ω ↦ stepsUntil a m ω.1) ⁻¹' {↑n}) ≠ 0) :
    𝓛[fun ω ↦ reward n ω.1 | fun ω ↦ stepsUntil a m ω.1 ← ↑n; Bandit.measure alg ν] = ν a := by
  let μ := Bandit.measure alg ν
  have hμna :
      μ ((fun ω ↦ stepsUntil a m ω.1) ⁻¹' {↑n} ∩ (fun ω ↦ arm n ω.1) ⁻¹' {a}) ≠ 0 := by
    suffices ((fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦
          stepsUntil a m ω.1) ⁻¹' {↑n} ∩ (fun ω ↦ arm n ω.1) ⁻¹' {a})
        = (fun ω ↦ stepsUntil a m ω.1) ⁻¹' {↑n} by simpa [this] using hμn
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact arm_eq_of_stepsUntil_eq_coe hm
  have hμa : μ.map (fun ω ↦ arm n ω.1) {a} ≠ 0 := by
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    refine fun h_zero ↦ hμn (measure_mono_null (fun ω ↦ ?_) h_zero)
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact arm_eq_of_stepsUntil_eq_coe hm
  calc 𝓛[fun ω ↦ reward n ω.1 | fun ω ↦ stepsUntil a m ω.1 ← (n : ℕ∞); μ]
  _ = (μ[|(fun ω ↦ stepsUntil a m ω.1) ⁻¹' {↑n} ∩ (fun ω ↦ arm n ω.1) ⁻¹' {a}]).map
      (fun ω ↦ reward n ω.1) := by
    congr with ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, iff_self_and]
    exact arm_eq_of_stepsUntil_eq_coe hm
  _ = (μ[|(fun ω ↦ arm n ω.1) ⁻¹' {a}
      ∩ {ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) | stepsUntil a m ω.1 = ↑n}.indicator 1 ⁻¹' {1} ]).map
      (fun ω ↦ reward n ω.1) := by
    congr 2 with ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.indicator_apply,
      Set.mem_setOf_eq, Pi.one_apply, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    rw [and_comm]
  _ = 𝓛[fun ω ↦ reward n ω.1 | fun ω ↦ arm n ω.1 ← a; μ] := by
    rw [cond_of_condIndepFun (by fun_prop)]
    · exact condIndepFun_reward_stepsUntil_arm a m n hm
    · refine measurable_one.indicator ?_
      exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
    · fun_prop
    · convert hμna using 2
      rw [Set.inter_comm]
      congr 1 with ω
      simp [Set.indicator_apply]
  _ = ν a := reward_cond_arm a n hμa

lemma condDistrib_rewardByCount_stepsUntil [Countable α] [StandardBorelSpace α] [Nonempty α]
    (a : α) (m : ℕ) (hm : m ≠ 0) :
    condDistrib (rewardByCount a m) (fun ω ↦ stepsUntil a m ω.1)
        (Bandit.measure alg ν)
      =ᵐ[(Bandit.measure alg ν).map (fun ω ↦ stepsUntil a m ω.1)] Kernel.const _ (ν a) := by
  let μ := Bandit.measure alg ν
  refine (condDistrib_ae_eq_cond (μ := μ)
    (X := fun ω ↦ stepsUntil a m ω.1) (by fun_prop) (by fun_prop)).trans ?_
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro n hn
  simp only [Kernel.const_apply]
  cases n with
  | top =>
    rw [Measure.map_congr (g := fun ω ↦ ω.2 m a)]
    swap
    · refine ae_cond_of_forall_mem ((measurableSet_singleton _).preimage (by fun_prop)) ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact fun ω ↦ rewardByCount_of_stepsUntil_eq_top
    rw [cond_of_indepFun _ (by fun_prop) (by fun_prop) (measurableSet_singleton _)]
    · exact (hasLaw_Z a m).map_eq
    · rwa [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hn
    · exact indepFun_prod (X := fun ω : ℕ → α × ℝ ↦ stepsUntil a m ω)
        (Y := fun ω : ℕ → α → ℝ ↦ ω m a) (by fun_prop) (by fun_prop)
  | coe n =>
    rw [Measure.map_congr (g := fun ω ↦ reward n ω.1)]
    swap
    · refine ae_cond_of_forall_mem ((measurableSet_singleton _).preimage (by fun_prop)) ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact fun ω ↦ rewardByCount_of_stepsUntil_eq_coe
    refine reward_cond_stepsUntil a m n hm ?_
    rwa [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hn

/-- The reward received at the `m`-th pull of arm `a` has law `ν a`. -/
lemma hasLaw_rewardByCount [Countable α] [StandardBorelSpace α] [Nonempty α]
    (a : α) (m : ℕ) (hm : m ≠ 0) :
    HasLaw (rewardByCount a m) (ν a) (Bandit.measure alg ν) where
  map_eq := by
    have h_condDistrib :
        condDistrib (rewardByCount a m) (fun ω ↦ stepsUntil a m ω.1)
          (Bandit.measure alg ν)
        =ᵐ[(Bandit.measure alg ν).map (fun ω ↦ stepsUntil a m ω.1)]
          Kernel.const _ (ν a) := condDistrib_rewardByCount_stepsUntil a m hm
    calc (Bandit.measure alg ν).map (rewardByCount a m)
    _ = (condDistrib (rewardByCount a m) (fun ω ↦ stepsUntil a m ω.1)
          (Bandit.measure alg ν))
        ∘ₘ ((Bandit.measure alg ν).map (fun ω ↦ stepsUntil a m ω.1)) := by
      rw [condDistrib_comp_map (by fun_prop) (by fun_prop)]
    _ = (Kernel.const _ (ν a))
        ∘ₘ ((Bandit.measure alg ν).map (fun ω ↦ stepsUntil a m ω.1)) :=
      Measure.comp_congr h_condDistrib
    _ = ν a := by
      have : IsProbabilityMeasure
          ((Bandit.measure alg ν).map (fun ω ↦ stepsUntil a m ω.1)) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      simp

lemma identDistrib_rewardByCount [Countable α] [StandardBorelSpace α] [Nonempty α] (a : α) (n m : ℕ)
    (hn : n ≠ 0) (hm : m ≠ 0) :
    IdentDistrib (rewardByCount a n) (rewardByCount a m)
      (Bandit.measure alg ν) (Bandit.measure alg ν) where
  aemeasurable_fst := by fun_prop
  aemeasurable_snd := by fun_prop
  map_eq := by rw [(hasLaw_rewardByCount a n hn).map_eq, (hasLaw_rewardByCount a m hm).map_eq]

lemma identDistrib_rewardByCount_id [Countable α] [StandardBorelSpace α] [Nonempty α]
    (a : α) (n : ℕ) (hn : n ≠ 0) :
    IdentDistrib (rewardByCount a n) id (Bandit.measure alg ν) (ν a) where
  aemeasurable_fst := by fun_prop
  aemeasurable_snd := Measurable.aemeasurable <| by fun_prop
  map_eq := by rw [(hasLaw_rewardByCount a n hn).map_eq, Measure.map_id]

lemma identDistrib_rewardByCount_eval [Countable α] [StandardBorelSpace α] [Nonempty α]
    (a : α) (n m : ℕ) (hn : n ≠ 0) :
    IdentDistrib (rewardByCount a n) (fun ω ↦ ω m a)
      (Bandit.measure alg ν) (Bandit.streamMeasure ν) :=
  (identDistrib_rewardByCount_id a n hn).trans (identDistrib_eval_eval_id_streamMeasure ν m a).symm

lemma indepFun_rewardByCount_Iic (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν] (a : α)
    (n : ℕ) :
    (rewardByCount a (n + 1)) ⟂ᵢ[Bandit.measure alg ν] fun ω (i : Iic n) ↦ rewardByCount a i ω := by
  sorry

lemma iIndepFun_rewardByCount' (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν] (a : α) :
    iIndepFun (rewardByCount a) (Bandit.measure alg ν) := by
  rw [iIndepFun_nat_iff_forall_indepFun (by fun_prop)]
  exact indepFun_rewardByCount_Iic alg ν a

lemma iIndepFun_rewardByCount (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν] :
    iIndepFun (fun (p : α × ℕ) ↦ rewardByCount p.1 p.2) (Bandit.measure alg ν) := by
  sorry

lemma identDistrib_rewardByCount_stream' [Countable α] [StandardBorelSpace α] [Nonempty α]
    (a : α) :
    IdentDistrib (fun ω n ↦ rewardByCount a (n + 1) ω) (fun ω n ↦ ω n a)
      (Bandit.measure alg ν) (Bandit.streamMeasure ν) := by
  refine IdentDistrib.pi (fun n ↦ ?_) ?_ ?_
  · refine identDistrib_rewardByCount_eval a (n + 1) n (by simp) (ν := ν)
  · have h_indep := iIndepFun_rewardByCount' alg ν a
    exact iIndepFun.precomp (g := fun n ↦ n + 1) (fun i j hij ↦ by grind) h_indep
  · exact iIndepFun_eval_streamMeasure'' ν a

omit [DecidableEq α] [MeasurableSingletonClass α] in
lemma identDistrib_eval_streamMeasure_measure (a : α) :
    IdentDistrib (fun ω n ↦ ω n a) (fun ω n ↦ ω.2 n a)
      (Bandit.streamMeasure ν) (Bandit.measure alg ν) := by
  refine IdentDistrib.pi (fun n ↦ ?_) ?_ ?_
  · rw [← Bandit.snd_measure alg ν, Measure.snd,
      identDistrib_map_left_iff (by fun_prop) (by fun_prop)
        (Measurable.aemeasurable <| by fun_prop)]
    exact IdentDistrib.refl (by fun_prop)
  · exact iIndepFun_eval_streamMeasure'' ν a
  · change iIndepFun (fun n ↦ ((fun ω ↦ ω n a) ∘ Prod.snd)) (Bandit.measure alg ν)
    rw [← iIndepFun_map_iff (by fun_prop) (fun _ ↦ Measurable.aemeasurable (by fun_prop))]
    rw [← Measure.snd, Bandit.snd_measure]
    exact iIndepFun_eval_streamMeasure'' ν a

lemma identDistrib_rewardByCount_stream [Countable α] [StandardBorelSpace α] [Nonempty α]
    (a : α) :
    IdentDistrib (fun ω n ↦ rewardByCount a (n + 1) ω) (fun ω n ↦ ω.2 n a)
      (Bandit.measure alg ν) (Bandit.measure alg ν) :=
  (identDistrib_rewardByCount_stream' a).trans (identDistrib_eval_streamMeasure_measure a)

-- todo: this should NOT be required. Independence in time is all we need. Fix downstream lemmas.
lemma indepFun_rewardByCount_of_ne {a b : α} (hab : a ≠ b) :
    IndepFun (fun ω s ↦ rewardByCount a s ω) (fun ω s ↦ rewardByCount b s ω)
      (Bandit.measure alg ν) := by
  sorry

lemma identDistrib_sum_Icc_rewardByCount [Nonempty α] [Countable α] (m : ℕ) (a : α) :
    IdentDistrib (fun ω ↦ ∑ s ∈ Icc 1 m, rewardByCount a s ω)
      (fun ω ↦ ∑ s ∈ range m, ω.2 s a) (Bandit.measure alg ν) (Bandit.measure alg ν) := by
  have h1 (a : α) :
      IdentDistrib (fun ω s ↦ rewardByCount a (s + 1) ω) (fun ω s ↦ ω.2 s a)
        (Bandit.measure alg ν) (Bandit.measure alg ν) :=
    identDistrib_rewardByCount_stream a
  have h_eq (ω : (ℕ → α × ℝ) × (ℕ → α → ℝ)) : ∑ s ∈ Icc 1 m, rewardByCount a s ω
      = ∑ s ∈ range m, rewardByCount a (s + 1) ω := by
    let e : Icc 1 m ≃ range m :=
    { toFun x := ⟨x - 1, by have h := x.2; simp only [mem_Icc] at h; simp; grind⟩
      invFun x := ⟨x + 1, by
        have h := x.2
        simp only [mem_Icc, le_add_iff_nonneg_left, zero_le, true_and, ge_iff_le]
        simp only [mem_range] at h
        grind⟩
      left_inv x := by have h := x.2; simp only [mem_Icc] at h; grind
      right_inv x := by have h := x.2; grind }
    rw [← sum_coe_sort (Icc 1 m), ← sum_coe_sort (range m), sum_equiv e]
    · simp
    · simp only [univ_eq_attach, mem_attach, forall_const, Subtype.forall, mem_Icc,
        forall_and_index]
      grind
  simp_rw [h_eq]
  exact IdentDistrib.comp (h1 a) (u := fun p ↦ ∑ s ∈ range m, p s) (by fun_prop)

end Bandits
