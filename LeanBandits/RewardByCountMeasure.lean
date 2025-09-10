/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.Bandit
import LeanBandits.ForMathlib.CondDistrib
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
lemma measurable_stepsUntil (a : α) (m : ℕ) : Measurable (fun k ↦ stepsUntil k a m) := by
  classical
  have h_union : {k' | ∃ s, pullCount k' a (s + 1) = m}
      = ⋃ s : ℕ, {k' | pullCount k' a (s + 1) = m} := by ext; simp
  have h_meas_set : MeasurableSet {k' | ∃ s, pullCount k' a (s + 1) = m} := by
    rw [h_union]
    exact MeasurableSet.iUnion fun s ↦ (measurableSet_singleton _).preimage (by fun_prop)
  simp_rw [stepsUntil_eq_dite]
  suffices Measurable fun k ↦ if h : k ∈ {k' | ∃ s, pullCount k' a (s + 1) = m}
      then (Nat.find h : ℕ∞) else ⊤ by convert this
  refine Measurable.dite (s := {k' : ℕ → α | ∃ s, pullCount k' a (s + 1) = m})
    (f := fun x ↦ (Nat.find x.2 : ℕ∞)) (g := fun _ ↦ ⊤) ?_ (by fun_prop) h_meas_set
  refine Measurable.coe_nat_enat ?_
  refine measurable_find _ fun k ↦ ?_
  suffices MeasurableSet {x : ℕ → α | pullCount x a (k + 1) = m} by
    have : Subtype.val ''
          {x : {k' : ℕ → α | ∃ s, pullCount k' a (s + 1) = m} | pullCount x a (k + 1) = m}
        = {x : ℕ → α | pullCount x a (k + 1) = m} := by
      ext x
      simp only [Set.mem_setOf_eq, Set.coe_setOf, Set.mem_image, Subtype.exists, exists_and_left,
        exists_prop, exists_eq_right_right, and_iff_left_iff_imp]
      exact fun h ↦ ⟨_, h⟩
    refine (MeasurableEmbedding.subtype_coe h_meas_set).measurableSet_image.mp ?_
    rw [this]
    exact (measurableSet_singleton _).preimage (by fun_prop)
  exact (measurableSet_singleton _).preimage (by fun_prop)

lemma measurable_stepsUntil'' (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × ℝ) ↦ stepsUntil (arm · ω) a m) :=
  (measurable_stepsUntil a m).comp (by fun_prop)

lemma measurable_stepsUntil' (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ stepsUntil (arm · ω.1) a m) :=
  (measurable_stepsUntil'' a m).comp measurable_fst

@[fun_prop]
lemma measurable_rewardByCount (a : α) (m : ℕ) :
    Measurable (fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ rewardByCount a m ω.1 ω.2) := by
  simp_rw [rewardByCount_eq_ite]
  refine Measurable.ite ?_ ?_ ?_
  · exact (measurableSet_singleton _).preimage <| measurable_stepsUntil' a m
  · fun_prop
  · change Measurable ((fun p : ℕ × (ℕ → α × ℝ) ↦ reward p.1 p.2)
      ∘ (fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦ ((stepsUntil (arm · ω.1) a m).toNat, ω.1)))
    have : Measurable fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦
        ((stepsUntil (arm · ω.1) a m).toNat, ω.1) :=
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
/-- Law of `Y` conditioned on `X`. -/
notation "𝓛[" Y " | " X "; " μ "]" => condDistrib Y X μ

omit [DecidableEq α] [MeasurableSingletonClass α] in
lemma condDistrib_reward' (n : ℕ) :
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
    condDistrib_fst_prod (by fun_prop) (by fun_prop) _
  filter_upwards [h_ra', h_prod] with ω h_eq h_prod
  rw [h_prod, h_eq]

omit [DecidableEq α] in
lemma reward_cond_arm [Countable α] (a : α) (n : ℕ)
    (hμa : (Bandit.measure alg ν).map (fun ω ↦ arm n ω.1) {a} ≠ 0) :
    𝓛[fun ω ↦ reward n ω.1 | fun ω ↦ arm n ω.1 ← a; Bandit.measure alg ν] = ν a := by
  let μ := Bandit.measure alg ν
  have h_ra : 𝓛[fun ω ↦ reward n ω.1 | fun ω ↦ arm n ω.1; μ] =ᵐ[μ.map (fun ω ↦ arm n ω.1)] ν :=
    condDistrib_reward' n
  have h_eq := condDistrib_ae_eq_cond (μ := μ)
    (X := fun ω ↦ arm n ω.1) (Y := fun ω ↦ reward n ω.1) (by fun_prop) (by fun_prop)
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h_ra h_eq
  specialize h_ra a hμa
  specialize h_eq a hμa
  rw [h_ra] at h_eq
  exact h_eq.symm

lemma condIndepFun_reward_stepsUntil_arm [StandardBorelSpace α] [Countable α] [Nonempty α]
    (a : α) (m n : ℕ) (hm : m ≠ 0) :
    CondIndepFun (mα.comap (fun ω ↦ arm n ω.1)) ((measurable_arm n).comp measurable_fst).comap_le
      (fun ω ↦ reward n ω.1) ({ω | stepsUntil (arm · ω.1) a m = ↑n}.indicator (fun _ ↦ 1))
      (Bandit.measure alg ν) := by
  -- first restrict to the `trajMeasure` side
  suffices h_indep :
      CondIndepFun (mα.comap (arm n)) (measurable_arm n).comap_le
        (reward n) ({ω | stepsUntil (arm · ω) a m = ↑n}.indicator (fun _ ↦ 1))
        (Bandit.trajMeasure alg ν) by
    sorry
  -- Now prove the independence : the indicator of `stepsUntil ... = n` is a function of
  -- `hist (n-1)` and `arm n`.
  -- It thus suffices to prove the independence of `reward n` and `hist (n-1)` conditionally
  -- on `arm n`.
  have hn : n ≠ 0 := by
    sorry -- assume it?
  have h_indep : CondIndepFun (mα.comap (arm n)) (measurable_arm n).comap_le (reward n)
      (hist (n - 1)) (Bandit.trajMeasure alg ν) := by
    convert condIndepFun_reward_hist_arm (alg := alg) (ν := ν) (n - 1)
      <;> rw [Nat.sub_add_cancel (by grind)]
  have h_indep' : CondIndepFun (mα.comap (arm n)) (measurable_arm n).comap_le (reward n)
      (fun ω ↦ (hist (n - 1) ω, arm n ω)) (Bandit.trajMeasure alg ν) :=
    h_indep.prod_right (by fun_prop) (by fun_prop) (by fun_prop)
  suffices ∃ φ : ((Iic (n - 1) → α × ℝ) × α) → ℕ, Measurable φ ∧
      ({ω : ℕ → α × ℝ | stepsUntil (arm · ω) a m = ↑n}.indicator (fun _ ↦ 1))
        = φ ∘ (fun ω : ℕ → α × ℝ ↦ (hist (n - 1) ω, arm n ω)) by
    obtain ⟨φ, hφ_meas, h_eq⟩ := this
    rw [h_eq]
    exact h_indep'.comp measurable_id hφ_meas
  -- it would follow from measurability wrt the sigma-algebra generated by
  -- `hist (n-1)` and `arm n`, but we can also give an explicit function
  let k : ((Iic (n - 1) → α × ℝ) × α) → (ℕ → α) := fun x i ↦
    if hi : i ∈ Iic (n - 1) then (x.1 ⟨i, hi⟩).1 else if i = n then x.2 else a -- a is arbitrary
  let φ : ((Iic (n - 1) → α × ℝ) × α) → ℕ := fun x ↦ if stepsUntil (k x) a m = ↑n then 1 else 0
  classical
  have hφ_meas : Measurable φ := by
    refine Measurable.ite ?_ (by fun_prop) (by fun_prop)
    refine (measurableSet_singleton _).preimage ?_
    refine (measurable_stepsUntil a m).comp ?_
    unfold k
    rw [measurable_pi_iff]
    intro i
    split_ifs <;> fun_prop
  refine ⟨φ, hφ_meas, ?_⟩
  ext ω
  classical
  simp only [Set.indicator_apply, Set.mem_setOf_eq, Function.comp_apply, φ]
  congr 1
  rw [stepsUntil_eq_congr]
  intro i hin
  simp only [arm, mem_Iic, hist, dite_eq_ite, left_eq_ite_iff, not_le, k]
  intro hni
  have : i = n := by grind
  simp [this]

lemma reward_cond_stepsUntil [StandardBorelSpace α] [Countable α] [Nonempty α] (a : α) (m n : ℕ)
    (hm : m ≠ 0)
    (hμn : (Bandit.measure alg ν) ((fun ω ↦ stepsUntil (arm · ω.1) a m) ⁻¹' {↑n}) ≠ 0) :
    𝓛[fun ω ↦ reward n ω.1 | fun ω ↦ stepsUntil (fun x ↦ arm x ω.1) a m ← (n : ℕ∞);
      Bandit.measure alg ν] = ν a := by
  let μ := Bandit.measure alg ν
  have hμna :
      μ ((fun ω ↦ stepsUntil (arm · ω.1) a m) ⁻¹' {↑n} ∩ (fun ω ↦ arm n ω.1) ⁻¹' {a}) ≠ 0 := by
    suffices ((fun ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) ↦
          stepsUntil (arm · ω.1) a m) ⁻¹' {↑n} ∩ (fun ω ↦ arm n ω.1) ⁻¹' {a})
        = (fun ω ↦ stepsUntil (arm · ω.1) a m) ⁻¹' {↑n} by simpa [this] using hμn
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact arm_eq_of_stepsUntil_eq_coe hm
  have hμa : μ.map (fun ω ↦ arm n ω.1) {a} ≠ 0 := by
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    refine fun h_zero ↦ hμn (measure_mono_null (fun ω ↦ ?_) h_zero)
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact arm_eq_of_stepsUntil_eq_coe hm
  calc 𝓛[fun ω ↦ reward n ω.1 | fun ω ↦ stepsUntil (arm · ω.1) a m ← (n : ℕ∞); μ]
  _ = (μ[|(fun ω ↦ stepsUntil (fun x ↦ arm x ω.1) a m) ⁻¹' {↑n} ∩ (fun ω ↦ arm n ω.1) ⁻¹' {a}]).map
      (fun ω ↦ reward n ω.1) := by
    congr with ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, iff_self_and]
    exact arm_eq_of_stepsUntil_eq_coe hm
  _ = (μ[|{ω : (ℕ → α × ℝ) × (ℕ → α → ℝ) | stepsUntil (arm · ω.1) a m = ↑n}.indicator 1 ⁻¹' {1}
      ∩ (fun ω ↦ arm n ω.1) ⁻¹' {a}]).map (fun ω ↦ reward n ω.1) := by
    congr 3 with ω
    simp [Set.indicator_apply]
  _ = 𝓛[fun ω ↦ reward n ω.1 | fun ω ↦ arm n ω.1 ← a; μ] := by
    rw [cond_of_condIndepFun (by fun_prop)]
    · exact condIndepFun_reward_stepsUntil_arm a m n hm
    · refine measurable_one.indicator ?_
      exact measurableSet_eq_fun' (by fun_prop) (by fun_prop)
    · fun_prop
    · convert hμna
      ext ω
      simp [Set.indicator_apply]
  _ = ν a := reward_cond_arm a n hμa

lemma condDistrib_rewardByCount_stepsUntil [Countable α] [StandardBorelSpace α] [Nonempty α]
    (a : α) (m : ℕ) (hm : m ≠ 0) :
    condDistrib (fun ω ↦ rewardByCount a m ω.1 ω.2) (fun ω ↦ stepsUntil (arm · ω.1) a m)
        (Bandit.measure alg ν)
      =ᵐ[(Bandit.measure alg ν).map (fun ω ↦ stepsUntil (arm · ω.1) a m)] Kernel.const _ (ν a) := by
  let μ := Bandit.measure alg ν
  refine (condDistrib_ae_eq_cond (μ := μ)
    (X := fun ω ↦ stepsUntil (arm · ω.1) a m) (by fun_prop) (by fun_prop)).trans ?_
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
    · exact indepFun_prod (X := fun ω : ℕ → α × ℝ ↦ stepsUntil (arm · ω) a m)
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
    HasLaw (fun ω ↦ rewardByCount a m ω.1 ω.2) (ν a) (Bandit.measure alg ν) where
  map_eq := by
    have h_condDistrib :
        condDistrib (fun ω ↦ rewardByCount a m ω.1 ω.2) (fun ω ↦ stepsUntil (arm · ω.1) a m)
          (Bandit.measure alg ν)
        =ᵐ[(Bandit.measure alg ν).map (fun ω ↦ stepsUntil (arm · ω.1) a m)]
          Kernel.const _ (ν a) := condDistrib_rewardByCount_stepsUntil a m hm
    calc (Bandit.measure alg ν).map (fun ω ↦ rewardByCount a m ω.1 ω.2)
    _ = (condDistrib (fun ω ↦ rewardByCount a m ω.1 ω.2) (fun ω ↦ stepsUntil (arm · ω.1) a m)
          (Bandit.measure alg ν))
        ∘ₘ ((Bandit.measure alg ν).map (fun ω ↦ stepsUntil (arm · ω.1) a m)) := by
      rw [condDistrib_comp_map (by fun_prop) (by fun_prop)]
    _ = (Kernel.const _ (ν a))
        ∘ₘ ((Bandit.measure alg ν).map (fun ω ↦ stepsUntil (arm · ω.1) a m)) :=
      Measure.comp_congr h_condDistrib
    _ = ν a := by
      have : IsProbabilityMeasure
          ((Bandit.measure alg ν).map (fun ω ↦ stepsUntil (arm · ω.1) a m)) :=
        isProbabilityMeasure_map (by fun_prop)
      simp

lemma identDistrib_rewardByCount [Countable α] [StandardBorelSpace α] [Nonempty α] (a : α) (n m : ℕ)
    (hn : n ≠ 0) (hm : m ≠ 0) :
    IdentDistrib (fun ω ↦ rewardByCount a n ω.1 ω.2) (fun ω ↦ rewardByCount a m ω.1 ω.2)
      (Bandit.measure alg ν) (Bandit.measure alg ν) where
  aemeasurable_fst := by fun_prop
  aemeasurable_snd := by fun_prop
  map_eq := by rw [(hasLaw_rewardByCount a n hn).map_eq, (hasLaw_rewardByCount a m hm).map_eq]

lemma iIndepFun_rewardByCount (alg : Algorithm α ℝ) (ν : Kernel α ℝ) [IsMarkovKernel ν] :
    iIndepFun (fun (p : α × ℕ) ω ↦ rewardByCount p.1 p.2 ω.1 ω.2) (Bandit.measure alg ν) := by
  sorry

end Bandits
