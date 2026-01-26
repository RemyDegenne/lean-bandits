/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.Bandit.Bandit
import Mathlib.Probability.IdentDistribIndep

/-! # Laws of `stepsUntil` and `rewardByCount`
-/

open MeasureTheory ProbabilityTheory Finset Learning
open scoped ENNReal NNReal

namespace Bandits

variable {α Ω : Type*} {mα : MeasurableSpace α} {mΩ : MeasurableSpace Ω} [DecidableEq α]
  [StandardBorelSpace α] [Nonempty α]
  {A : ℕ → Ω → α} {R : ℕ → Ω → ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
  {alg : Algorithm α ℝ} {ν : Kernel α ℝ} [IsMarkovKernel ν]
  {h_inter : IsAlgEnvSeq A R alg (stationaryEnv ν) P}

local notation "𝔓" => P.prod (streamMeasure ν)

omit [DecidableEq α] [StandardBorelSpace α] [Nonempty α] in
lemma hasLaw_Z (a : α) (m : ℕ) :
  HasLaw (fun ω ↦ ω.2 m a) (ν a) 𝔓 where
  map_eq := by
    calc (𝔓).map (fun ω ↦ ω.2 m a)
    _ = ((𝔓).snd).map (fun ω ↦ ω m a) := by
      rw [Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = (streamMeasure ν).map (fun ω ↦ ω m a) := by simp
    _ = ((Measure.infinitePi fun _ ↦ Measure.infinitePi ν).map (fun ω ↦ ω m)).map
        (fun ω ↦ ω a) := by
      rw [streamMeasure, Measure.map_map (by fun_prop) (by fun_prop)]
      rfl
    _ = ν a := by simp_rw [(measurePreserving_eval_infinitePi _ _).map_eq]

/-- Law of `Y` conditioned on the event `s`.-/
notation "𝓛[" Y " | " s "; " μ "]" => Measure.map Y (μ[|s])
/-- Law of `Y` conditioned on the event that `X` is in `s`. -/
notation "𝓛[" Y " | " X " in " s "; " μ "]" => Measure.map Y (μ[|X ⁻¹' s])
/-- Law of `Y` conditioned on the event that `X` equals `x`. -/
notation "𝓛[" Y " | " X " ← " x "; " μ "]" => Measure.map Y (μ[|X ⁻¹' {x}])

omit [DecidableEq α] in
lemma condDistrib_reward'' [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (n : ℕ) :
    𝓛[fun ω ↦ R n ω.1 | fun ω ↦ A n ω.1; 𝔓] =ᵐ[(𝔓).map (fun ω ↦ A n ω.1)] ν := by
  have hA := h.measurable_A
  have hR := h.measurable_R
  have h_ra' : 𝓛[R n | A n; P] =ᵐ[P.map (A n)] ν := h.condDistrib_reward_stationaryEnv n
  have h_law : (𝔓).map (fun ω ↦ A n ω.1) = P.map (A n) := by
    change ((𝔓).map (A n ∘ Prod.fst)) = _
    rw [← Measure.map_map (by fun_prop) (by fun_prop), ← Measure.fst, Measure.fst_prod]
  rw [h_law]
  have h_prod : 𝓛[fun ω ↦ R n ω.1 | fun ω ↦ A n ω.1; 𝔓]
      =ᵐ[P.map (A n)] 𝓛[R n | A n; P] :=
    condDistrib_fst_prod _ (by fun_prop) _
  filter_upwards [h_ra', h_prod] with ω h_eq h_prod
  rw [h_prod, h_eq]

omit [DecidableEq α] in
lemma reward_cond_action [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : α) (n : ℕ)
    (hμa : (𝔓).map (fun ω ↦ A n ω.1) {a} ≠ 0) :
    𝓛[fun ω ↦ R n ω.1 | fun ω ↦ A n ω.1 ← a; 𝔓] = ν a := by
  have hA := h.measurable_A
  have hR := h.measurable_R
  have h_ra : 𝓛[fun ω ↦ R n ω.1 | fun ω ↦ A n ω.1; 𝔓] =ᵐ[(𝔓).map (fun ω ↦ A n ω.1)] ν :=
    condDistrib_reward'' h n
  have h_eq := condDistrib_ae_eq_cond (μ := 𝔓)
    (X := fun ω ↦ A n ω.1) (Y := fun ω ↦ R n ω.1) (by fun_prop) (by fun_prop)
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h_ra h_eq
  specialize h_ra a hμa
  specialize h_eq a hμa
  rw [h_ra] at h_eq
  exact h_eq.symm

lemma condIndepFun_reward_stepsUntil_action' [StandardBorelSpace Ω]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : α) (m n : ℕ) :
    R n ⟂ᵢ[A n, h.measurable_A n; P] {ω | stepsUntil A a m ω = ↑n}.indicator (fun _ ↦ 1) := by
  -- the indicator of `stepsUntil ... = n` is a function of `hist (n-1)` and `action n`.
  -- It thus suffices to use the independence of `reward n` and `hist (n-1)` conditionally
  -- on `action n`.
  have hA := h.measurable_A
  have hR := h.measurable_R
  by_cases hn : n = 0
  · have h_indep : R 0 ⟂ᵢ[A 0, hA 0; P] A 0 :=
      condIndepFun_self_right (by fun_prop) (by fun_prop)
    simp only [hn, CharP.cast_eq_zero]
    refine h_indep.of_measurable_right (hX := hA 0) ?_
    exact measurable_comap_indicator_stepsUntil_eq_zero a m
  · have h_indep : R n ⟂ᵢ[A n, hA n; P] fun ω ↦ (IsAlgEnvSeq.hist A R (n - 1) ω, A n ω) :=
      IsAlgEnvSeq.condIndepFun_reward_hist_action_action' h n (by grind)
    refine h_indep.of_measurable_right (hX := hA n) ?_
    exact measurable_comap_indicator_stepsUntil_eq hA hR a m n

lemma condIndepFun_reward_stepsUntil_action [StandardBorelSpace Ω] [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P)
    (a : α) (m n : ℕ) :
    CondIndepFun (mα.comap (fun ω ↦ A n ω.1)) ((h.measurable_A n).comp measurable_fst).comap_le
      (fun ω ↦ R n ω.1) ({ω | stepsUntil A a m ω.1 = ↑n}.indicator (fun _ ↦ 1)) 𝔓 := by
  have hA := h.measurable_A
  have hR := h.measurable_R
  exact condIndepFun_fst_prod (ν := streamMeasure ν)
    (measurable_indicator_stepsUntil_eq hA hR a m n) (by fun_prop) (by fun_prop)
    (condIndepFun_reward_stepsUntil_action' h a m n)

lemma reward_cond_stepsUntil [StandardBorelSpace Ω] [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : α) (m n : ℕ)
    (hm : m ≠ 0) (hμn : 𝔓 ((fun ω ↦ stepsUntil A a m ω.1) ⁻¹' {↑n}) ≠ 0) :
    𝓛[fun ω ↦ R n ω.1 | fun ω ↦ stepsUntil A a m ω.1 ← ↑n; 𝔓] = ν a := by
  have hA := h.measurable_A
  have hR := h.measurable_R
  have hμna :
      𝔓 ((fun ω ↦ stepsUntil A a m ω.1) ⁻¹' {↑n} ∩ (fun ω ↦ A n ω.1) ⁻¹' {a}) ≠ 0 := by
    suffices ((fun ω : Ω × (ℕ → α → ℝ) ↦
          stepsUntil A a m ω.1) ⁻¹' {↑n} ∩ (fun ω ↦ A n ω.1) ⁻¹' {a})
        = (fun ω ↦ stepsUntil A a m ω.1) ⁻¹' {↑n} by simpa [this] using hμn
    ext ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, and_iff_left_iff_imp]
    exact action_eq_of_stepsUntil_eq_coe hm
  have hμa : (𝔓).map (fun ω ↦ A n ω.1) {a} ≠ 0 := by
    rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)]
    refine fun h_zero ↦ hμn (measure_mono_null (fun ω ↦ ?_) h_zero)
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact action_eq_of_stepsUntil_eq_coe hm
  calc 𝓛[fun ω ↦ R n ω.1 | fun ω ↦ stepsUntil A a m ω.1 ← (n : ℕ∞); 𝔓]
  _ = (𝔓[|(fun ω ↦ stepsUntil A a m ω.1) ⁻¹' {↑n} ∩ (fun ω ↦ A n ω.1) ⁻¹' {a}]).map
      (fun ω ↦ R n ω.1) := by
    congr with ω
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_inter_iff, iff_self_and]
    exact action_eq_of_stepsUntil_eq_coe hm
  _ = (𝔓[|(fun ω ↦ A n ω.1) ⁻¹' {a}
      ∩ {ω : Ω × (ℕ → α → ℝ) | stepsUntil A a m ω.1 = ↑n}.indicator 1 ⁻¹' {1} ]).map
      (fun ω ↦ R n ω.1) := by
    congr 2 with ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_singleton_iff, Set.indicator_apply,
      Set.mem_setOf_eq, Pi.one_apply, ite_eq_left_iff, zero_ne_one, imp_false, Decidable.not_not]
    rw [and_comm]
  _ = 𝓛[fun ω ↦ R n ω.1 | fun ω ↦ A n ω.1 ← a; 𝔓] := by
    rw [cond_of_condIndepFun (by fun_prop)]
    · exact condIndepFun_reward_stepsUntil_action h a m n
    · refine measurable_one.indicator ?_
      exact measurableSet_eq_fun (by fun_prop) (by fun_prop)
    · fun_prop
    · convert hμna using 2
      rw [Set.inter_comm]
      congr 1 with ω
      simp [Set.indicator_apply]
  _ = ν a := reward_cond_action h a n hμa

/-- The conditional distribution of the reward received at the `m`-th pull of action `a`
given the time at which number of pulls is `m` is the constant kernel with value `ν a`. -/
theorem condDistrib_rewardByCount_stepsUntil [StandardBorelSpace Ω] [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : α) (m : ℕ) (hm : m ≠ 0) :
    condDistrib (rewardByCount A R a m) (fun ω ↦ stepsUntil A a m ω.1) 𝔓
      =ᵐ[(𝔓).map (fun ω ↦ stepsUntil A a m ω.1)] Kernel.const _ (ν a) := by
  have hA := h.measurable_A
  have hR := h.measurable_R
  refine (condDistrib_ae_eq_cond (μ := 𝔓)
    (X := fun ω ↦ stepsUntil A a m ω.1) (by fun_prop) (by fun_prop)).trans ?_
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
    · exact indepFun_prod (X := fun ω : Ω ↦ stepsUntil A a m ω)
        (Y := fun ω : ℕ → α → ℝ ↦ ω m a) (by fun_prop) (by fun_prop)
  | coe n =>
    rw [Measure.map_congr (g := fun ω ↦ R n ω.1)]
    swap
    · refine ae_cond_of_forall_mem ((measurableSet_singleton _).preimage (by fun_prop)) ?_
      simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact fun ω ↦ rewardByCount_of_stepsUntil_eq_coe
    refine reward_cond_stepsUntil h a m n hm ?_
    rwa [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at hn

/-- The reward received at the `m`-th pull of action `a` has law `ν a`. -/
lemma hasLaw_rewardByCount [StandardBorelSpace Ω] [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : α) (m : ℕ) (hm : m ≠ 0) :
    HasLaw (rewardByCount A R a m) (ν a) 𝔓 where
  aemeasurable := (measurable_rewardByCount h.measurable_A h.measurable_R a m).aemeasurable
  map_eq := by
    have hA := h.measurable_A
    have hR := h.measurable_R
    have h_condDistrib :
        condDistrib (rewardByCount A R a m) (fun ω ↦ stepsUntil A a m ω.1) 𝔓
        =ᵐ[(𝔓).map (fun ω ↦ stepsUntil A a m ω.1)]
          Kernel.const _ (ν a) := condDistrib_rewardByCount_stepsUntil h a m hm
    calc (𝔓).map (rewardByCount A R a m)
    _ = (condDistrib (rewardByCount A R a m) (fun ω ↦ stepsUntil A a m ω.1) 𝔓)
        ∘ₘ ((𝔓).map (fun ω ↦ stepsUntil A a m ω.1)) := by
      rw [condDistrib_comp_map (by fun_prop) (by fun_prop)]
    _ = (Kernel.const _ (ν a)) ∘ₘ ((𝔓).map (fun ω ↦ stepsUntil A a m ω.1)) :=
      Measure.comp_congr h_condDistrib
    _ = ν a := by
      have : IsProbabilityMeasure ((𝔓).map (fun ω ↦ stepsUntil A a m ω.1)) :=
        Measure.isProbabilityMeasure_map (by fun_prop)
      simp

lemma identDistrib_rewardByCount [StandardBorelSpace Ω] [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : α) (n m : ℕ)
    (hn : n ≠ 0) (hm : m ≠ 0) :
    IdentDistrib (rewardByCount A R a n) (rewardByCount A R a m) 𝔓 𝔓 where
  aemeasurable_fst := (measurable_rewardByCount h.measurable_A h.measurable_R a n).aemeasurable
  aemeasurable_snd := (measurable_rewardByCount h.measurable_A h.measurable_R a m).aemeasurable
  map_eq := by rw [(hasLaw_rewardByCount h a n hn).map_eq, (hasLaw_rewardByCount h a m hm).map_eq]

lemma identDistrib_rewardByCount_id [StandardBorelSpace Ω] [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : α) (n : ℕ) (hn : n ≠ 0) :
    IdentDistrib (rewardByCount A R a n) id 𝔓 (ν a) where
  aemeasurable_fst := (measurable_rewardByCount h.measurable_A h.measurable_R a n).aemeasurable
  aemeasurable_snd := Measurable.aemeasurable <| by fun_prop
  map_eq := by rw [(hasLaw_rewardByCount h a n hn).map_eq, Measure.map_id]

lemma identDistrib_rewardByCount_eval [StandardBorelSpace Ω] [Countable α]
    (h : IsAlgEnvSeq A R alg (stationaryEnv ν) P) (a : α) (n m : ℕ) (hn : n ≠ 0) :
    IdentDistrib (rewardByCount A R a n) (fun ω ↦ ω m a) 𝔓 (streamMeasure ν) :=
  (identDistrib_rewardByCount_id h a n hn).trans
    (identDistrib_eval_eval_id_streamMeasure ν m a).symm

end Bandits
