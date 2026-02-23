/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.Bandit.Regret
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.SequentialLearning.StationaryEnv

/-! # Bayesian stationary environments -/

open MeasureTheory ProbabilityTheory Finset

namespace Learning

variable {𝓔 α R Ω : Type*}
variable [MeasurableSpace 𝓔] [MeasurableSpace α] [MeasurableSpace R] [MeasurableSpace Ω]

structure IsBayesAlgEnvSeq
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (Q : Measure 𝓔) (κ : Kernel (𝓔 × α) R) (alg : Algorithm α R)
    (E : Ω → 𝓔) (A : ℕ → Ω → α) (R' : ℕ → Ω → R)
    (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  measurable_E : Measurable E := by fun_prop
  measurable_A n : Measurable (A n) := by fun_prop
  measurable_R n : Measurable (R' n) := by fun_prop
  hasLaw_env : HasLaw E Q P
  hasCondDistrib_action_zero : HasCondDistrib (A 0) E (Kernel.const _ alg.p0) P
  hasCondDistrib_reward_zero : HasCondDistrib (R' 0) (fun ω ↦ (E ω, A 0 ω)) κ P
  hasCondDistrib_action n :
    HasCondDistrib (A (n + 1)) (fun ω ↦ (E ω, IsAlgEnvSeq.hist A R' n ω))
      ((alg.policy n).prodMkLeft _) P
  hasCondDistrib_reward n :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, E ω, A (n + 1) ω))
      (κ.prodMkLeft _) P

namespace IsBayesAlgEnvSeq

def trajectory (A : ℕ → Ω → α) (R' : ℕ → Ω → R) (ω : Ω) : ℕ → α × R := fun n ↦ (A n ω, R' n ω)

@[fun_prop]
lemma measurable_trajectory {A : ℕ → Ω → α} {R' : ℕ → Ω → R} (hA : ∀ n, Measurable (A n))
    (hR : ∀ n, Measurable (R' n)) : Measurable (trajectory A R') := by
  unfold trajectory
  fun_prop

section Real

noncomputable
def actionMean (κ : Kernel (𝓔 × α) ℝ) (E : Ω → 𝓔) (a : α) (ω : Ω) : ℝ := (κ (E ω, a))[id]

@[fun_prop]
lemma measurable_actionMean {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} {a : α} (hE : Measurable E) :
    Measurable (actionMean κ E a) :=
  stronglyMeasurable_id.integral_kernel.measurable.comp (by fun_prop)

noncomputable
def bestAction [Nonempty α] [Fintype α] [Encodable α] [MeasurableSingletonClass α]
    (κ : Kernel (𝓔 × α) ℝ) (E : Ω → 𝓔) (ω : Ω) : α :=
  measurableArgmax (fun ω' a ↦ actionMean κ E a ω') ω

@[fun_prop]
lemma measurable_bestAction [Nonempty α] [Fintype α] [Encodable α] [MeasurableSingletonClass α]
    {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} (hE : Measurable E) : Measurable (bestAction κ E) :=
  measurable_measurableArgmax (by fun_prop)

noncomputable
def regret (κ : Kernel (𝓔 × α) ℝ) (E : Ω → 𝓔) (A : ℕ → Ω → α) (t : ℕ) (ω : Ω) : ℝ :=
  Bandits.regret (κ.sectR (E ω)) A t ω

@[fun_prop]
lemma measurable_regret [Countable α] {κ : Kernel (𝓔 × α) ℝ} {E : Ω → 𝓔} {A : ℕ → Ω → α} {t : ℕ}
    (hE : Measurable E) (hA : ∀ n, Measurable (A n)) :
    Measurable (regret κ E A t) := by
  have hm := (stronglyMeasurable_id.integral_kernel (κ := κ)).measurable
  exact (Measurable.const_mul (Measurable.iSup fun _ ↦ (hm.comp (by fun_prop))) _).sub
    (Finset.measurable_sum _ fun _ _ ↦ hm.comp (by fun_prop))

end Real

variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
variable {Q : Measure 𝓔} {κ : Kernel (𝓔 × α) R} {alg : Algorithm α R}
variable {E : Ω → 𝓔} {A : ℕ → Ω → α} {R' : ℕ → Ω → R}
variable {P : Measure Ω} [IsFiniteMeasure P]

section Laws

lemma hasLaw_action_zero [IsProbabilityMeasure P] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    HasLaw (A 0) alg.p0 P := h.hasCondDistrib_action_zero.hasLaw_of_const

lemma hasCondDistrib_action' (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R' n) (alg.policy n) P :=
  (h.hasCondDistrib_action n).comp_left (by fun_prop)

lemma hasCondDistrib_reward' [IsFiniteKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (E ω, A (n + 1) ω)) κ P :=
  (h.hasCondDistrib_reward n).comp_left (by fun_prop)

end Laws

section CondDistribIsAlgEnvSeq

lemma hasLaw_IT_action_zero (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    ∀ᵐ e ∂Q, HasLaw (IT.action 0) alg.p0 (condDistrib (trajectory A R') E P e) := by
  have hmt := (measurable_trajectory h.measurable_A h.measurable_R)
  have hma : Measurable (IT.action 0) := IT.measurable_action (α := α) (R := R) 0
  rw [← h.hasLaw_env.map_eq]
  filter_upwards [condDistrib_comp E (hmt.aemeasurable) hma,
    h.hasCondDistrib_action_zero.condDistrib_eq] with e hc hcd
  have hat : IT.action 0 ∘ trajectory A R' = A 0 := rfl
  exact ⟨hma.aemeasurable, by rw [← Kernel.map_apply _ hma, ← hc, hat, hcd, Kernel.const_apply]⟩

lemma hasCondDistrib_IT_reward_zero [IsFiniteKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    ∀ᵐ e ∂Q, HasCondDistrib (IT.reward 0) (IT.action 0) (κ.sectR e)
      (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq]
  have hmt := (measurable_trajectory h.measurable_A h.measurable_R)
  have h_prod := condDistrib_prod_left (h.measurable_A 0).aemeasurable
    (h.measurable_R 0).aemeasurable h.measurable_E.aemeasurable (μ := P)
  have h_comp_pair : ⇑(condDistrib (fun ω ↦ (A 0 ω, R' 0 ω)) E P) =ᶠ[ae (P.map E)]
      ⇑((condDistrib (trajectory A R') E P).map (fun ω ↦ (IT.action 0 ω, IT.reward 0 ω))) :=
    condDistrib_comp E hmt.aemeasurable
      ((IT.measurable_action 0).prodMk (IT.measurable_reward 0))
  have h_comp_action : ⇑(condDistrib (A 0) E P) =ᶠ[ae (P.map E)]
      ⇑((condDistrib (trajectory A R') E P).map (IT.action 0)) :=
    condDistrib_comp E hmt.aemeasurable (IT.measurable_action 0)
  have h_reward_eq := h.hasCondDistrib_reward_zero.condDistrib_eq
  rw [(compProd_map_condDistrib (h.measurable_A 0).aemeasurable).symm] at h_reward_eq
  filter_upwards [h_prod, h_comp_pair, h_comp_action,
    (Measure.ae_compProd_iff (Kernel.measurableSet_eq _ _)).mp h_reward_eq]
    with e h_prod_e h_pair_e h_act_e h_nested_e
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
  rw [← Kernel.map_apply _ (by fun_prop), ← h_pair_e]
  conv_rhs => rw [← Kernel.map_apply _ (IT.measurable_action 0), ← h_act_e]
  rw [h_prod_e, Kernel.compProd_apply_eq_compProd_sectR]
  refine Measure.compProd_congr ?_
  filter_upwards [h_nested_e] with a ha
  ext s _
  simp_rw [Kernel.sectR_apply, ha]

lemma hasCondDistrib_IT_action (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    ∀ᵐ e ∂Q, HasCondDistrib (IT.action (n + 1)) (IT.hist n) (alg.policy n)
      (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq]
  have hW := (measurable_trajectory h.measurable_A h.measurable_R).aemeasurable (μ := P)
  have h_hist_meas := IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n
  have h_prod := condDistrib_prod_left h_hist_meas.aemeasurable
    (h.measurable_A (n + 1)).aemeasurable h.measurable_E.aemeasurable (μ := P)
  have h_action_env := (h.hasCondDistrib_action n).condDistrib_eq
  have h_comp_pair : ⇑(condDistrib (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω)) E P)
      =ᶠ[ae (P.map E)] ⇑((condDistrib (trajectory A R') E P).map
        (fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω))) :=
    condDistrib_comp E hW ((IT.measurable_hist n).prodMk (IT.measurable_action (n + 1)))
  have h_comp_hist : ⇑(condDistrib (IsAlgEnvSeq.hist A R' n) E P) =ᶠ[ae (P.map E)]
      ⇑((condDistrib (trajectory A R') E P).map (IT.hist n)) :=
    condDistrib_comp E hW (IT.measurable_hist n)
  rw [(compProd_map_condDistrib h_hist_meas.aemeasurable).symm] at h_action_env
  filter_upwards [h_prod, h_comp_pair, h_comp_hist,
    (Measure.ae_compProd_iff (Kernel.measurableSet_eq _ _)).mp h_action_env]
    with e h_prod_e h_pair_e h_hist_e h_nested_e
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
  rw [← Kernel.map_apply _ ((IT.measurable_hist n).prodMk (IT.measurable_action (n + 1))),
    ← h_pair_e]
  conv_rhs => rw [← Kernel.map_apply _ (IT.measurable_hist n), ← h_hist_e]
  rw [h_prod_e, Kernel.compProd_apply_eq_compProd_sectR]
  refine Measure.compProd_congr ?_
  filter_upwards [h_nested_e] with _ ha
  ext s _
  rw [Kernel.sectR_apply, ha, Kernel.prodMkLeft_apply]

lemma hasCondDistrib_IT_reward [IsFiniteKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    ∀ᵐ e ∂Q, HasCondDistrib (IT.reward (n + 1)) (fun x ↦ (IT.hist n x, IT.action (n + 1) x))
      ((κ.sectR e).prodMkLeft _) (condDistrib (trajectory A R') E P e) := by
  rw [← h.hasLaw_env.map_eq]
  have hmt := measurable_trajectory h.measurable_A h.measurable_R
  have hm := IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n
  have hm_pair : Measurable
      (fun f : ℕ → α × R ↦ (IT.hist n f, IT.action (n + 1) f)) := by fun_prop
  have h_reorder : HasCondDistrib (R' (n + 1))
      (fun ω ↦ (E ω, IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
      (κ.comap (fun (e, _, a) ↦ (e, a)) (by fun_prop)) P := by
    convert (h.hasCondDistrib_reward n).comp_right (MeasurableEquiv.prodAssoc.symm.trans
      ((MeasurableEquiv.prodComm.prodCongr (MeasurableEquiv.refl α)).trans
        MeasurableEquiv.prodAssoc)) using 2
  have h_eq := h_reorder.condDistrib_eq
  rw [(compProd_map_condDistrib (hm.prodMk (h.measurable_A (n + 1))).aemeasurable).symm] at h_eq
  have h_comp_triple : ⇑(condDistrib
      (fun ω ↦ ((IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω), R' (n + 1) ω)) E P)
      =ᶠ[ae (P.map E)] ⇑((condDistrib (trajectory A R') E P).map
        (fun ω ↦ ((IT.hist n ω, IT.action (n + 1) ω), IT.reward (n + 1) ω))) :=
    condDistrib_comp E hmt.aemeasurable (hm_pair.prodMk (IT.measurable_reward (n + 1)))
  have h_comp_pair : ⇑(condDistrib (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω)) E P)
      =ᶠ[ae (P.map E)] ⇑((condDistrib (trajectory A R') E P).map
        (fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω))) :=
    condDistrib_comp E hmt.aemeasurable hm_pair
  filter_upwards [
    condDistrib_prod_left (hm.prodMk (h.measurable_A (n + 1))).aemeasurable
      (h.measurable_R (n + 1)).aemeasurable h.measurable_E.aemeasurable (μ := P),
    h_comp_triple, h_comp_pair,
    (Measure.ae_compProd_iff (Kernel.measurableSet_eq _ _)).mp h_eq]
    with e h_prod h_triple h_pair h_inner
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
  rw [← Kernel.map_apply _ (hm_pair.prodMk (IT.measurable_reward (n + 1))), ← h_triple]
  conv_rhs => rw [← Kernel.map_apply _ hm_pair, ← h_pair]
  rw [h_prod, Kernel.compProd_apply_eq_compProd_sectR]
  exact Measure.compProd_congr (by
    filter_upwards [h_inner] with a ha; ext s _
    simp only [Kernel.sectR_apply, ha, Kernel.comap_apply, Kernel.prodMkLeft_apply])

lemma ae_IsAlgEnvSeq [IsMarkovKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    ∀ᵐ e ∂Q, IsAlgEnvSeq IT.action IT.reward alg (stationaryEnv (κ.sectR e))
      (condDistrib (trajectory A R') E P e) := by
  filter_upwards [hasLaw_IT_action_zero h, hasCondDistrib_IT_reward_zero h,
    ae_all_iff.2 (hasCondDistrib_IT_action h), ae_all_iff.2 (hasCondDistrib_IT_reward h)]
    with _ h_a0 h_r0 h_a h_r
  exact {
    hasLaw_action_zero := h_a0
    hasCondDistrib_reward_zero := h_r0
    hasCondDistrib_action := h_a
    hasCondDistrib_reward := h_r
  }

end CondDistribIsAlgEnvSeq

end IsBayesAlgEnvSeq

section IsAlgEnvSeq

noncomputable
def bayesStationaryEnv (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × α) R)
    [IsMarkovKernel κ] : Environment α (𝓔 × R) where
  feedback n :=
    let g : (Iic n → α × 𝓔 × R) × α → 𝓔 × α := fun (h, a) => ((h ⟨0, by simp⟩).2.1, a)
    (Kernel.deterministic (Prod.fst ∘ g) (by fun_prop)) ×ₖ (κ.comap g (by fun_prop))
  ν0 := (Kernel.const _ Q) ⊗ₖ κ.swapLeft

variable [Nonempty α] [Nonempty 𝓔] [Nonempty R]
variable [StandardBorelSpace α] [StandardBorelSpace 𝓔] [StandardBorelSpace R]
variable {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (𝓔 × α) R} [IsMarkovKernel κ]
variable {alg : Algorithm α R} {A : ℕ → Ω → α} {R' : ℕ → Ω → 𝓔 × R}
variable {P : Measure Ω} [IsProbabilityMeasure P]

lemma IsAlgEnvSeq.isBayesAlgEnvSeq
    (h : IsAlgEnvSeq A R' (alg.prod_left 𝓔) (bayesStationaryEnv Q κ) P) :
    IsBayesAlgEnvSeq Q κ alg (fun ω ↦ (R' 0 ω).1) A (fun n ω ↦ (R' n ω).2) P where
  measurable_E := (h.measurable_R 0).fst
  measurable_A := h.measurable_A
  measurable_R n := (h.measurable_R n).snd
  hasLaw_env := by
    apply HasCondDistrib.hasLaw_of_const
    simpa [bayesStationaryEnv] using h.hasCondDistrib_reward_zero.fst
  hasCondDistrib_action_zero := by
    have hfst : HasCondDistrib (fun ω ↦ (R' 0 ω).1) (A 0) (Kernel.const α Q) P := by
      simpa [bayesStationaryEnv] using h.hasCondDistrib_reward_zero.fst
    -- E' | A 0 is constant Q = P.map E', so A 0 and E' are independent
    have h_indep : IndepFun (A 0) (fun ω ↦ (R' 0 ω).1) P := by
      rw [indepFun_iff_condDistrib_eq_const (h.measurable_A 0).aemeasurable
        (h.measurable_R 0).fst.aemeasurable, hfst.hasLaw_of_const.map_eq]
      exact hfst.condDistrib_eq
    -- From independence: condDistrib (A 0) E' P = const (P.map (A 0)) = const alg.p0
    have hcd := condDistrib_of_indepFun h_indep.symm (h.measurable_R 0).fst.aemeasurable
      (h.measurable_A 0).aemeasurable
    simp only [h.hasLaw_action_zero.map_eq, Algorithm.prod_left] at hcd
    exact ⟨(h.measurable_A 0).aemeasurable, (h.measurable_R 0).fst.aemeasurable, hcd⟩
  hasCondDistrib_reward_zero := by
    have h0 := h.hasCondDistrib_reward_zero
    simp only [bayesStationaryEnv] at h0
    convert h0.of_compProd.comp_right (MeasurableEquiv.prodComm : α × 𝓔 ≃ᵐ 𝓔 × α) using 2
  hasCondDistrib_action n := by
    let f : (Iic n → α × 𝓔 × R) → 𝓔 × (Iic n → α × R) :=
      fun h ↦ ((h ⟨0, by simp⟩).2.1, fun i ↦ ((h i).1, (h i).2.2))
    suffices h' : HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R' n)
        (((alg.policy n).comap Prod.snd (by fun_prop)).comap f (by fun_prop)) P from
      h'.comp_left (f := f)
    exact h.hasCondDistrib_action n
  hasCondDistrib_reward n := by
    let f : (Iic n → α × 𝓔 × R) × α → (Iic n → α × R) × 𝓔 × α :=
      fun p ↦ ((fun i ↦ ((p.1 i).1, (p.1 i).2.2)), (p.1 ⟨0, by simp⟩).2.1, p.2)
    have hf : Measurable f := by fun_prop
    suffices h' : HasCondDistrib (fun ω ↦ (R' (n + 1) ω).2)
        (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
        ((Kernel.prodMkLeft (↥(Iic n) → α × R) κ).comap f hf) P from h'.comp_left hf
    simpa [bayesStationaryEnv, Kernel.snd_prod] using (h.hasCondDistrib_reward n).snd

end IsAlgEnvSeq

namespace IT

noncomputable
def bayesTrajMeasure (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × α) R)
    [IsMarkovKernel κ] (alg : Algorithm α R) : Measure (ℕ → α × 𝓔 × R) :=
  trajMeasure (alg.prod_left 𝓔) (bayesStationaryEnv Q κ)
deriving IsProbabilityMeasure

lemma isBayesAlgEnvSeq_bayesTrajMeasure
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace 𝓔] [Nonempty 𝓔]
    [StandardBorelSpace R] [Nonempty R]
    (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × α) R) [IsMarkovKernel κ]
    (alg : Algorithm α R) :
    IsBayesAlgEnvSeq Q κ alg (fun ω ↦ (ω 0).2.1) action (fun n ω ↦ (ω n).2.2)
       (bayesTrajMeasure Q κ alg) :=
  (isAlgEnvSeq_trajMeasure _ _).isBayesAlgEnvSeq

noncomputable
def bayesTrajMeasurePosterior [StandardBorelSpace 𝓔] [Nonempty 𝓔]
    (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (𝓔 × α) ℝ) [IsMarkovKernel κ]
    (alg : Algorithm α ℝ) (n : ℕ) : Kernel (Iic n → α × ℝ) 𝓔 :=
  condDistrib (fun ω ↦ (ω 0).2.1) (IsAlgEnvSeq.hist action (fun n ω ↦ (ω n).2.2) n)
    (bayesTrajMeasure Q κ alg)
deriving IsMarkovKernel

end IT

end Learning
