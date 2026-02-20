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

variable {α R 𝓔 : Type*} [MeasurableSpace α] [MeasurableSpace R] [MeasurableSpace 𝓔]
variable {Ω : Type*} [MeasurableSpace Ω]

structure IsBayesAlgEnvSeq
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (Q : Measure 𝓔) (κ : Kernel (α × 𝓔) R) (alg : Algorithm α R)
    (E : Ω → 𝓔) (A : ℕ → Ω → α) (R' : ℕ → Ω → R)
    (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  measurable_E : Measurable E := by fun_prop
  measurable_A n : Measurable (A n) := by fun_prop
  measurable_R n : Measurable (R' n) := by fun_prop
  hasLaw_env : HasLaw E Q P
  hasCondDistrib_action_zero : HasCondDistrib (A 0) E (Kernel.const _ alg.p0) P
  hasCondDistrib_reward_zero : HasCondDistrib (R' 0) (fun ω ↦ (A 0 ω, E ω)) κ P
  hasCondDistrib_action n :
    HasCondDistrib (A (n + 1)) (fun ω ↦ (E ω, IsAlgEnvSeq.hist A R' n ω))
      ((alg.policy n).prodMkLeft _) P
  hasCondDistrib_reward n :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω, E ω))
      (κ.prodMkLeft _) P

namespace IsBayesAlgEnvSeq

section Laws

variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
variable {Q : Measure 𝓔} {κ : Kernel (α × 𝓔) R} {alg : Algorithm α R}
variable {E : Ω → 𝓔} {A : ℕ → Ω → α} {R' : ℕ → Ω → R}
variable {P : Measure Ω} [IsFiniteMeasure P]

lemma hasLaw_action_zero [IsProbabilityMeasure P] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    HasLaw (A 0) alg.p0 P :=
  h.hasCondDistrib_action_zero.hasLaw_of_const

lemma hasCondDistrib_action' (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R' n) (alg.policy n) P :=
  (h.hasCondDistrib_action n).comp_left (by fun_prop)

lemma hasCondDistrib_reward' [IsFiniteKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (A (n + 1) ω, E ω)) κ P :=
  (h.hasCondDistrib_reward n).comp_left (by fun_prop)

---

lemma hasLaw_action_zero_fiber (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    ∀ᵐ e ∂Q, HasLaw (IT.action 0) alg.p0
      (condDistrib (fun ω n ↦ (A n ω, R' n ω)) E P e) := by
  rw [← h.hasLaw_env.map_eq]
  have hW : AEMeasurable (fun ω n ↦ (A n ω, R' n ω)) P :=
    (measurable_pi_lambda _ fun n ↦ (h.measurable_A n).prodMk (h.measurable_R n)).aemeasurable
  have h_comp : ⇑(condDistrib (A 0) E P) =ᶠ[ae (P.map E)]
      ⇑((condDistrib (fun ω n ↦ (A n ω, R' n ω)) E P).map (IT.action 0)) :=
    condDistrib_comp E hW (IT.measurable_action 0)
  filter_upwards [h_comp, h.hasCondDistrib_action_zero.condDistrib_eq] with e he hcd
  exact ⟨(IT.measurable_action 0).aemeasurable, by
    rw [← Kernel.map_apply _ (IT.measurable_action 0), ← he, hcd, Kernel.const_apply]⟩

lemma hasCondDistrib_reward_zero_fiber [IsFiniteKernel κ]
    (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    ∀ᵐ e ∂Q, HasCondDistrib (IT.reward 0) (IT.action 0)
      (κ.comap (·, e) (by fun_prop))
      (condDistrib (fun ω n ↦ (A n ω, R' n ω)) E P e) := by
  rw [← h.hasLaw_env.map_eq]
  set W := fun ω n ↦ (A n ω, R' n ω)
  have hW : AEMeasurable W P :=
    (measurable_pi_lambda _ fun n ↦ (h.measurable_A n).prodMk (h.measurable_R n)).aemeasurable
  have h_swap : HasCondDistrib (R' 0) (fun ω ↦ (E ω, A 0 ω))
      (κ.comap Prod.swap (by fun_prop)) P := by
    convert h.hasCondDistrib_reward_zero.comp_right
      (MeasurableEquiv.prodComm : α × 𝓔 ≃ᵐ 𝓔 × α) using 2
  have h_prod := condDistrib_prod_left (h.measurable_A 0).aemeasurable
    (h.measurable_R 0).aemeasurable h.measurable_E.aemeasurable (μ := P)
  have h_comp_pair : ⇑(condDistrib (fun ω ↦ (A 0 ω, R' 0 ω)) E P) =ᶠ[ae (P.map E)]
      ⇑((condDistrib W E P).map (fun ω ↦ (IT.action 0 ω, IT.reward 0 ω))) :=
    condDistrib_comp E hW ((IT.measurable_action 0).prodMk (IT.measurable_reward 0))
  have h_comp_action : ⇑(condDistrib (A 0) E P) =ᶠ[ae (P.map E)]
      ⇑((condDistrib W E P).map (IT.action 0)) :=
    condDistrib_comp E hW (IT.measurable_action 0)
  have h_swap_eq := h_swap.condDistrib_eq
  rw [(compProd_map_condDistrib (h.measurable_A 0).aemeasurable).symm] at h_swap_eq
  filter_upwards [h_prod, h_comp_pair, h_comp_action,
    (Measure.ae_compProd_iff (Kernel.measurableSet_eq _ _)).mp h_swap_eq]
    with e h_prod_e h_pair_e h_act_e h_nested_e
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
  rw [← Kernel.map_apply _ (by fun_prop), ← h_pair_e]
  conv_rhs => rw [← Kernel.map_apply _ (IT.measurable_action 0), ← h_act_e]
  rw [h_prod_e, Kernel.compProd_apply_eq_compProd_sectR]
  refine Measure.compProd_congr ?_
  filter_upwards [h_nested_e] with a ha
  ext s _
  rw [Kernel.sectR_apply, Kernel.comap_apply, ha, Kernel.comap_apply]; rfl

lemma hasCondDistrib_action_fiber (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    ∀ᵐ e ∂Q, HasCondDistrib (IT.action (n + 1))
      (IsAlgEnvSeq.hist IT.action IT.reward n) (alg.policy n)
      (condDistrib (fun ω n ↦ (A n ω, R' n ω)) E P e) := by
  rw [← h.hasLaw_env.map_eq]
  set W := fun ω n ↦ (A n ω, R' n ω)
  have hW : AEMeasurable W P :=
    (measurable_pi_lambda _ fun n ↦ (h.measurable_A n).prodMk (h.measurable_R n)).aemeasurable
  have h_hist_meas := IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n
  have h_prod := condDistrib_prod_left h_hist_meas.aemeasurable
    (h.measurable_A (n + 1)).aemeasurable h.measurable_E.aemeasurable (μ := P)
  have h_action_env := (h.hasCondDistrib_action n).condDistrib_eq
  have h_hist_IT_meas : Measurable
      (IsAlgEnvSeq.hist (IT.action (R := R)) (IT.reward (α := α)) n) :=
    IsAlgEnvSeq.measurable_hist (fun n ↦ IT.measurable_action n) (fun n ↦ IT.measurable_reward n) n
  have h_comp_pair : ⇑(condDistrib (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω)) E P)
      =ᶠ[ae (P.map E)] ⇑((condDistrib W E P).map
        (fun ω ↦ (IsAlgEnvSeq.hist IT.action IT.reward n ω, IT.action (n + 1) ω))) :=
    condDistrib_comp E hW (h_hist_IT_meas.prodMk (IT.measurable_action (n + 1)))
  have h_comp_hist : ⇑(condDistrib (IsAlgEnvSeq.hist A R' n) E P) =ᶠ[ae (P.map E)]
      ⇑((condDistrib W E P).map (IsAlgEnvSeq.hist IT.action IT.reward n)) :=
    condDistrib_comp E hW h_hist_IT_meas
  rw [(compProd_map_condDistrib h_hist_meas.aemeasurable).symm] at h_action_env
  filter_upwards [h_prod, h_comp_pair, h_comp_hist,
    (Measure.ae_compProd_iff (Kernel.measurableSet_eq _ _)).mp h_action_env]
    with e h_prod_e h_pair_e h_hist_e h_nested_e
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
  rw [← Kernel.map_apply _ (h_hist_IT_meas.prodMk (IT.measurable_action (n + 1))),
    ← h_pair_e]
  conv_rhs => rw [← Kernel.map_apply _ h_hist_IT_meas, ← h_hist_e]
  rw [h_prod_e, Kernel.compProd_apply_eq_compProd_sectR]
  refine Measure.compProd_congr ?_
  filter_upwards [h_nested_e] with _ ha
  ext s _
  rw [Kernel.sectR_apply, ha, Kernel.prodMkLeft_apply]

lemma hasCondDistrib_reward_fiber [IsFiniteKernel κ]
    (h : IsBayesAlgEnvSeq Q κ alg E A R' P) (n : ℕ) :
    ∀ᵐ e ∂Q, HasCondDistrib (IT.reward (n + 1))
      (fun f ↦ (IsAlgEnvSeq.hist IT.action IT.reward n f, IT.action (n + 1) f))
      ((κ.comap (·, e) (by fun_prop)).prodMkLeft _)
      (condDistrib (fun ω n ↦ (A n ω, R' n ω)) E P e) := by
  rw [← h.hasLaw_env.map_eq]
  set W := fun ω n ↦ (A n ω, R' n ω)
  have hW : AEMeasurable W P :=
    (measurable_pi_lambda _ fun n ↦ (h.measurable_A n).prodMk (h.measurable_R n)).aemeasurable
  have h_hist_meas := IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n
  have h_prod := condDistrib_prod_left
    (Measurable.prodMk h_hist_meas (h.measurable_A (n + 1))).aemeasurable
    (h.measurable_R (n + 1)).aemeasurable h.measurable_E.aemeasurable (μ := P)
  have h_swap : HasCondDistrib (R' (n + 1))
      (fun ω ↦ (E ω, IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
      (κ.comap (fun p ↦ (p.2.2, p.1)) (by fun_prop)) P :=
    (h.hasCondDistrib_reward n).comp_right
      (MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm)
  have h_swap_eq := h_swap.condDistrib_eq
  have h_hist_IT_meas : Measurable
      (IsAlgEnvSeq.hist (IT.action (R := R)) (IT.reward (α := α)) n) :=
    IsAlgEnvSeq.measurable_hist (fun n ↦ IT.measurable_action n) (fun n ↦ IT.measurable_reward n) n
  have h_pair_meas := h_hist_IT_meas.prodMk (IT.measurable_action (n + 1))
  have h_comp_triple : ⇑(condDistrib
      (fun ω ↦ ((IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω), R' (n + 1) ω)) E P)
      =ᶠ[ae (P.map E)] ⇑((condDistrib W E P).map
        (fun ω ↦ ((IsAlgEnvSeq.hist IT.action IT.reward n ω, IT.action (n + 1) ω),
          IT.reward (n + 1) ω))) :=
    condDistrib_comp E hW (h_pair_meas.prodMk (IT.measurable_reward (n + 1)))
  have h_comp_pair : ⇑(condDistrib (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω)) E P)
      =ᶠ[ae (P.map E)] ⇑((condDistrib W E P).map
        (fun ω ↦ (IsAlgEnvSeq.hist IT.action IT.reward n ω, IT.action (n + 1) ω))) :=
    condDistrib_comp E hW h_pair_meas
  rw [(compProd_map_condDistrib (Measurable.prodMk h_hist_meas
    (h.measurable_A (n + 1))).aemeasurable).symm] at h_swap_eq
  filter_upwards [h_prod, h_comp_triple, h_comp_pair,
    (Measure.ae_compProd_iff (Kernel.measurableSet_eq _ _)).mp h_swap_eq]
    with e h_prod_e h_triple_e h_pair_e h_nested_e
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
  rw [← Kernel.map_apply _ (h_pair_meas.prodMk (IT.measurable_reward (n + 1))), ← h_triple_e]
  conv_rhs => rw [← Kernel.map_apply _ h_pair_meas, ← h_pair_e]
  rw [h_prod_e, Kernel.compProd_apply_eq_compProd_sectR]
  refine Measure.compProd_congr ?_
  filter_upwards [h_nested_e] with _ ha
  ext s _
  rw [Kernel.sectR_apply, ha, Kernel.comap_apply, Kernel.prodMkLeft_apply, Kernel.comap_apply]

lemma condDistrib_traj_isAlgEnvSeq [IsMarkovKernel κ] (h : IsBayesAlgEnvSeq Q κ alg E A R' P) :
    ∀ᵐ e ∂Q, IsAlgEnvSeq IT.action IT.reward alg (stationaryEnv (κ.comap (·, e) (by fun_prop)))
      (condDistrib (fun ω n ↦ (A n ω, R' n ω)) E P e) := by
  filter_upwards [hasLaw_action_zero_fiber h,
    hasCondDistrib_reward_zero_fiber h,
    ae_all_iff.2 (hasCondDistrib_action_fiber h),
    ae_all_iff.2 (hasCondDistrib_reward_fiber h)]
    with _ h_law h_r0 h_a h_r
  exact {
    hasLaw_action_zero := h_law
    hasCondDistrib_reward_zero := h_r0
    hasCondDistrib_action := h_a
    hasCondDistrib_reward := h_r
  }

end Laws

section Real

noncomputable
def actionMean (κ : Kernel (α × 𝓔) ℝ) (E : Ω → 𝓔) (a : α) (ω : Ω) : ℝ := (κ (a, E ω))[id]

@[fun_prop]
lemma measurable_actionMean {κ : Kernel (α × 𝓔) ℝ} {E : Ω → 𝓔} {a : α} (hE : Measurable E) :
    Measurable (actionMean κ E a) :=
  stronglyMeasurable_id.integral_kernel.measurable.comp (by fun_prop)

noncomputable
def bestAction [Fintype α] [Encodable α] [Nonempty α] [MeasurableSingletonClass α]
    (κ : Kernel (α × 𝓔) ℝ) (E : Ω → 𝓔) (ω : Ω) : α :=
  measurableArgmax (fun ω' a ↦ actionMean κ E a ω') ω

@[fun_prop]
lemma measurable_bestAction [Fintype α] [Encodable α] [Nonempty α] [MeasurableSingletonClass α]
    {κ : Kernel (α × 𝓔) ℝ} {E : Ω → 𝓔} (hE : Measurable E) : Measurable (bestAction κ E) :=
  measurable_measurableArgmax (by fun_prop)

noncomputable
def regret (κ : Kernel (α × 𝓔) ℝ) (E : Ω → 𝓔) (A : ℕ → Ω → α) (t : ℕ) (ω : Ω) : ℝ :=
  Bandits.regret (κ.comap (·, E ω) (by fun_prop)) A t ω

end Real

end IsBayesAlgEnvSeq

section StationaryEquivalence

noncomputable
def bayesStationaryEnv (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (α × 𝓔) R)
    [IsMarkovKernel κ] : Environment α (𝓔 × R) where
  feedback n :=
    let g : (Iic n → α × 𝓔 × R) × α → α × 𝓔 := fun (h, a) => (a, (h ⟨0, by simp⟩).2.1)
    (Kernel.deterministic (Prod.snd ∘ g) (by fun_prop)) ×ₖ (κ.comap g (by fun_prop))
  ν0 := (Kernel.const _ Q) ⊗ₖ κ

/-- Bridge theorem: an `IsAlgEnvSeq` for `(alg.prod_left E)` and `(bayesStationaryEnv Q κ)`
gives rise to an `IsBayesAlgEnvSeq`. -/
theorem IsAlgEnvSeq.toIsBayesAlgEnvSeq
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace 𝓔] [Nonempty 𝓔]
    [StandardBorelSpace R] [Nonempty R]
    {Q : Measure 𝓔} [IsProbabilityMeasure Q] {κ : Kernel (α × 𝓔) R} [IsMarkovKernel κ]
    {A : ℕ → Ω → α} {R'' : ℕ → Ω → 𝓔 × R} {alg : Algorithm α R}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq A R'' (alg.prod_left 𝓔) (bayesStationaryEnv Q κ) P) :
    IsBayesAlgEnvSeq Q κ alg (fun ω ↦ (R'' 0 ω).1) A (fun n ω ↦ (R'' n ω).2) P where
  measurable_E := (h.measurable_R 0).fst
  measurable_A := h.measurable_A
  measurable_R n := (h.measurable_R n).snd
  hasLaw_env := by
    apply HasCondDistrib.hasLaw_of_const
    simpa [bayesStationaryEnv] using h.hasCondDistrib_reward_zero.fst
  hasCondDistrib_action_zero := by
    have hfst : HasCondDistrib (fun ω ↦ (R'' 0 ω).1) (A 0) (Kernel.const α Q) P := by
      simpa [bayesStationaryEnv] using h.hasCondDistrib_reward_zero.fst
    -- E' | A 0 is constant Q = P.map E', so A 0 and E' are independent
    have h_indep : IndepFun (A 0) (fun ω ↦ (R'' 0 ω).1) P := by
      rw [indepFun_iff_condDistrib_eq_const (h.measurable_A 0).aemeasurable
        (h.measurable_R 0).fst.aemeasurable, hfst.hasLaw_of_const.map_eq]
      exact hfst.condDistrib_eq
    -- From independence: condDistrib (A 0) E' P = const (P.map (A 0)) = const alg.p0
    have hcd := condDistrib_of_indepFun h_indep.symm (h.measurable_R 0).fst.aemeasurable
      (h.measurable_A 0).aemeasurable
    simp only [h.hasLaw_action_zero.map_eq, Algorithm.prod_left] at hcd
    exact ⟨(h.measurable_A 0).aemeasurable, (h.measurable_R 0).fst.aemeasurable, hcd⟩
  hasCondDistrib_reward_zero := by
    simpa [bayesStationaryEnv] using h.hasCondDistrib_reward_zero.of_compProd
  hasCondDistrib_action n := by
    let f : (Iic n → α × 𝓔 × R) → 𝓔 × (Iic n → α × R) :=
      fun h ↦ ((h ⟨0, by simp⟩).2.1, fun i ↦ ((h i).1, (h i).2.2))
    suffices h' : HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R'' n)
        (((alg.policy n).comap Prod.snd (by fun_prop)).comap f (by fun_prop)) P from
      h'.comp_left (f := f)
    exact h.hasCondDistrib_action n
  hasCondDistrib_reward n := by
    let f : (Iic n → α × 𝓔 × R) × α → (Iic n → α × R) × α × 𝓔 :=
      fun p ↦ ((fun i ↦ ((p.1 i).1, (p.1 i).2.2)), p.2, (p.1 ⟨0, by simp⟩).2.1)
    have hf : Measurable f := by fun_prop
    suffices h' : HasCondDistrib (fun ω ↦ (R'' (n + 1) ω).2)
        (fun ω ↦ (IsAlgEnvSeq.hist A R'' n ω, A (n + 1) ω))
        ((κ.comap Prod.snd (by fun_prop)).comap f hf) P from h'.comp_left hf
    simpa [bayesStationaryEnv, Kernel.snd_prod] using (h.hasCondDistrib_reward n).snd

namespace IT

noncomputable
def bayesTrajMeasure (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (α × 𝓔) R)
    [IsMarkovKernel κ] (alg : Algorithm α R) : Measure (ℕ → α × 𝓔 × R) :=
  trajMeasure (alg.prod_left 𝓔) (bayesStationaryEnv Q κ)
deriving IsProbabilityMeasure

lemma isBayesAlgEnvSeq_bayesianTrajMeasure
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace 𝓔] [Nonempty 𝓔]
    [StandardBorelSpace R] [Nonempty R]
    (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (α × 𝓔) R) [IsMarkovKernel κ]
    (alg : Algorithm α R) :
    IsBayesAlgEnvSeq Q κ alg (fun ω ↦ (ω 0).2.1) action (fun n ω ↦ (ω n).2.2)
       (bayesTrajMeasure Q κ alg) :=
  (isAlgEnvSeq_trajMeasure _ _).toIsBayesAlgEnvSeq

/-- The conditional distribution over the best arm given the observed history. -/
noncomputable
def posteriorBestArm [StandardBorelSpace α] [Nonempty α] [Fintype α] [Encodable α]
    (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (α × 𝓔) ℝ) [IsMarkovKernel κ]
    (alg : Algorithm α ℝ) (n : ℕ) : Kernel (Iic n → α × ℝ) α :=
  condDistrib (IsBayesAlgEnvSeq.bestAction κ (fun ω ↦ (ω 0).2.1))
    (IsAlgEnvSeq.hist action (fun n ω ↦ (ω n).2.2) n)
    (bayesTrajMeasure Q κ alg)
deriving IsMarkovKernel

/-- The initial distribution over the best arm. -/
noncomputable
def priorBestArm [StandardBorelSpace α] [Nonempty α] [Fintype α] [Encodable α]
    (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (α × 𝓔) ℝ) [IsMarkovKernel κ]
    (alg : Algorithm α ℝ) : Measure α :=
  (bayesTrajMeasure Q κ alg).map (IsBayesAlgEnvSeq.bestAction κ (fun ω ↦ (ω 0).2.1))

instance [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace 𝓔] [Nonempty 𝓔] [Fintype α]
    [Encodable α] (Q : Measure 𝓔) [IsProbabilityMeasure Q] (κ : Kernel (α × 𝓔) ℝ)
 [IsMarkovKernel κ] (alg : Algorithm α ℝ) : IsProbabilityMeasure (priorBestArm Q κ alg) :=
  Measure.isProbabilityMeasure_map (by fun_prop)

end IT

end StationaryEquivalence

end Learning
