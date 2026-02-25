/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.FullSupport
import LeanBandits.ForMathlib.WithDensity
import LeanBandits.SequentialLearning.BayesStationaryEnv

open MeasureTheory ProbabilityTheory Finset Preorder

open scoped ENNReal NNReal

namespace Learning

variable {α : Type*} {R : Type*} [MeasurableSpace α] [MeasurableSpace R]

section HistoryDensity

variable [MeasurableSpace.CountablyGenerated α]

/-- The density of the history distribution under `alg` w.r.t. a positive reference algorithm.
This density depends only on the algorithm's action probabilities, not on the reward kernel. -/
noncomputable def historyDensity
    (alg alg₀ : Algorithm α R) :
    (t : ℕ) → (Iic t → α × R) → ℝ≥0∞
  | 0 => (alg.p0.rnDeriv alg₀.p0 ∘ Prod.fst) ∘
        MeasurableEquiv.piUnique (fun _ : Iic (0 : ℕ) => α × R)
  | n + 1 =>
    let σ : (Iic n → α × R) → (α × R) → ℝ≥0∞ :=
      fun h ar => Kernel.rnDeriv (alg.policy n)
        (alg₀.policy n) h ar.1
    (historyDensity alg alg₀ n ∘ Prod.fst * Function.uncurry σ) ∘
      MeasurableEquiv.IicSuccProd (fun _ : ℕ => α × R) n

@[fun_prop]
lemma measurable_historyDensity (alg alg₀ : Algorithm α R) (t : ℕ) :
    Measurable (historyDensity alg alg₀ t) := by
  induction t with
  | zero =>
    exact (Measure.measurable_rnDeriv _ _).comp
      (measurable_fst.comp (MeasurableEquiv.piUnique _).measurable)
  | succ n ih =>
    exact ((ih.comp measurable_fst).mul
      ((Kernel.measurable_rnDeriv _ _).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).comp
      (MeasurableEquiv.IicSuccProd _ n).measurable

lemma historyDensity_ne_top (alg alg₀ : Algorithm α R)
    (hpos : alg₀.IsPositive) (t : ℕ)
    (h : Iic t → α × R) : historyDensity alg alg₀ t h ≠ ⊤ := by
  induction t with
  | zero => exact rnDeriv_ne_top_of_forall_singleton_pos hpos.1 _
  | succ n ih =>
    exact ENNReal.mul_ne_top (ih _)
      (kernel_rnDeriv_ne_top_of_forall_singleton_pos
        (fun h' a => hpos.2 n h' a) _ _)

end HistoryDensity

/-- The step kernel for a stationary environment under a positive algorithm absolutely
    continuously dominates any other algorithm's step kernel. -/
lemma Algorithm.IsPositive.absolutelyContinuous_stepKernel_stationary
    {alg₀ : Algorithm α R} (hpos : alg₀.IsPositive)
    (alg : Algorithm α R) (ν : Kernel α R) [IsMarkovKernel ν]
    (n : ℕ) (h : Iic n → α × R) :
    stepKernel alg (stationaryEnv ν) n h ≪
    stepKernel alg₀ (stationaryEnv ν) n h := by
  have h1 : stepKernel alg (stationaryEnv ν) n h = (alg.policy n h) ⊗ₘ ν := by
    simp only [stepKernel, stationaryEnv]; ext s hs
    simp only [Kernel.compProd_apply hs, Measure.compProd_apply hs, Kernel.prodMkLeft_apply]
  have h2 : stepKernel alg₀ (stationaryEnv ν) n h =
      (alg₀.policy n h) ⊗ₘ ν := by
    simp only [stepKernel, stationaryEnv]; ext s hs
    simp only [Kernel.compProd_apply hs, Measure.compProd_apply hs, Kernel.prodMkLeft_apply]
  rw [h1, h2]
  exact Measure.AbsolutelyContinuous.compProd_left
    (absolutelyContinuous_of_forall_singleton_pos (hpos.2 n h)) _

namespace IsAlgEnvSeq

variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]

/-- The history distribution at time `n + 1` decomposes as a compProd of the history at time `n`
    and the step kernel, composed with `IicSuccProd.symm`. -/
lemma map_hist_succ_eq_compProd_map
    {Ω : Type*} [MeasurableSpace Ω]
    {A : ℕ → Ω → α} {R' : ℕ → Ω → R}
    {alg : Algorithm α R} {env : Environment α R}
    {P : Measure Ω} [IsFiniteMeasure P]
    (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) :
    P.map (IsAlgEnvSeq.hist A R' (n + 1)) =
    (P.map (IsAlgEnvSeq.hist A R' n) ⊗ₘ stepKernel alg env n).map
      (MeasurableEquiv.IicSuccProd (fun _ : ℕ => α × R) n).symm := by
  set e := MeasurableEquiv.IicSuccProd (fun _ : ℕ => α × R) n
  have hA := h.measurable_A; have hR := h.measurable_R
  have h_func : IsAlgEnvSeq.hist A R' (n + 1) = e.symm ∘
      (fun ω => (IsAlgEnvSeq.hist A R' n ω, IsAlgEnvSeq.step A R' (n + 1) ω)) := by
    funext ω; simp only [Function.comp_apply]
    change frestrictLe (n + 1) (fun k => IsAlgEnvSeq.step A R' k ω) =
      e.symm (frestrictLe n (fun k => IsAlgEnvSeq.step A R' k ω),
              IsAlgEnvSeq.step A R' (n + 1) ω)
    change frestrictLe (n + 1) (fun k => IsAlgEnvSeq.step A R' k ω) =
      e.symm (e (frestrictLe (n + 1) (fun k => IsAlgEnvSeq.step A R' k ω)))
    rw [e.symm_apply_apply]
  rw [h_func, (Measure.map_map e.symm.measurable
    ((IsAlgEnvSeq.measurable_hist hA hR n).prodMk
      (IsAlgEnvSeq.measurable_step (n + 1) (hA _) (hR _)))).symm]
  congr 1
  have h_cd := h.hasCondDistrib_step n
  exact ((condDistrib_ae_eq_iff_measure_eq_compProd _
    (IsAlgEnvSeq.measurable_step (n + 1) (hA _) (hR _)).aemeasurable
    (stepKernel alg env n)).mp h_cd.condDistrib_eq)

variable {ν : Kernel α R} [IsMarkovKernel ν]
variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : ℕ → Ω → α} {R' : ℕ → Ω → R}
variable {alg : Algorithm α R}
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {alg₀ : Algorithm α R}
variable {Ω₀ : Type*} [MeasurableSpace Ω₀]
variable {A₀ : ℕ → Ω₀ → α} {R₀ : ℕ → Ω₀ → R}
variable {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

/-- The history distribution under any algorithm is absolutely continuous w.r.t. the
    history distribution under a positive reference algorithm,
    for a stationary environment. -/
lemma absolutelyContinuous_map_hist_stationary
    (h : IsAlgEnvSeq A R' alg (stationaryEnv ν) P)
    (hpos : alg₀.IsPositive)
    (h₀ : IsAlgEnvSeq A₀ R₀ alg₀ (stationaryEnv ν) P₀)
    (t : ℕ) :
    P.map (IsAlgEnvSeq.hist A R' t) ≪ P₀.map (IsAlgEnvSeq.hist A₀ R₀ t) := by
  induction t with
  | zero =>
    set e := MeasurableEquiv.piUnique (fun _ : Iic (0 : ℕ) => α × R)
    have h_hist : IsAlgEnvSeq.hist A R' 0 = e.symm ∘ IsAlgEnvSeq.step A R' 0 := by
      funext ω ⟨i, hi⟩; have : i = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp hi); subst this; rfl
    have h_hist₀ : IsAlgEnvSeq.hist A₀ R₀ 0 = e.symm ∘ IsAlgEnvSeq.step A₀ R₀ 0 := by
      funext ω ⟨i, hi⟩; have : i = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp hi); subst this; rfl
    rw [h_hist, h_hist₀,
        ← Measure.map_map e.symm.measurable
          (IsAlgEnvSeq.measurable_step 0 (h.measurable_A _) (h.measurable_R _)),
        ← Measure.map_map e.symm.measurable
          (IsAlgEnvSeq.measurable_step 0 (h₀.measurable_A _) (h₀.measurable_R _)),
        h.hasLaw_step_zero.map_eq, h₀.hasLaw_step_zero.map_eq]
    simp only [stationaryEnv_ν0]
    exact (Measure.AbsolutelyContinuous.compProd_left
      (absolutelyContinuous_of_forall_singleton_pos hpos.1) _).map
      e.symm.measurable
  | succ n ih =>
    rw [h.map_hist_succ_eq_compProd_map, h₀.map_hist_succ_eq_compProd_map]
    exact (Measure.AbsolutelyContinuous.compProd ih
      (Filter.Eventually.of_forall fun x =>
        hpos.absolutelyContinuous_stepKernel_stationary alg ν n x)).map
      (MeasurableEquiv.IicSuccProd _ n).symm.measurable

/-- The history distribution under any algorithm equals the positive reference algorithm's history
distribution weighted by `historyDensity`, for any stationary environment. -/
lemma map_hist_eq_withDensity_historyDensity
    (h : IsAlgEnvSeq A R' alg (stationaryEnv ν) P)
    (hpos : alg₀.IsPositive) (t : ℕ)
    (h₀ : IsAlgEnvSeq A₀ R₀ alg₀ (stationaryEnv ν) P₀) :
    P.map (IsAlgEnvSeq.hist A R' t) =
    (P₀.map (IsAlgEnvSeq.hist A₀ R₀ t)).withDensity (historyDensity alg alg₀ t) := by
  induction t with
  | zero =>
    set e := MeasurableEquiv.piUnique (fun _ : Iic (0 : ℕ) => α × R)
    have h_ac : alg.p0 ≪ alg₀.p0 :=
      absolutelyContinuous_of_forall_singleton_pos hpos.1
    have h_hist : IsAlgEnvSeq.hist A R' 0 = e.symm ∘ IsAlgEnvSeq.step A R' 0 := by
      funext ω ⟨i, hi⟩
      have : i = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp hi); subst this; rfl
    have h_hist₀ : IsAlgEnvSeq.hist A₀ R₀ 0 = e.symm ∘ IsAlgEnvSeq.step A₀ R₀ 0 := by
      funext ω ⟨i, hi⟩
      have : i = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp hi); subst this; rfl
    rw [h_hist, h_hist₀,
        ← Measure.map_map e.symm.measurable
          (IsAlgEnvSeq.measurable_step 0 (h.measurable_A _) (h.measurable_R _)),
        ← Measure.map_map e.symm.measurable
          (IsAlgEnvSeq.measurable_step 0 (h₀.measurable_A _) (h₀.measurable_R _)),
        h.hasLaw_step_zero.map_eq, h₀.hasLaw_step_zero.map_eq]
    simp only [stationaryEnv_ν0]
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ h_ac]
    rw [withDensity_compProd_left (Measure.measurable_rnDeriv _ _)]
    exact withDensity_map_equiv_symm
      ((Measure.measurable_rnDeriv _ _).comp measurable_fst)
  | succ n ih =>
    let σ : (Iic n → α × R) → (α × R) → ℝ≥0∞ :=
      fun x ar => Kernel.rnDeriv (alg.policy n) (alg₀.policy n) x ar.1
    have hσ_meas : Measurable (Function.uncurry σ) :=
      (Kernel.measurable_rnDeriv _ _).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h_step : stepKernel alg (stationaryEnv ν) n =
        (stepKernel alg₀ (stationaryEnv ν) n).withDensity σ := by
      ext x : 1
      rw [Kernel.withDensity_apply _ hσ_meas]
      have h_alg : stepKernel alg (stationaryEnv ν) n x = (alg.policy n x) ⊗ₘ ν := by
        ext s hs
        simp only [stepKernel, stationaryEnv, Kernel.compProd_apply hs,
          Measure.compProd_apply hs, Kernel.prodMkLeft_apply]
      have h_alg₀ : stepKernel alg₀ (stationaryEnv ν) n x = (alg₀.policy n x) ⊗ₘ ν := by
        ext s hs
        simp only [stepKernel, stationaryEnv, Kernel.compProd_apply hs,
          Measure.compProd_apply hs, Kernel.prodMkLeft_apply]
      have h_wd : ((alg₀.policy n) x).withDensity
          (Kernel.rnDeriv (alg.policy n) (alg₀.policy n) x) = alg.policy n x := by
        rw [← Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _)]
        exact Kernel.withDensity_rnDeriv_eq (κ := alg.policy n) (η := alg₀.policy n)
          (absolutelyContinuous_of_forall_singleton_pos (hpos.2 n x))
      rw [h_alg, h_alg₀, ← h_wd]
      haveI : SFinite ((alg₀.policy n x).withDensity
          (Kernel.rnDeriv (alg.policy n) (alg₀.policy n) x)) := by
        rw [h_wd]; infer_instance
      exact withDensity_compProd_left
        (Kernel.measurable_rnDeriv (alg.policy n) (alg₀.policy n)).of_uncurry_left
    haveI : IsSFiniteKernel ((stepKernel alg₀ (stationaryEnv ν) n).withDensity σ) := by
      rw [← h_step]; infer_instance
    rw [h.map_hist_succ_eq_compProd_map n,
        h₀.map_hist_succ_eq_compProd_map n,
        ih, h_step,
        withDensity_compProd_withDensity (measurable_historyDensity alg alg₀ n) hσ_meas]
    exact withDensity_map_equiv_symm
      (((measurable_historyDensity alg alg₀ n).comp measurable_fst).mul hσ_meas)

end IsAlgEnvSeq

namespace IsBayesAlgEnvSeq

variable {𝓔 : Type*} [MeasurableSpace 𝓔]
variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
variable {Q : Measure 𝓔} [IsProbabilityMeasure Q]
variable {κ : Kernel (𝓔 × α) R}

variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : Ω → 𝓔} {A : ℕ → Ω → α} {R' : ℕ → Ω → R}
variable {alg : Algorithm α R}
variable {P : Measure Ω} [IsProbabilityMeasure P]
variable {alg₀ : Algorithm α R}
variable {Ω₀ : Type*} [MeasurableSpace Ω₀]
variable {E₀ : Ω₀ → 𝓔} {A₀ : ℕ → Ω₀ → α} {R₀ : ℕ → Ω₀ → R}
variable {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

/-- The history distribution under any algorithm is absolutely continuous w.r.t. the
    history distribution under a positive reference algorithm. -/
lemma absolutelyContinuous_map_hist
    [IsMarkovKernel κ] [StandardBorelSpace Ω] [Nonempty Ω]
    [StandardBorelSpace Ω₀] [Nonempty Ω₀]
    (h : IsBayesAlgEnvSeq Q κ alg E A R' P)
    (hpos : alg₀.IsPositive)
    (h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ R₀ P₀)
    (t : ℕ) :
    P.map (IsAlgEnvSeq.hist A R' t) ≪
    P₀.map (IsAlgEnvSeq.hist A₀ R₀ t) := by
  set κ_alg := condDistrib (IsAlgEnvSeq.hist A R' t) E P
  set κ₀ := condDistrib (IsAlgEnvSeq.hist A₀ R₀ t) E₀ P₀
  rw [h.map_hist_eq_condDistrib_comp t, h₀.map_hist_eq_condDistrib_comp t,
    ← Measure.snd_compProd, ← Measure.snd_compProd]
  have hW_meas : Measurable (fun (ω : Ω) (n : ℕ) => (A n ω, R' n ω)) :=
    measurable_pi_lambda _ fun n => (h.measurable_A n).prodMk (h.measurable_R n)
  have hW₀_meas : Measurable (fun (ω : Ω₀) (n : ℕ) => (A₀ n ω, R₀ n ω)) :=
    measurable_pi_lambda _ fun n => (h₀.measurable_A n).prodMk (h₀.measurable_R n)
  exact (Measure.AbsolutelyContinuous.compProd_right
    (show ∀ᵐ e ∂Q, κ_alg e ≪ κ₀ e from by
      have h_IT_hist : (IsAlgEnvSeq.hist IT.action IT.reward t :
          (ℕ → α × R) → (Iic t → α × R)) = IT.hist t :=
        funext fun ω => funext fun i => Prod.mk.eta
      have h_cd : ∀ᵐ e ∂Q, κ_alg e =
          (condDistrib (fun ω n => (A n ω, R' n ω)) E P e).map (IT.hist t) := by
        rw [← h.hasLaw_env.map_eq]
        have h_comp : κ_alg
            =ᵐ[P.map E] (condDistrib (fun ω n => (A n ω, R' n ω)) E P).map (IT.hist t) :=
          condDistrib_comp E hW_meas.aemeasurable (IT.measurable_hist t)
        filter_upwards [h_comp] with e he
        rw [he, Kernel.map_apply _ (IT.measurable_hist t)]
      have h_cd₀ : ∀ᵐ e ∂Q, κ₀ e =
          (condDistrib (fun ω n => (A₀ n ω, R₀ n ω)) E₀ P₀ e).map (IT.hist t) := by
        rw [← h₀.hasLaw_env.map_eq]
        have h_comp : κ₀
            =ᵐ[P₀.map E₀] (condDistrib (fun ω n => (A₀ n ω, R₀ n ω)) E₀ P₀).map (IT.hist t) :=
          condDistrib_comp E₀ hW₀_meas.aemeasurable (IT.measurable_hist t)
        filter_upwards [h_comp] with e he
        rw [he, Kernel.map_apply _ (IT.measurable_hist t)]
      have hae := h.ae_IsAlgEnvSeq
      have hae₀ := h₀.ae_IsAlgEnvSeq
      filter_upwards [h_cd, h_cd₀, hae, hae₀] with e he he₀ hae hae₀
      rw [he, he₀, ← h_IT_hist]
      exact hae.absolutelyContinuous_map_hist_stationary hpos hae₀ t)).map
    measurable_snd

variable [StandardBorelSpace 𝓔] [Nonempty 𝓔] [IsMarkovKernel κ]

/-- The posterior on the environment given history is algorithm-independent. -/
lemma condDistrib_env_hist_alg_indep
    (h : IsBayesAlgEnvSeq Q κ alg E A R' P)
    (hpos : alg₀.IsPositive)
    (h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ R₀ P₀)
    (t : ℕ) :
    condDistrib E (IsAlgEnvSeq.hist A R' t) P
      =ᵐ[P.map (IsAlgEnvSeq.hist A R' t)]
    condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ t) P₀ := by
  set κ_alg := condDistrib (IsAlgEnvSeq.hist A R' t) E P
  set κ₀ := condDistrib (IsAlgEnvSeq.hist A₀ R₀ t) E₀ P₀
  set ρ := historyDensity alg alg₀ t
  have hρ_meas := measurable_historyDensity alg alg₀ t
  have hρ_ne_top := historyDensity_ne_top alg alg₀ hpos t
  have hW_meas : Measurable (fun (ω : Ω) (n : ℕ) => (A n ω, R' n ω)) :=
    measurable_pi_lambda _ fun n => (h.measurable_A n).prodMk (h.measurable_R n)
  have hW₀_meas : Measurable (fun (ω : Ω₀) (n : ℕ) => (A₀ n ω, R₀ n ω)) :=
    measurable_pi_lambda _ fun n => (h₀.measurable_A n).prodMk (h₀.measurable_R n)
  -- Key factorization: κ_alg =ᵐ[Q] κ₀.withDensity (fun _ => ρ)
  have h_wd_ae : κ_alg =ᵐ[Q] κ₀.withDensity (fun _ => ρ) := by
    have h_IT_hist : (IsAlgEnvSeq.hist IT.action IT.reward t :
        (ℕ → α × R) → (Iic t → α × R)) = IT.hist t :=
      funext fun ω => funext fun i => Prod.mk.eta
    have h_cd : ∀ᵐ e ∂Q, κ_alg e =
        (condDistrib (fun ω n => (A n ω, R' n ω)) E P e).map (IT.hist t) := by
      rw [← h.hasLaw_env.map_eq]
      have h_comp : κ_alg
          =ᵐ[P.map E] (condDistrib (fun ω n => (A n ω, R' n ω)) E P).map (IT.hist t) :=
        condDistrib_comp E hW_meas.aemeasurable (IT.measurable_hist t)
      filter_upwards [h_comp] with e he
      rw [he, Kernel.map_apply _ (IT.measurable_hist t)]
    have h_cd₀ : ∀ᵐ e ∂Q, κ₀ e =
        (condDistrib (fun ω n => (A₀ n ω, R₀ n ω)) E₀ P₀ e).map (IT.hist t) := by
      rw [← h₀.hasLaw_env.map_eq]
      have h_comp : κ₀
          =ᵐ[P₀.map E₀] (condDistrib (fun ω n => (A₀ n ω, R₀ n ω)) E₀ P₀).map (IT.hist t) :=
        condDistrib_comp E₀ hW₀_meas.aemeasurable (IT.measurable_hist t)
      filter_upwards [h_comp] with e he
      rw [he, Kernel.map_apply _ (IT.measurable_hist t)]
    have hae := h.ae_IsAlgEnvSeq
    have hae₀ := h₀.ae_IsAlgEnvSeq
    filter_upwards [h_cd, h_cd₀, hae, hae₀] with e he he₀ hae hae₀
    rw [Kernel.withDensity_apply _
      (show Measurable (Function.uncurry (fun (_ : 𝓔) => ρ)) from hρ_meas.comp measurable_snd),
      he, he₀, ← h_IT_hist]
    exact hae.map_hist_eq_withDensity_historyDensity hpos t hae₀
  haveI : IsSFiniteKernel (κ₀.withDensity (fun _ => ρ)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ b => hρ_ne_top b)
  -- Direct condDistrib equality via joint measure argument
  have h_joint : P.map (fun ω => (E ω, IsAlgEnvSeq.hist A R' t ω)) = Q ⊗ₘ κ_alg := by
    rw [← h.hasLaw_env.map_eq]
    exact (compProd_map_condDistrib
      (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R t).aemeasurable).symm
  have h_joint₀ : P₀.map (fun ω => (E₀ ω, IsAlgEnvSeq.hist A₀ R₀ t ω)) = Q ⊗ₘ κ₀ := by
    rw [← h₀.hasLaw_env.map_eq]
    exact (compProd_map_condDistrib
      (IsAlgEnvSeq.measurable_hist h₀.measurable_A h₀.measurable_R t).aemeasurable).symm
  have h_meas_hist := IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R t
  have h_meas_hist₀ := IsAlgEnvSeq.measurable_hist h₀.measurable_A h₀.measurable_R t
  -- P.map hist = (P₀.map hist₀).withDensity ρ
  have h_hist : P.map (IsAlgEnvSeq.hist A R' t)
      = (P₀.map (IsAlgEnvSeq.hist A₀ R₀ t)).withDensity ρ := by
    have h_marg : P.map (IsAlgEnvSeq.hist A R' t) = (Q ⊗ₘ κ_alg).map Prod.snd := by
      rw [← h_joint]
      exact (Measure.map_map measurable_snd (h.measurable_E.prodMk h_meas_hist)).symm
    have h_marg₀ : P₀.map (IsAlgEnvSeq.hist A₀ R₀ t) = (Q ⊗ₘ κ₀).map Prod.snd := by
      rw [← h_joint₀]
      exact (Measure.map_map measurable_snd (h₀.measurable_E.prodMk h_meas_hist₀)).symm
    rw [h_marg, h_marg₀, Measure.compProd_congr h_wd_ae,
      Measure.compProd_withDensity
        (show Measurable (Function.uncurry (fun (_ : 𝓔) => ρ)) from hρ_meas.comp measurable_snd)]
    exact map_withDensity_comp measurable_snd hρ_meas
  have h_swap : P.map (fun ω => (IsAlgEnvSeq.hist A R' t ω, E ω))
      = P.map (IsAlgEnvSeq.hist A R' t) ⊗ₘ condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ t) P₀ := by
    have h_uncurry_meas : Measurable (Function.uncurry (fun (_ : 𝓔) => ρ)) :=
      hρ_meas.comp measurable_snd
    calc P.map (fun ω => (IsAlgEnvSeq.hist A R' t ω, E ω))
      _ = (Q ⊗ₘ κ_alg).map Prod.swap := by
          rw [← h_joint]
          exact (Measure.map_map measurable_swap
            (h.measurable_E.prodMk h_meas_hist)).symm
      _ = (Q ⊗ₘ (κ₀.withDensity (fun _ => ρ))).map Prod.swap := by
          rw [Measure.compProd_congr h_wd_ae]
      _ = ((Q ⊗ₘ κ₀).withDensity (ρ ∘ Prod.snd)).map Prod.swap := by
          congr 1; exact Measure.compProd_withDensity h_uncurry_meas
      _ = ((Q ⊗ₘ κ₀).map Prod.swap).withDensity (ρ ∘ Prod.fst) :=
          map_swap_withDensity_fst hρ_meas
      _ = (P₀.map (fun ω => (IsAlgEnvSeq.hist A₀ R₀ t ω, E₀ ω))).withDensity
            (ρ ∘ Prod.fst) := by
          congr 1; rw [← h_joint₀]
          exact Measure.map_map measurable_swap
            (h₀.measurable_E.prodMk h_meas_hist₀)
      _ = (P₀.map (IsAlgEnvSeq.hist A₀ R₀ t) ⊗ₘ
            condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ t) P₀).withDensity
            (ρ ∘ Prod.fst) := by
          rw [← compProd_map_condDistrib h₀.measurable_E.aemeasurable]
      _ = (P₀.map (IsAlgEnvSeq.hist A₀ R₀ t)).withDensity ρ ⊗ₘ
            condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ t) P₀ :=
          (withDensity_compProd_left hρ_meas).symm
      _ = P.map (IsAlgEnvSeq.hist A R' t) ⊗ₘ
            condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ t) P₀ := by
          rw [h_hist]
  -- By uniqueness of disintegration
  exact (condDistrib_ae_eq_iff_measure_eq_compProd _
    h.measurable_E.aemeasurable (condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ t) P₀)).mpr h_swap

end IsBayesAlgEnvSeq

end Learning
