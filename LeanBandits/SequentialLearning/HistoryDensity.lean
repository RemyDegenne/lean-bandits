/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.SequentialLearning.StationaryEnv
import LeanBandits.SequentialLearning.BayesStationaryEnv
import LeanBandits.BanditAlgorithms.Uniform
import LeanBandits.ForMathlib.FullSupport
import LeanBandits.ForMathlib.WithDensity

/-!
# Algorithm-Independence of Bayesian Posteriors

The key result: the posterior distribution on the environment (and therefore on the best arm)
given the observed history is independent of the algorithm used to generate the data.

The proof routes through a reference algorithm with full support. The history distribution
under any algorithm is absolutely continuous w.r.t. the reference algorithm's, with a density
that depends only on action probabilities (not the environment). This density factorization
implies the posteriors agree.
-/

open MeasureTheory ProbabilityTheory Finset Preorder

open scoped ENNReal NNReal

namespace Learning

variable {K : ℕ}

section AbsolutelyContinuousHist

variable [Nonempty (Fin K)]

omit [Nonempty (Fin K)] in
/-- The step kernel for a stationary environment decomposes as a product of the policy
    measure and the reward kernel. -/
private lemma absolutelyContinuous_stepKernel_stationary
    (alg ref : Algorithm (Fin K) ℝ) (href : ref.IsPositive)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (n : ℕ) (h : Iic n → Fin K × ℝ) :
    stepKernel alg (stationaryEnv ν) n h ≪
    stepKernel ref (stationaryEnv ν) n h := by
  have h1 : stepKernel alg (stationaryEnv ν) n h = (alg.policy n h) ⊗ₘ ν := by
    simp only [stepKernel, stationaryEnv]; ext s hs
    simp only [Kernel.compProd_apply hs, Measure.compProd_apply hs, Kernel.prodMkLeft_apply]
  have h2 : stepKernel ref (stationaryEnv ν) n h =
      (ref.policy n h) ⊗ₘ ν := by
    simp only [stepKernel, stationaryEnv]; ext s hs
    simp only [Kernel.compProd_apply hs, Measure.compProd_apply hs, Kernel.prodMkLeft_apply]
  rw [h1, h2]
  exact Measure.AbsolutelyContinuous.compProd_left
    (absolutelyContinuous_of_forall_singleton_pos (href.2 n h)) _

/-- The history distribution at time `n + 1` decomposes as a compProd of the history at time `n`
    and the step kernel, composed with `IicSuccProd.symm`. -/
private lemma map_hist_succ_eq_compProd_map
    {Ω : Type*} [MeasurableSpace Ω]
    {A : ℕ → Ω → Fin K} {R' : ℕ → Ω → ℝ}
    {alg : Algorithm (Fin K) ℝ} {env : Environment (Fin K) ℝ}
    {P : Measure Ω} [IsFiniteMeasure P]
    (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) :
    P.map (IsAlgEnvSeq.hist A R' (n + 1)) =
    (P.map (IsAlgEnvSeq.hist A R' n) ⊗ₘ stepKernel alg env n).map
      (MeasurableEquiv.IicSuccProd (fun _ : ℕ => Fin K × ℝ) n).symm := by
  set e := MeasurableEquiv.IicSuccProd (fun _ : ℕ => Fin K × ℝ) n
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

/-- The history distribution under any algorithm is absolutely continuous w.r.t. the
    history distribution under a reference algorithm with full support,
    for a stationary environment. -/
private lemma absolutelyContinuous_map_hist_stationary
    (alg ref : Algorithm (Fin K) ℝ) (href : ref.IsPositive)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    {Ω₁ : Type*} [MeasurableSpace Ω₁]
    {A₁ : ℕ → Ω₁ → Fin K} {R₁ : ℕ → Ω₁ → ℝ}
    {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    (h₁ : IsAlgEnvSeq A₁ R₁ alg (stationaryEnv ν) P₁)
    {Ω₂ : Type*} [MeasurableSpace Ω₂]
    {A₂ : ℕ → Ω₂ → Fin K} {R₂ : ℕ → Ω₂ → ℝ}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    (h₂ : IsAlgEnvSeq A₂ R₂ ref (stationaryEnv ν) P₂)
    (t : ℕ) :
    P₁.map (IsAlgEnvSeq.hist A₁ R₁ t) ≪ P₂.map (IsAlgEnvSeq.hist A₂ R₂ t) := by
  induction t with
  | zero =>
    set e := MeasurableEquiv.piUnique (fun _ : Iic (0 : ℕ) => Fin K × ℝ)
    have h_hist₁ : IsAlgEnvSeq.hist A₁ R₁ 0 = e.symm ∘ IsAlgEnvSeq.step A₁ R₁ 0 := by
      funext ω ⟨i, hi⟩; have : i = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp hi); subst this; rfl
    have h_hist₂ : IsAlgEnvSeq.hist A₂ R₂ 0 = e.symm ∘ IsAlgEnvSeq.step A₂ R₂ 0 := by
      funext ω ⟨i, hi⟩; have : i = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp hi); subst this; rfl
    rw [h_hist₁, h_hist₂,
        ← Measure.map_map e.symm.measurable
          (IsAlgEnvSeq.measurable_step 0 (h₁.measurable_A _) (h₁.measurable_R _)),
        ← Measure.map_map e.symm.measurable
          (IsAlgEnvSeq.measurable_step 0 (h₂.measurable_A _) (h₂.measurable_R _)),
        h₁.hasLaw_step_zero.map_eq, h₂.hasLaw_step_zero.map_eq]
    simp only [stationaryEnv_ν0]
    exact (Measure.AbsolutelyContinuous.compProd_left
      (absolutelyContinuous_of_forall_singleton_pos href.1) _).map
      e.symm.measurable
  | succ n ih =>
    rw [map_hist_succ_eq_compProd_map h₁, map_hist_succ_eq_compProd_map h₂]
    exact (Measure.AbsolutelyContinuous.compProd ih
      (Filter.Eventually.of_forall fun h =>
        absolutelyContinuous_stepKernel_stationary alg ref href ν n h)).map
      (MeasurableEquiv.IicSuccProd _ n).symm.measurable

end AbsolutelyContinuousHist

section DensityIndependence

variable {K : ℕ} [Nonempty (Fin K)]

/-- The density of the history distribution under `alg` w.r.t. a reference algorithm.
This density depends only on the algorithm's action probabilities, not on the reward kernel. -/
private noncomputable def historyDensity
    (alg ref : Algorithm (Fin K) ℝ) :
    (t : ℕ) → (Iic t → Fin K × ℝ) → ℝ≥0∞
  | 0 => (alg.p0.rnDeriv ref.p0 ∘ Prod.fst) ∘
        MeasurableEquiv.piUnique (fun _ : Iic (0 : ℕ) => Fin K × ℝ)
  | n + 1 =>
    let σ : (Iic n → Fin K × ℝ) → (Fin K × ℝ) → ℝ≥0∞ :=
      fun h ar => Kernel.rnDeriv (alg.policy n)
        (ref.policy n) h ar.1
    (historyDensity alg ref n ∘ Prod.fst * Function.uncurry σ) ∘
      MeasurableEquiv.IicSuccProd (fun _ : ℕ => Fin K × ℝ) n

omit [Nonempty (Fin K)] in
private lemma measurable_historyDensity (alg ref : Algorithm (Fin K) ℝ) (t : ℕ) :
    Measurable (historyDensity alg ref t) := by
  induction t with
  | zero =>
    exact (Measure.measurable_rnDeriv _ _).comp
      (measurable_fst.comp (MeasurableEquiv.piUnique _).measurable)
  | succ n ih =>
    exact ((ih.comp measurable_fst).mul
      ((Kernel.measurable_rnDeriv _ _).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd)))).comp
      (MeasurableEquiv.IicSuccProd _ n).measurable

omit [Nonempty (Fin K)] in
private lemma historyDensity_ne_top (alg ref : Algorithm (Fin K) ℝ)
    (href : ref.IsPositive) (t : ℕ)
    (h : Iic t → Fin K × ℝ) : historyDensity alg ref t h ≠ ⊤ := by
  induction t with
  | zero => exact rnDeriv_ne_top_of_forall_singleton_pos href.1 _
  | succ n ih =>
    exact ENNReal.mul_ne_top (ih _)
      (kernel_rnDeriv_ne_top_of_forall_singleton_pos
        (fun h' a => href.2 n h' a) _ _)

/-- The history distribution under any algorithm equals the reference algorithm's history
distribution weighted by `historyDensity`, for any stationary environment. -/
private lemma map_hist_eq_withDensity_historyDensity
    (alg ref : Algorithm (Fin K) ℝ) (href : ref.IsPositive) (t : ℕ)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    {Ω₁ : Type*} [MeasurableSpace Ω₁]
    {A₁ : ℕ → Ω₁ → Fin K} {R₁ : ℕ → Ω₁ → ℝ}
    {P₁ : Measure Ω₁} [IsProbabilityMeasure P₁]
    (h₁ : IsAlgEnvSeq A₁ R₁ alg (stationaryEnv ν) P₁)
    {Ω₂ : Type*} [MeasurableSpace Ω₂]
    {A₂ : ℕ → Ω₂ → Fin K} {R₂ : ℕ → Ω₂ → ℝ}
    {P₂ : Measure Ω₂} [IsProbabilityMeasure P₂]
    (h₂ : IsAlgEnvSeq A₂ R₂ ref (stationaryEnv ν) P₂) :
    P₁.map (IsAlgEnvSeq.hist A₁ R₁ t) =
    (P₂.map (IsAlgEnvSeq.hist A₂ R₂ t)).withDensity (historyDensity alg ref t) := by
  induction t with
  | zero =>
    set e := MeasurableEquiv.piUnique (fun _ : Iic (0 : ℕ) => Fin K × ℝ)
    have h_ac : alg.p0 ≪ ref.p0 :=
      absolutelyContinuous_of_forall_singleton_pos href.1
    have h_hist₁ : IsAlgEnvSeq.hist A₁ R₁ 0 = e.symm ∘ IsAlgEnvSeq.step A₁ R₁ 0 := by
      funext ω ⟨i, hi⟩
      have : i = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp hi); subst this; rfl
    have h_hist₂ : IsAlgEnvSeq.hist A₂ R₂ 0 = e.symm ∘ IsAlgEnvSeq.step A₂ R₂ 0 := by
      funext ω ⟨i, hi⟩
      have : i = 0 := Nat.le_zero.mp (Finset.mem_Iic.mp hi); subst this; rfl
    rw [h_hist₁, h_hist₂,
        ← Measure.map_map e.symm.measurable
          (IsAlgEnvSeq.measurable_step 0 (h₁.measurable_A _) (h₁.measurable_R _)),
        ← Measure.map_map e.symm.measurable
          (IsAlgEnvSeq.measurable_step 0 (h₂.measurable_A _) (h₂.measurable_R _)),
        h₁.hasLaw_step_zero.map_eq, h₂.hasLaw_step_zero.map_eq]
    simp only [stationaryEnv_ν0]
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ h_ac]
    rw [withDensity_compProd_left (Measure.measurable_rnDeriv _ _)]
    exact withDensity_map_equiv_symm
      ((Measure.measurable_rnDeriv _ _).comp measurable_fst)
  | succ n ih =>
    let σ : (Iic n → Fin K × ℝ) → (Fin K × ℝ) → ℝ≥0∞ :=
      fun h ar => Kernel.rnDeriv (alg.policy n) (ref.policy n) h ar.1
    have hσ_meas : Measurable (Function.uncurry σ) :=
      (Kernel.measurable_rnDeriv _ _).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    have h_step : stepKernel alg (stationaryEnv ν) n =
        (stepKernel ref (stationaryEnv ν) n).withDensity σ := by
      ext h : 1
      rw [Kernel.withDensity_apply _ hσ_meas]
      have h_alg : stepKernel alg (stationaryEnv ν) n h = (alg.policy n h) ⊗ₘ ν := by
        ext s hs
        simp only [stepKernel, stationaryEnv, Kernel.compProd_apply hs,
          Measure.compProd_apply hs, Kernel.prodMkLeft_apply]
      have h_ref : stepKernel ref (stationaryEnv ν) n h = (ref.policy n h) ⊗ₘ ν := by
        ext s hs
        simp only [stepKernel, stationaryEnv, Kernel.compProd_apply hs,
          Measure.compProd_apply hs, Kernel.prodMkLeft_apply]
      have h_wd : ((ref.policy n) h).withDensity
          (Kernel.rnDeriv (alg.policy n) (ref.policy n) h) = alg.policy n h := by
        rw [← Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _)]
        exact Kernel.withDensity_rnDeriv_eq (κ := alg.policy n) (η := ref.policy n)
          (absolutelyContinuous_of_forall_singleton_pos (href.2 n h))
      rw [h_alg, h_ref, ← h_wd]
      haveI : SFinite ((ref.policy n h).withDensity
          (Kernel.rnDeriv (alg.policy n) (ref.policy n) h)) := by
        rw [h_wd]; infer_instance
      exact withDensity_compProd_left
        (Kernel.measurable_rnDeriv (alg.policy n) (ref.policy n)).of_uncurry_left
    haveI : IsSFiniteKernel ((stepKernel ref (stationaryEnv ν) n).withDensity σ) := by
      rw [← h_step]; infer_instance
    rw [map_hist_succ_eq_compProd_map h₁ n,
        map_hist_succ_eq_compProd_map h₂ n,
        ih, h_step,
        withDensity_compProd_withDensity (measurable_historyDensity alg ref n) hσ_meas]
    exact withDensity_map_equiv_symm
      (((measurable_historyDensity alg ref n).comp measurable_fst).mul hσ_meas)

end DensityIndependence

section PosteriorIndependence

/-! ### Algorithm-independence of the posterior

The key theorem: the posterior distribution on the best arm given the observed history
is independent of the algorithm used to generate the data. The proof routes through
a reference algorithm with full support. The posterior on the environment given history
is algorithm-independent (ae wrt the algorithm's own history distribution), and this
transfers to the posterior on the best arm via `condDistrib_comp`.
-/

variable {K : ℕ} [Nonempty (Fin K)]
variable {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
variable (Q : Measure E) [IsProbabilityMeasure Q]
variable (κ : Kernel (E × Fin K) ℝ) [IsMarkovKernel κ]
variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
variable {E' : Ω → E} {A : ℕ → Ω → Fin K} {R' : ℕ → Ω → ℝ}
variable {alg : Algorithm (Fin K) ℝ}
variable {P : Measure Ω} [IsProbabilityMeasure P]

omit [StandardBorelSpace E] [Nonempty E] [IsMarkovKernel κ] in
/-- The marginal on the history equals `condDistrib (hist) (env) P ∘ₘ Q`. -/
private lemma map_hist_eq_condDistrib_comp
    {Ω' : Type*} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    {E'' : Ω' → E} {A' : ℕ → Ω' → Fin K} {R'' : ℕ → Ω' → ℝ}
    {alg' : Algorithm (Fin K) ℝ} {P' : Measure Ω'} [IsProbabilityMeasure P']
    (h' : IsBayesAlgEnvSeq Q κ alg' E'' A' R'' P') (t : ℕ) :
    P'.map (IsAlgEnvSeq.hist A' R'' t) =
    condDistrib (IsAlgEnvSeq.hist A' R'' t) E'' P' ∘ₘ Q := by
  calc P'.map (IsAlgEnvSeq.hist A' R'' t)
    _ = (P'.map (fun ω => (E'' ω,
          IsAlgEnvSeq.hist A' R'' t ω))).snd :=
        (Measure.snd_map_prodMk h'.measurable_E).symm
    _ = (P'.map E'' ⊗ₘ condDistrib
          (IsAlgEnvSeq.hist A' R'' t) E'' P').snd := by
        rw [compProd_map_condDistrib
          (IsAlgEnvSeq.measurable_hist h'.measurable_A h'.measurable_R t).aemeasurable]
    _ = (Q ⊗ₘ condDistrib (IsAlgEnvSeq.hist A' R'' t)
          E'' P').snd := by rw [h'.hasLaw_env.map_eq]
    _ = _ := Measure.snd_compProd Q _

omit [StandardBorelSpace E] [Nonempty E] in
/-- The history distribution under any algorithm is absolutely continuous w.r.t. the
    history distribution under a reference algorithm with full support. -/
lemma absolutelyContinuous_map_hist
    (h : IsBayesAlgEnvSeq Q κ alg E' A R' P)
    {ref : Algorithm (Fin K) ℝ} (href : ref.IsPositive)
    {Ωu : Type*} [MeasurableSpace Ωu] [StandardBorelSpace Ωu] [Nonempty Ωu]
    {Eu : Ωu → E} {Au : ℕ → Ωu → Fin K} {Ru : ℕ → Ωu → ℝ}
    {Pu : Measure Ωu} [IsProbabilityMeasure Pu]
    (hu : IsBayesAlgEnvSeq Q κ ref Eu Au Ru Pu)
    (t : ℕ) :
    P.map (IsAlgEnvSeq.hist A R' t) ≪
    Pu.map (IsAlgEnvSeq.hist Au Ru t) := by
  set κ_alg := condDistrib (IsAlgEnvSeq.hist A R' t) E' P
  set κ_ref := condDistrib (IsAlgEnvSeq.hist Au Ru t) Eu Pu
  rw [map_hist_eq_condDistrib_comp Q κ h t, map_hist_eq_condDistrib_comp Q κ hu t,
    ← Measure.snd_compProd, ← Measure.snd_compProd]
  have hW_meas : Measurable (fun (ω : Ω) (n : ℕ) => (A n ω, R' n ω)) :=
    measurable_pi_lambda _ fun n => (h.measurable_A n).prodMk (h.measurable_R n)
  have hWu_meas : Measurable (fun (ω : Ωu) (n : ℕ) => (Au n ω, Ru n ω)) :=
    measurable_pi_lambda _ fun n => (hu.measurable_A n).prodMk (hu.measurable_R n)
  exact (Measure.AbsolutelyContinuous.compProd_right
    (show ∀ᵐ e ∂Q, κ_alg e ≪ κ_ref e from by
      have h_IT_hist : (IsAlgEnvSeq.hist IT.action IT.reward t :
          (ℕ → Fin K × ℝ) → (Iic t → Fin K × ℝ)) = IT.hist t :=
        funext fun ω => funext fun i => Prod.mk.eta
      have h_cd₁ : ∀ᵐ e ∂Q, κ_alg e =
          (condDistrib (fun ω n => (A n ω, R' n ω)) E' P e).map (IT.hist t) := by
        rw [← h.hasLaw_env.map_eq]
        have h_comp : κ_alg
            =ᵐ[P.map E'] (condDistrib (fun ω n => (A n ω, R' n ω)) E' P).map (IT.hist t) :=
          condDistrib_comp E' hW_meas.aemeasurable (IT.measurable_hist t)
        filter_upwards [h_comp] with e he
        rw [he, Kernel.map_apply _ (IT.measurable_hist t)]
      have h_cd₂ : ∀ᵐ e ∂Q, κ_ref e =
          (condDistrib (fun ω n => (Au n ω, Ru n ω)) Eu Pu e).map (IT.hist t) := by
        rw [← hu.hasLaw_env.map_eq]
        have h_comp : κ_ref
            =ᵐ[Pu.map Eu] (condDistrib (fun ω n => (Au n ω, Ru n ω)) Eu Pu).map (IT.hist t) :=
          condDistrib_comp Eu hWu_meas.aemeasurable (IT.measurable_hist t)
        filter_upwards [h_comp] with e he
        rw [he, Kernel.map_apply _ (IT.measurable_hist t)]
      have hae₁ := h.ae_IsAlgEnvSeq
      have hae₂ := hu.ae_IsAlgEnvSeq
      filter_upwards [h_cd₁, h_cd₂, hae₁, hae₂] with e he₁ he₂ hae₁ hae₂
      rw [he₁, he₂, ← h_IT_hist]
      exact absolutelyContinuous_map_hist_stationary alg ref href _ hae₁ hae₂ t)).map
    measurable_snd

omit [StandardBorelSpace Ω] [Nonempty Ω] in
/-- The posterior on the environment given history is algorithm-independent. -/
lemma condDistrib_env_hist_alg_indep
    (h : IsBayesAlgEnvSeq Q κ alg E' A R' P)
    {ref : Algorithm (Fin K) ℝ} (href : ref.IsPositive)
    {Ωu : Type*} [MeasurableSpace Ωu] [StandardBorelSpace Ωu] [Nonempty Ωu]
    {Eu : Ωu → E} {Au : ℕ → Ωu → Fin K} {Ru : ℕ → Ωu → ℝ}
    {Pu : Measure Ωu} [IsProbabilityMeasure Pu]
    (hu : IsBayesAlgEnvSeq Q κ ref Eu Au Ru Pu)
    (t : ℕ) :
    condDistrib E' (IsAlgEnvSeq.hist A R' t) P
      =ᵐ[P.map (IsAlgEnvSeq.hist A R' t)]
    condDistrib Eu (IsAlgEnvSeq.hist Au Ru t) Pu := by
  set κ_alg := condDistrib (IsAlgEnvSeq.hist A R' t) E' P
  set κ_ref := condDistrib (IsAlgEnvSeq.hist Au Ru t) Eu Pu
  set ρ := historyDensity alg ref t
  have hρ_meas := measurable_historyDensity alg ref t
  have hρ_ne_top := historyDensity_ne_top alg ref href t
  have hW_meas : Measurable (fun (ω : Ω) (n : ℕ) => (A n ω, R' n ω)) :=
    measurable_pi_lambda _ fun n => (h.measurable_A n).prodMk (h.measurable_R n)
  have hWu_meas : Measurable (fun (ω : Ωu) (n : ℕ) => (Au n ω, Ru n ω)) :=
    measurable_pi_lambda _ fun n => (hu.measurable_A n).prodMk (hu.measurable_R n)
  -- Key factorization: κ_alg =ᵐ[Q] κ_ref.withDensity (fun _ => ρ)
  have h_wd_ae : κ_alg =ᵐ[Q] κ_ref.withDensity (fun _ => ρ) := by
    have h_IT_hist : (IsAlgEnvSeq.hist IT.action IT.reward t :
        (ℕ → Fin K × ℝ) → (Iic t → Fin K × ℝ)) = IT.hist t :=
      funext fun ω => funext fun i => Prod.mk.eta
    have h_cd₁ : ∀ᵐ e ∂Q, κ_alg e =
        (condDistrib (fun ω n => (A n ω, R' n ω)) E' P e).map (IT.hist t) := by
      rw [← h.hasLaw_env.map_eq]
      have h_comp : κ_alg
          =ᵐ[P.map E'] (condDistrib (fun ω n => (A n ω, R' n ω)) E' P).map (IT.hist t) :=
        condDistrib_comp E' hW_meas.aemeasurable (IT.measurable_hist t)
      filter_upwards [h_comp] with e he
      rw [he, Kernel.map_apply _ (IT.measurable_hist t)]
    have h_cd₂ : ∀ᵐ e ∂Q, κ_ref e =
        (condDistrib (fun ω n => (Au n ω, Ru n ω)) Eu Pu e).map (IT.hist t) := by
      rw [← hu.hasLaw_env.map_eq]
      have h_comp : κ_ref
          =ᵐ[Pu.map Eu] (condDistrib (fun ω n => (Au n ω, Ru n ω)) Eu Pu).map (IT.hist t) :=
        condDistrib_comp Eu hWu_meas.aemeasurable (IT.measurable_hist t)
      filter_upwards [h_comp] with e he
      rw [he, Kernel.map_apply _ (IT.measurable_hist t)]
    have hae₁ := h.ae_IsAlgEnvSeq
    have hae₂ := hu.ae_IsAlgEnvSeq
    filter_upwards [h_cd₁, h_cd₂, hae₁, hae₂] with e he₁ he₂ hae₁ hae₂
    rw [Kernel.withDensity_apply _
      (show Measurable (Function.uncurry (fun (_ : E) => ρ)) from hρ_meas.comp measurable_snd),
      he₁, he₂, ← h_IT_hist]
    exact map_hist_eq_withDensity_historyDensity alg ref href t _ hae₁ hae₂
  haveI : IsSFiniteKernel (κ_ref.withDensity (fun _ => ρ)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ b => hρ_ne_top b)
  -- Direct condDistrib equality via joint measure argument
  -- Show: P.map (hist, E') = P.map hist ⊗ₘ condDistrib Eu hist_ref Pu
  -- using the density factorization and disintegration
  have h_joint₁ : P.map (fun ω => (E' ω, IsAlgEnvSeq.hist A R' t ω)) = Q ⊗ₘ κ_alg := by
    rw [← h.hasLaw_env.map_eq]
    exact (compProd_map_condDistrib
      (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R t).aemeasurable).symm
  have h_joint₂ : Pu.map (fun ω => (Eu ω, IsAlgEnvSeq.hist Au Ru t ω)) = Q ⊗ₘ κ_ref := by
    rw [← hu.hasLaw_env.map_eq]
    exact (compProd_map_condDistrib
      (IsAlgEnvSeq.measurable_hist hu.measurable_A hu.measurable_R t).aemeasurable).symm
  -- The swapped joint of P equals P.map hist ⊗ₘ condDistrib Eu hist_ref Pu
  have h_meas_hist := IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R t
  have h_meas_hist_u := IsAlgEnvSeq.measurable_hist hu.measurable_A hu.measurable_R t
  -- P.map hist = (Pu.map hist_ref).withDensity ρ
  have h_hist : P.map (IsAlgEnvSeq.hist A R' t)
      = (Pu.map (IsAlgEnvSeq.hist Au Ru t)).withDensity ρ := by
    have h_marg₁ : P.map (IsAlgEnvSeq.hist A R' t) = (Q ⊗ₘ κ_alg).map Prod.snd := by
      rw [← h_joint₁]
      exact (Measure.map_map measurable_snd (h.measurable_E.prodMk h_meas_hist)).symm
    have h_marg₂ : Pu.map (IsAlgEnvSeq.hist Au Ru t) = (Q ⊗ₘ κ_ref).map Prod.snd := by
      rw [← h_joint₂]
      exact (Measure.map_map measurable_snd (hu.measurable_E.prodMk h_meas_hist_u)).symm
    rw [h_marg₁, h_marg₂, Measure.compProd_congr h_wd_ae,
      Measure.compProd_withDensity
        (show Measurable (Function.uncurry (fun (_ : E) => ρ)) from hρ_meas.comp measurable_snd)]
    exact map_withDensity_comp measurable_snd hρ_meas
  have h_swap : P.map (fun ω => (IsAlgEnvSeq.hist A R' t ω, E' ω))
      = P.map (IsAlgEnvSeq.hist A R' t) ⊗ₘ condDistrib Eu (IsAlgEnvSeq.hist Au Ru t) Pu := by
    have h_uncurry_meas : Measurable (Function.uncurry (fun (_ : E) => ρ)) :=
      hρ_meas.comp measurable_snd
    calc P.map (fun ω => (IsAlgEnvSeq.hist A R' t ω, E' ω))
      _ = (Q ⊗ₘ κ_alg).map Prod.swap := by
          rw [← h_joint₁]
          exact (Measure.map_map measurable_swap
            (h.measurable_E.prodMk h_meas_hist)).symm
      _ = (Q ⊗ₘ (κ_ref.withDensity (fun _ => ρ))).map Prod.swap := by
          rw [Measure.compProd_congr h_wd_ae]
      _ = ((Q ⊗ₘ κ_ref).withDensity (ρ ∘ Prod.snd)).map Prod.swap := by
          congr 1; exact Measure.compProd_withDensity h_uncurry_meas
      _ = ((Q ⊗ₘ κ_ref).map Prod.swap).withDensity (ρ ∘ Prod.fst) :=
          map_swap_withDensity_fst hρ_meas
      _ = (Pu.map (fun ω => (IsAlgEnvSeq.hist Au Ru t ω, Eu ω))).withDensity
            (ρ ∘ Prod.fst) := by
          congr 1; rw [← h_joint₂]
          exact Measure.map_map measurable_swap
            (hu.measurable_E.prodMk h_meas_hist_u)
      _ = (Pu.map (IsAlgEnvSeq.hist Au Ru t) ⊗ₘ
            condDistrib Eu (IsAlgEnvSeq.hist Au Ru t) Pu).withDensity
            (ρ ∘ Prod.fst) := by
          rw [← compProd_map_condDistrib hu.measurable_E.aemeasurable]
      _ = (Pu.map (IsAlgEnvSeq.hist Au Ru t)).withDensity ρ ⊗ₘ
            condDistrib Eu (IsAlgEnvSeq.hist Au Ru t) Pu :=
          (withDensity_compProd_left hρ_meas).symm
      _ = P.map (IsAlgEnvSeq.hist A R' t) ⊗ₘ
            condDistrib Eu (IsAlgEnvSeq.hist Au Ru t) Pu := by
          rw [h_hist]
  -- By uniqueness of disintegration
  exact (condDistrib_ae_eq_iff_measure_eq_compProd _
    h.measurable_E.aemeasurable (condDistrib Eu (IsAlgEnvSeq.hist Au Ru t) Pu)).mpr h_swap

omit [StandardBorelSpace Ω] [Nonempty Ω] in
/-- The environment posterior is algorithm-independent: it equals the posterior under the
reference algorithm, which is `IsBayesAlgEnvSeq.posterior`. -/
lemma posterior_eq_ref
    (h : IsBayesAlgEnvSeq Q κ alg E' A R' P)
    {ref : Algorithm (Fin K) ℝ} (href : ref.IsPositive) (t : ℕ) :
    condDistrib E' (IsAlgEnvSeq.hist A R' t) P
      =ᵐ[P.map (IsAlgEnvSeq.hist A R' t)]
    IT.bayesTrajMeasurePosterior Q κ ref t :=
  condDistrib_env_hist_alg_indep Q κ h href
    (IT.isBayesAlgEnvSeq_bayesTrajMeasure Q κ ref) t

end PosteriorIndependence

end Learning
