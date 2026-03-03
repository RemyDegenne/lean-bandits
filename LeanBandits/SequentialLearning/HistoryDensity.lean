/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.FullSupport
import LeanBandits.ForMathlib.WithDensity
import LeanBandits.SequentialLearning.BayesStationaryEnv

open MeasureTheory ProbabilityTheory Finset

open scoped ENNReal

namespace Learning

variable {α R : Type*} [MeasurableSpace α] [MeasurableSpace R]

noncomputable
def historyDensity [MeasurableSpace.CountablyGenerated α] (alg alg₀ : Algorithm α R) :
    (n : ℕ) → (Iic n → α × R) → ℝ≥0∞
  | 0, h => (alg.p0.rnDeriv alg₀.p0 (h ⟨0, by simp⟩).1)
  | n + 1, h =>
    let p := MeasurableEquiv.IicSuccProd (fun _ ↦ α × R) n h
    historyDensity alg alg₀ n p.1 * (alg.policy n).rnDeriv (alg₀.policy n) p.1 p.2.1

@[fun_prop]
lemma measurable_historyDensity [MeasurableSpace.CountablyGenerated α] (alg alg₀ : Algorithm α R)
    (n : ℕ) : Measurable (historyDensity alg alg₀ n) := by
  induction n with
  | zero =>
    simp_rw [historyDensity]
    fun_prop
  | succ n ih =>
    simp_rw [historyDensity]
    fun_prop

lemma Algorithm.IsPositive.historyDensity_ne_top [MeasurableSpace.CountablyGenerated α]
    {alg₀ : Algorithm α R} (hp : alg₀.IsPositive) (alg : Algorithm α R) (n : ℕ)
    (h : Iic n → α × R) : historyDensity alg alg₀ n h ≠ ⊤ := by
  induction n with
  | zero => exact Measure.rnDeriv_ne_top_of_forall_singleton_pos hp.1 _
  | succ n ih =>
    exact ENNReal.mul_ne_top (ih _) (Kernel.rnDeriv_ne_top_of_forall_singleton_pos (hp.2 n) _ _)

namespace IsAlgEnvSeq

variable {Ω : Type*} [MeasurableSpace Ω]
variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
variable {alg : Algorithm α R} {env : Environment α R}
variable {A : ℕ → Ω → α} {R' : ℕ → Ω → R}
variable {P : Measure Ω} [IsFiniteMeasure P]

lemma hasLaw_hist_zero (h : IsAlgEnvSeq A R' alg env P) : HasLaw (hist A R' 0)
    ((P.map (step A R' 0)).map
      (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ α × R)).symm) P where
  aemeasurable := (measurable_hist h.measurable_A h.measurable_R 0).aemeasurable
  map_eq := by
    have he : (MeasurableEquiv.piUnique (fun _ : Iic 0 ↦ α × R)).symm ∘ step A R' 0 =
        hist A R' 0 := by
      funext _ ⟨0, _⟩
      rfl
    rw [← he]
    have hA := h.measurable_A
    have hR := h.measurable_R
    exact (Measure.map_map (by fun_prop) (by fun_prop)).symm

lemma hasLaw_hist_succ (h : IsAlgEnvSeq A R' alg env P) (n : ℕ) : HasLaw (hist A R' (n + 1))
    ((P.map (hist A R' n) ⊗ₘ condDistrib (step A R' (n + 1)) (hist A R' n) P).map
        (MeasurableEquiv.IicSuccProd (fun _ ↦ α × R) n).symm) P where
  aemeasurable := (measurable_hist h.measurable_A h.measurable_R (n + 1)).aemeasurable
  map_eq := by
    have he : (MeasurableEquiv.IicSuccProd (fun _ ↦ α × R) n).symm ∘
        (fun ω ↦ (hist A R' n ω, step A R' (n + 1) ω)) = hist A R' (n + 1) := by
      funext ω
      exact (MeasurableEquiv.IicSuccProd (fun _ ↦ α × R) n).symm_apply_apply (hist A R' (n + 1) ω)
    have hA := h.measurable_A
    have hR := h.measurable_R
    rw [← he, ← Measure.map_map (by fun_prop) (by fun_prop)]
    congr
    exact (compProd_map_condDistrib (by fun_prop)).symm

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]
variable {alg₀ : Algorithm α R}
variable {A₀ : ℕ → Ω₀ → α} {R₀ : ℕ → Ω₀ → R}
variable {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

lemma absolutelyContinuous_map_hist (h : IsAlgEnvSeq A R' alg env P)
    (h₀ : IsAlgEnvSeq A₀ R₀ alg₀ env P₀) (hp : alg₀.IsPositive) (n : ℕ) :
    P.map (IsAlgEnvSeq.hist A R' n) ≪ P₀.map (IsAlgEnvSeq.hist A₀ R₀ n) := by
  induction n with
  | zero =>
    rw [h.hasLaw_hist_zero.map_eq, h₀.hasLaw_hist_zero.map_eq]
    apply Measure.AbsolutelyContinuous.map _ (by fun_prop)
    rw [h.hasLaw_step_zero.map_eq, h₀.hasLaw_step_zero.map_eq]
    apply Measure.AbsolutelyContinuous.compProd_left
    exact Measure.absolutelyContinuous_of_forall_singleton_pos hp.1
  | succ n ih =>
    rw [(h.hasLaw_hist_succ n).map_eq, (h₀.hasLaw_hist_succ n).map_eq]
    apply Measure.AbsolutelyContinuous.map _ (by fun_prop)
    rw [Measure.compProd_congr (h.hasCondDistrib_step n).condDistrib_eq,
        Measure.compProd_congr (h₀.hasCondDistrib_step n).condDistrib_eq]
    apply Measure.AbsolutelyContinuous.compProd ih
    filter_upwards with h'
    apply Measure.AbsolutelyContinuous.kernel_compProd_left
    exact Measure.absolutelyContinuous_of_forall_singleton_pos (hp.2 n h')

lemma hasLaw_hist_withDensity (h : IsAlgEnvSeq A R' alg env P)
    (h₀ : IsAlgEnvSeq A₀ R₀ alg₀ env P₀) (hp : alg₀.IsPositive) (n : ℕ) :
    HasLaw (IsAlgEnvSeq.hist A R' n)
      ((P₀.map (IsAlgEnvSeq.hist A₀ R₀ n)).withDensity (historyDensity alg alg₀ n)) P where
  aemeasurable := (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n).aemeasurable
  map_eq := by
    induction n with
    | zero =>
      rw [h.hasLaw_hist_zero.map_eq, h₀.hasLaw_hist_zero.map_eq, h.hasLaw_step_zero.map_eq,
        h₀.hasLaw_step_zero.map_eq]
      have ha : alg.p0 ≪ alg₀.p0 := Measure.absolutelyContinuous_of_forall_singleton_pos hp.1
      rw [← Measure.withDensity_rnDeriv_eq _ _ ha, Measure.withDensity_compProd_left (by fun_prop)]
      exact Measure.withDensity_map_equiv (by fun_prop)
    | succ n ih =>
      let ρ h' (ar : α × R) := Kernel.rnDeriv (alg.policy n) (alg₀.policy n) h' ar.1
      have hpo h' : alg.policy n h' ≪ alg₀.policy n h' :=
        Measure.absolutelyContinuous_of_forall_singleton_pos (hp.2 n h')
      have hs : stepKernel alg env n = (stepKernel alg₀ env n).withDensity ρ := by
        rw [stepKernel, ← Kernel.withDensity_rnDeriv_eq' hpo]
        exact Kernel.withDensity_compProd_left (Kernel.measurable_rnDeriv _ _)
      have : IsMarkovKernel ((stepKernel alg₀ env n).withDensity ρ) := by
        rw [← hs]
        infer_instance
      rw [(h.hasLaw_hist_succ n).map_eq, (h₀.hasLaw_hist_succ n).map_eq,
          Measure.compProd_congr (h.hasCondDistrib_step n).condDistrib_eq,
          Measure.compProd_congr (h₀.hasCondDistrib_step n).condDistrib_eq, ih, hs,
          Measure.withDensity_compProd_withDensity (by fun_prop) (by fun_prop)]
      exact Measure.withDensity_map_equiv (by fun_prop)

end IsAlgEnvSeq

namespace IsBayesAlgEnvSeq

variable {𝓔 : Type*} [MeasurableSpace 𝓔]
variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
variable {Q : Measure 𝓔}
variable {κ : Kernel (𝓔 × α) R} [IsMarkovKernel κ]

variable {Ω : Type*} [MeasurableSpace Ω]
variable {E : Ω → 𝓔} {A : ℕ → Ω → α} {R' : ℕ → Ω → R}
variable {alg : Algorithm α R}
variable {P : Measure Ω} [IsProbabilityMeasure P]

variable {Ω₀ : Type*} [MeasurableSpace Ω₀]
variable {E₀ : Ω₀ → 𝓔} {A₀ : ℕ → Ω₀ → α} {R₀ : ℕ → Ω₀ → R}
variable {alg₀ : Algorithm α R}
variable {P₀ : Measure Ω₀} [IsProbabilityMeasure P₀]

lemma hasCondDistrib_hist_withDensity_historyDensity
    (h : IsBayesAlgEnvSeq Q κ alg E A R' P)
    (hp : alg₀.IsPositive)
    (h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ R₀ P₀)
    (n : ℕ) :
    HasCondDistrib (IsAlgEnvSeq.hist A R' n) E
      ((condDistrib (IsAlgEnvSeq.hist A₀ R₀ n) E₀ P₀).withDensity
        (fun _ => historyDensity alg alg₀ n)) P where
  aemeasurable_fst := (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n).aemeasurable
  aemeasurable_snd := h.measurable_E.aemeasurable
  condDistrib_eq := by
    rw [h.hasLaw_env.map_eq]
    have h_IT_hist : (IsAlgEnvSeq.hist IT.action IT.reward n :
        (ℕ → α × R) → (Iic n → α × R)) = IT.hist n :=
      funext fun ω => funext fun i => Prod.mk.eta
    filter_upwards [h.hasLaw_IT_hist n, h₀.hasLaw_IT_hist n,
      h.ae_IsAlgEnvSeq, h₀.ae_IsAlgEnvSeq] with e he he₀ hae hae₀
    rw [Kernel.withDensity_apply _ (by fun_prop),
      ← he.map_eq, ← he₀.map_eq, ← h_IT_hist]
    exact (hae.hasLaw_hist_withDensity hae₀ hp n).map_eq

variable [IsProbabilityMeasure Q]

/-- The history distribution under any algorithm equals the reference algorithm's
    history distribution, weighted by the history density ratio. -/
lemma hasLaw_hist_withDensity
    (h : IsBayesAlgEnvSeq Q κ alg E A R' P)
    (hp : alg₀.IsPositive)
    (h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ R₀ P₀)
    (n : ℕ) :
    HasLaw (IsAlgEnvSeq.hist A R' n)
      ((P₀.map (IsAlgEnvSeq.hist A₀ R₀ n)).withDensity (historyDensity alg alg₀ n)) P where
  aemeasurable := (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n).aemeasurable
  map_eq := by
    set κ_alg := condDistrib (IsAlgEnvSeq.hist A R' n) E P
    set κ₀ := condDistrib (IsAlgEnvSeq.hist A₀ R₀ n) E₀ P₀
    set ρ := historyDensity alg alg₀ n
    have hρ_meas := measurable_historyDensity alg alg₀ n
    have hρ_ne_top := hp.historyDensity_ne_top alg n
    have h_wd_ae : κ_alg =ᵐ[Q] κ₀.withDensity (fun _ => ρ) := by
      rw [← h.hasLaw_env.map_eq]
      exact (h.hasCondDistrib_hist_withDensity_historyDensity hp h₀ n).condDistrib_eq
    haveI : IsSFiniteKernel (κ₀.withDensity (fun _ => ρ)) :=
      Kernel.IsSFiniteKernel.withDensity _ (fun _ b => hρ_ne_top b)
    rw [(h.hasLaw_hist n).map_eq, (h₀.hasLaw_hist n).map_eq,
      ← Measure.snd_compProd Q κ_alg, Measure.compProd_congr h_wd_ae,
      Measure.snd_compProd Q (κ₀.withDensity (fun _ => ρ))]
    exact Kernel.comp_withDensity_const hρ_meas

variable [StandardBorelSpace 𝓔] [Nonempty 𝓔]

/-- The joint distribution of (history, environment) under any algorithm equals
    the history marginal compProd with the reference algorithm's posterior. -/
lemma hasLaw_hist_env
    (h : IsBayesAlgEnvSeq Q κ alg E A R' P)
    (hp : alg₀.IsPositive)
    (h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ R₀ P₀)
    (n : ℕ) :
    HasLaw (fun ω => (IsAlgEnvSeq.hist A R' n ω, E ω))
      (P.map (IsAlgEnvSeq.hist A R' n) ⊗ₘ
        condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ n) P₀) P where
  aemeasurable :=
    ((IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n).prodMk
      h.measurable_E).aemeasurable
  map_eq := by
    set κ_alg := condDistrib (IsAlgEnvSeq.hist A R' n) E P
    set κ₀ := condDistrib (IsAlgEnvSeq.hist A₀ R₀ n) E₀ P₀
    set ρ := historyDensity alg alg₀ n
    have hρ_meas := measurable_historyDensity alg alg₀ n
    have hρ_ne_top := hp.historyDensity_ne_top alg n
    have h_wd_ae : κ_alg =ᵐ[Q] κ₀.withDensity (fun _ => ρ) := by
      rw [← h.hasLaw_env.map_eq]
      exact (h.hasCondDistrib_hist_withDensity_historyDensity hp h₀ n).condDistrib_eq
    haveI : IsSFiniteKernel (κ₀.withDensity (fun _ => ρ)) :=
      Kernel.IsSFiniteKernel.withDensity _ (fun _ b => hρ_ne_top b)
    have h_hist := (h.hasLaw_hist_withDensity hp h₀ n).map_eq
    have h_meas_hist := IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n
    have h_meas_hist₀ := IsAlgEnvSeq.measurable_hist h₀.measurable_A h₀.measurable_R n
    have h_joint : P.map (fun ω => (E ω, IsAlgEnvSeq.hist A R' n ω)) = Q ⊗ₘ κ_alg := by
      rw [← h.hasLaw_env.map_eq]
      exact (compProd_map_condDistrib h_meas_hist.aemeasurable).symm
    have h_joint₀ : P₀.map (fun ω => (E₀ ω, IsAlgEnvSeq.hist A₀ R₀ n ω)) = Q ⊗ₘ κ₀ := by
      rw [← h₀.hasLaw_env.map_eq]
      exact (compProd_map_condDistrib h_meas_hist₀.aemeasurable).symm
    calc P.map (fun ω => (IsAlgEnvSeq.hist A R' n ω, E ω))
      _ = (Q ⊗ₘ κ_alg).map Prod.swap := by
          rw [← h_joint]
          exact (Measure.map_map measurable_swap
            (h.measurable_E.prodMk h_meas_hist)).symm
      _ = (Q ⊗ₘ (κ₀.withDensity (fun _ => ρ))).map Prod.swap := by
          rw [Measure.compProd_congr h_wd_ae]
      _ = ((Q ⊗ₘ κ₀).withDensity (ρ ∘ Prod.snd)).map Prod.swap := by
          congr 1; exact Measure.compProd_withDensity (by fun_prop)
      _ = ((Q ⊗ₘ κ₀).map Prod.swap).withDensity (ρ ∘ Prod.fst) :=
          Measure.map_swap_withDensity_fst hρ_meas
      _ = (P₀.map (fun ω => (IsAlgEnvSeq.hist A₀ R₀ n ω, E₀ ω))).withDensity
            (ρ ∘ Prod.fst) := by
          congr 1; rw [← h_joint₀]
          exact Measure.map_map measurable_swap
            (h₀.measurable_E.prodMk h_meas_hist₀)
      _ = (P₀.map (IsAlgEnvSeq.hist A₀ R₀ n) ⊗ₘ
            condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ n) P₀).withDensity
            (ρ ∘ Prod.fst) := by
          rw [← compProd_map_condDistrib h₀.measurable_E.aemeasurable]
      _ = (P₀.map (IsAlgEnvSeq.hist A₀ R₀ n)).withDensity ρ ⊗ₘ
            condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ n) P₀ :=
          (Measure.withDensity_compProd_left hρ_meas).symm
      _ = P.map (IsAlgEnvSeq.hist A R' n) ⊗ₘ
            condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ n) P₀ := by
          rw [h_hist]

/-- The posterior on the environment given history is algorithm-independent. -/
lemma hasCondDistrib_env_hist
    (h : IsBayesAlgEnvSeq Q κ alg E A R' P)
    (hp : alg₀.IsPositive)
    (h₀ : IsBayesAlgEnvSeq Q κ alg₀ E₀ A₀ R₀ P₀)
    (n : ℕ) :
    HasCondDistrib E (IsAlgEnvSeq.hist A R' n)
      (condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ n) P₀) P where
  aemeasurable_fst := h.measurable_E.aemeasurable
  aemeasurable_snd :=
    (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n).aemeasurable
  condDistrib_eq :=
    (condDistrib_ae_eq_iff_measure_eq_compProd _
      h.measurable_E.aemeasurable
      (condDistrib E₀ (IsAlgEnvSeq.hist A₀ R₀ n) P₀)).mpr
      (h.hasLaw_hist_env hp h₀ n).map_eq

end IsBayesAlgEnvSeq

end Learning
