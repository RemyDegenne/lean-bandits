/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.SequentialLearning.StationaryEnv
import LeanBandits.SequentialLearning.BayesStationaryEnv
import LeanBandits.BanditAlgorithms.Uniform
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Algorithm-Independence of Bayesian Posteriors

The key result: the posterior distribution on the environment (and therefore on the best arm)
given the observed history is independent of the algorithm used to generate the data.

The proof routes through a uniform algorithm as reference measure. The history distribution
under any algorithm is absolutely continuous w.r.t. the uniform algorithm's, with a density
that depends only on action probabilities (not the environment). This density factorization
implies the posteriors agree.
-/

open MeasureTheory ProbabilityTheory Finset Preorder

open scoped ENNReal NNReal

namespace Learning

variable {K : ℕ}

section UniformFullSupport

variable {K : ℕ} (hK : 0 < K)

/-- The uniform algorithm gives positive probability to every action. -/
lemma uniformAlgorithm_p0_pos (a : Fin K) :
    (Bandits.uniformAlgorithm hK).p0 {a} > 0 := by
  simp only [Bandits.uniformAlgorithm, uniformOn]
  refine cond_pos_of_inter_ne_zero MeasurableSet.univ ?_
  simp only [Set.univ_inter, Measure.count_singleton, ne_eq, one_ne_zero, not_false_eq_true]

/-- The uniform algorithm's policy gives positive probability to every action. -/
lemma uniformAlgorithm_policy_pos (n : ℕ) (h : Iic n → Fin K × ℝ) (a : Fin K) :
    (Bandits.uniformAlgorithm hK).policy n h {a} > 0 := by
  simp only [Bandits.uniformAlgorithm, Kernel.const_apply, uniformOn]
  refine cond_pos_of_inter_ne_zero MeasurableSet.univ ?_
  simp only [Set.univ_inter, Measure.count_singleton, ne_eq, one_ne_zero, not_false_eq_true]

/-- Any measure on a finite type is absolutely continuous wrt any measure giving positive mass
    to all singletons. -/
lemma absolutelyContinuous_of_forall_singleton_pos {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α]
    {μ ν : Measure α} [IsFiniteMeasure μ]
    (hν : ∀ a : α, ν {a} > 0) : μ ≪ ν := by
  intro s hs
  have h_empty : s = ∅ := by
    by_contra h
    obtain ⟨a, ha⟩ := Set.nonempty_iff_ne_empty.mpr h
    have h1 : ν {a} ≤ ν s := measure_mono (Set.singleton_subset_iff.mpr ha)
    exact absurd (le_antisymm (hs ▸ h1) (zero_le _)) (ne_of_gt (hν a))
  rw [h_empty, measure_empty]

/-- `rnDeriv` is pointwise finite when the reference measure has full support on singletons. -/
lemma rnDeriv_ne_top_of_forall_singleton_pos {α : Type*} [MeasurableSpace α]
    [MeasurableSingletonClass α] [Fintype α]
    {μ ν : Measure α} [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hν : ∀ a, ν {a} > 0) (a : α) : μ.rnDeriv ν a ≠ ⊤ := by
  intro h_eq
  have h_mem : a ∈ {x | ¬ (μ.rnDeriv ν x < ⊤)} := by simp [h_eq]
  have h_null : ν {x | ¬ (μ.rnDeriv ν x < ⊤)} = 0 :=
    ae_iff.mp (Measure.rnDeriv_lt_top μ ν)
  exact absurd (le_antisymm ((measure_mono (Set.singleton_subset_iff.mpr h_mem)).trans
    (le_of_eq h_null)) (zero_le _)) (ne_of_gt (hν a))

/-- Kernel `rnDeriv` is pointwise finite when the reference kernel has full support
    on singletons. -/
lemma kernel_rnDeriv_ne_top_of_forall_singleton_pos
    {α' β' : Type*} [MeasurableSpace α'] [MeasurableSpace β']
    [MeasurableSingletonClass β'] [Fintype β']
    [MeasurableSpace.CountableOrCountablyGenerated α' β']
    {κ η : Kernel α' β'} [IsFiniteKernel κ] [IsFiniteKernel η]
    (hη : ∀ a b, η a {b} > 0) (a : α') (b : β') :
    Kernel.rnDeriv κ η a b ≠ ⊤ := by
  intro h_eq
  have h_mem : b ∈ {x | ¬ (Kernel.rnDeriv κ η a x < ⊤)} := by simp [h_eq]
  have h_null : η a {x | ¬ (Kernel.rnDeriv κ η a x < ⊤)} = 0 :=
    ae_iff.mp (Kernel.rnDeriv_lt_top κ η)
  exact absurd (le_antisymm ((measure_mono (Set.singleton_subset_iff.mpr h_mem)).trans
    (le_of_eq h_null)) (zero_le _)) (ne_of_gt (hη a b))

end UniformFullSupport

section WithDensityHelpers

variable {α' β' : Type*} {mα' : MeasurableSpace α'} {mβ' : MeasurableSpace β'}

/-- Composing `withDensity` on the measure side of a `compProd`:
`(μ.withDensity f) ⊗ₘ κ = (μ ⊗ₘ κ).withDensity (f ∘ Prod.fst)`. -/
private lemma withDensity_compProd_left
    {μ : Measure α'} [SFinite μ] {κ : Kernel α' β'} [IsSFiniteKernel κ]
    {f : α' → ENNReal} (hf : Measurable f) [SFinite (μ.withDensity f)] :
    (μ.withDensity f) ⊗ₘ κ = (μ ⊗ₘ κ).withDensity (f ∘ Prod.fst) := by
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs,
    lintegral_withDensity_eq_lintegral_mul₀ hf.aemeasurable
      (Kernel.measurable_kernel_prodMk_left hs).aemeasurable,
    ← lintegral_indicator hs,
    Measure.lintegral_compProd ((hf.comp measurable_fst).indicator hs)]
  congr 1; ext a; simp_rw [Pi.mul_apply]
  have : (fun b => s.indicator (f ∘ Prod.fst) (a, b)) =
      fun b => (Prod.mk a ⁻¹' s).indicator (fun _ => f a) b := by
    ext b; simp only [Function.comp, Set.indicator, Set.mem_preimage]; rfl
  rw [this, lintegral_indicator_const (hs.preimage (by fun_prop))]

/-- Mapping a `withDensity` through `MeasurableEquiv.symm`:
`(μ.withDensity f).map e.symm = (μ.map e.symm).withDensity (f ∘ e)`. -/
private lemma withDensity_map_equiv_symm
    {μ : Measure β'} {e : α' ≃ᵐ β'} {f : β' → ENNReal} (hf : Measurable f) :
    (μ.withDensity f).map e.symm = (μ.map e.symm).withDensity (f ∘ e) := by
  ext s hs
  rw [Measure.map_apply e.symm.measurable hs,
    withDensity_apply _ (e.symm.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map e.symm.measurable hs,
    lintegral_map (hf.comp e.measurable) e.symm.measurable]
  simp_rw [Function.comp_apply, e.apply_symm_apply]

/-- Mapping a `withDensity` through a `MeasurableEquiv` from the snd component. -/
private lemma map_swap_withDensity_fst
    {μ : Measure (α' × β')} [SFinite μ]
    {f : β' → ENNReal} (hf : Measurable f) :
    (μ.withDensity (f ∘ Prod.snd)).map Prod.swap
      = (μ.map Prod.swap).withDensity (f ∘ Prod.fst) := by
  ext s hs
  rw [Measure.map_apply measurable_swap hs, withDensity_apply _ (measurable_swap hs),
    withDensity_apply _ hs, Measure.restrict_map measurable_swap hs]
  exact (lintegral_map (hf.comp measurable_fst) measurable_swap).symm

/-- `(μ.withDensity (h ∘ g)).map g = (μ.map g).withDensity h`. -/
private lemma withDensity_map_eq'
    {γ' : Type*} {mγ' : MeasurableSpace γ'}
    {μ : Measure α'} {g : α' → γ'} {h : γ' → ENNReal}
    (hg : Measurable g) (hh : Measurable h) :
    (μ.withDensity (h ∘ g)).map g = (μ.map g).withDensity h := by
  ext s hs
  rw [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs]
  conv_rhs => rw [Measure.restrict_map hg hs]
  rw [lintegral_map hh hg]; rfl

/-- `(κ.withDensity (fun _ => ρ)) ∘ₘ Q = (κ ∘ₘ Q).withDensity ρ`. -/
private lemma comp_withDensity_const
    {γ' : Type*} {mγ' : MeasurableSpace γ'}
    {Q : Measure α'} [SFinite Q]
    {κ : Kernel α' γ'} [IsSFiniteKernel κ]
    {ρ : γ' → ENNReal} (hρ : Measurable ρ)
    [IsSFiniteKernel (κ.withDensity (fun _ => ρ))] :
    (κ.withDensity (fun _ => ρ)) ∘ₘ Q = (κ ∘ₘ Q).withDensity ρ := by
  rw [← Measure.snd_compProd Q (κ.withDensity (fun _ => ρ)),
    Measure.compProd_withDensity (show Measurable (Function.uncurry (fun (_ : α') => ρ)) from
      hρ.comp measurable_snd),
    ← Measure.snd_compProd Q κ, Measure.snd, Measure.snd]
  exact withDensity_map_eq' measurable_snd hρ

/-- `(μ.withDensity f) ⊗ₘ (κ.withDensity g) = (μ ⊗ₘ κ).withDensity (f ∘ fst * uncurry g)`. -/
private lemma withDensity_compProd_withDensity
    {γ' : Type*} {mγ' : MeasurableSpace γ'}
    {μ : Measure α'} [SFinite μ]
    {κ : Kernel α' γ'} [IsSFiniteKernel κ]
    {f : α' → ENNReal} {g : α' → γ' → ENNReal}
    (hf : Measurable f) (hg : Measurable (Function.uncurry g))
    [SFinite (μ.withDensity f)] [IsSFiniteKernel (κ.withDensity g)] :
    (μ.withDensity f) ⊗ₘ (κ.withDensity g)
      = (μ ⊗ₘ κ).withDensity (f ∘ Prod.fst * Function.uncurry g) := by
  rw [Measure.compProd_withDensity hg, withDensity_compProd_left hf]
  exact (withDensity_mul _ (hf.comp measurable_fst) hg).symm

end WithDensityHelpers

section AbsolutelyContinuousHist

variable {K : ℕ} [Nonempty (Fin K)]

omit [Nonempty (Fin K)] in
/-- The step kernel for a stationary environment decomposes as a product of the policy
    measure and the reward kernel. -/
private lemma absolutelyContinuous_stepKernel_stationary
    (hK : 0 < K) (alg : Algorithm (Fin K) ℝ) (ν : Kernel (Fin K) ℝ)
    [IsMarkovKernel ν] (n : ℕ) (h : Iic n → Fin K × ℝ) :
    stepKernel alg (stationaryEnv ν) n h ≪
    stepKernel (Bandits.uniformAlgorithm hK) (stationaryEnv ν) n h := by
  have h1 : stepKernel alg (stationaryEnv ν) n h = (alg.policy n h) ⊗ₘ ν := by
    simp only [stepKernel, stationaryEnv]; ext s hs
    simp only [Kernel.compProd_apply hs, Measure.compProd_apply hs, Kernel.prodMkLeft_apply]
  have h2 : stepKernel (Bandits.uniformAlgorithm hK) (stationaryEnv ν) n h =
      ((Bandits.uniformAlgorithm hK).policy n h) ⊗ₘ ν := by
    simp only [stepKernel, stationaryEnv]; ext s hs
    simp only [Kernel.compProd_apply hs, Measure.compProd_apply hs, Kernel.prodMkLeft_apply]
  rw [h1, h2]
  exact Measure.AbsolutelyContinuous.compProd_left
    (absolutelyContinuous_of_forall_singleton_pos (uniformAlgorithm_policy_pos hK n h)) _

-- `compProd` unfolding requires extra heartbeats
/-- The history distribution at time `n + 1` decomposes as a compProd of the history at time `n`
    and the step kernel, composed with `IicSuccProd.symm`. -/
private lemma map_hist_succ_eq_compProd_map
    (alg : Algorithm (Fin K) ℝ) (env : Environment (Fin K) ℝ) (n : ℕ) :
    (trajMeasure alg env).map (IT.hist (n + 1)) =
    ((trajMeasure alg env).map (IT.hist n) ⊗ₘ stepKernel alg env n).map
      (MeasurableEquiv.IicSuccProd (fun _ : ℕ => Fin K × ℝ) n).symm := by
  set P := trajMeasure alg env
  set e := MeasurableEquiv.IicSuccProd (fun _ : ℕ => Fin K × ℝ) n
  have h_func : IT.hist (α := Fin K) (R := ℝ) (n + 1) = e.symm ∘
      (fun (ω : ℕ → Fin K × ℝ) => (IT.hist n ω, IT.step (n + 1) ω)) := by
    funext ω
    change frestrictLe (n + 1) ω = e.symm (frestrictLe n ω, IT.step (n + 1) ω)
    rw [show IT.step (n + 1) ω = ω (n + 1) from Prod.mk.eta]
    change frestrictLe (n + 1) ω = e.symm (e (frestrictLe (n + 1) ω))
    rw [e.symm_apply_apply]
  rw [h_func, (Measure.map_map e.symm.measurable (by fun_prop :
      Measurable (fun (ω : ℕ → Fin K × ℝ) =>
        (IT.hist n ω, IT.step (n + 1) ω)))).symm]
  congr 1
  have h_cd := (IT.isAlgEnvSeq_trajMeasure alg env).hasCondDistrib_step n
  exact ((condDistrib_ae_eq_iff_measure_eq_compProd _
    (by fun_prop : AEMeasurable (IsAlgEnvSeq.step IT.action IT.reward (n + 1)) P)
    (stepKernel alg env n)).mp h_cd.condDistrib_eq)

/-- The history distribution under any algorithm is absolutely continuous w.r.t. the
    history distribution under the uniform algorithm, for a stationary environment. -/
private lemma absolutelyContinuous_map_hist_stationary
    (hK : 0 < K) (alg : Algorithm (Fin K) ℝ)
    (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] (t : ℕ) :
    (trajMeasure alg (stationaryEnv ν)).map (IT.hist t) ≪
    (trajMeasure (Bandits.uniformAlgorithm hK) (stationaryEnv ν)).map
      (IT.hist t) := by
  induction t with
  | zero =>
    simp only [IT.hist_eq_frestrictLe, trajMeasure,
      Kernel.trajMeasure_map_frestrictLe, Kernel.partialTraj_self,
      Measure.id_comp, stationaryEnv_ν0]
    exact (Measure.AbsolutelyContinuous.compProd_left
      (absolutelyContinuous_of_forall_singleton_pos
        (uniformAlgorithm_p0_pos hK)) _).map
      (MeasurableEquiv.piUnique _).symm.measurable
  | succ n ih =>
    rw [map_hist_succ_eq_compProd_map, map_hist_succ_eq_compProd_map]
    exact (Measure.AbsolutelyContinuous.compProd ih
      (Filter.Eventually.of_forall fun h =>
        absolutelyContinuous_stepKernel_stationary hK alg ν n h)).map
      (MeasurableEquiv.IicSuccProd _ n).symm.measurable

-- `condDistrib_comp` + `eq_trajMeasure` chain requires extra heartbeats
/-- The conditional distribution of the history given the environment equals the trajectory
    measure's history marginal (for Bayesian stationary environments). -/
private lemma condDistrib_hist_env_eq_traj
    {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
    (Q : Measure E) [IsProbabilityMeasure Q]
    (κ : Kernel (Fin K × E) ℝ) [IsMarkovKernel κ]
    {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
    {A : ℕ → Ω → Fin K} {R' : ℕ → Ω → E × ℝ}
    {alg : Algorithm (Fin K) ℝ} {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsBayesAlgEnvSeq Q κ A R' alg P) (t : ℕ) :
    ∀ᵐ e ∂Q,
      condDistrib (IsBayesAlgEnvSeq.hist A R' t)
        (IsBayesAlgEnvSeq.env R') P e =
      (trajMeasure alg
        (stationaryEnv (κ.comap (·, e) (by fun_prop)))).map (IT.hist t) := by
  rw [← h.hasLaw_env.map_eq]
  have h_comp : condDistrib (IT.hist t ∘ IsBayesAlgEnvSeq.traj A R')
      (IsBayesAlgEnvSeq.env R') P
      =ᵐ[P.map (IsBayesAlgEnvSeq.env R')]
      (condDistrib (IsBayesAlgEnvSeq.traj A R')
        (IsBayesAlgEnvSeq.env R') P).map (IT.hist t) :=
    condDistrib_comp (IsBayesAlgEnvSeq.env R')
      h.measurable_traj.aemeasurable (IT.measurable_hist t)
  rw [IsBayesAlgEnvSeq.IT_hist_comp_traj (E := E) t] at h_comp
  filter_upwards [h_comp, h.condDistrib_traj_isAlgEnvSeq] with e hc he
  rw [hc, Kernel.map_apply _ (IT.measurable_hist t)]
  congr 1
  have h' := eq_trajMeasure_of_isAlgEnvSeq he
  have hid :
      (fun (ω : ℕ → Fin K × ℝ) n => (IT.action n ω, IT.reward n ω)) = id := by
    funext ω n; exact Prod.mk.eta
  rw [hid, Measure.map_id] at h'; exact h'

end AbsolutelyContinuousHist

section PosteriorEquality

variable {E' X' : Type*} {mE' : MeasurableSpace E'} {mX' : MeasurableSpace X'}

-- `compProd` unfolding requires extra heartbeats
/-- If `κ₁ =ᵐ[Q] κ₂.withDensity (fun _ => ρ)`, then the posteriors agree:
`κ₂†Q =ᵐ[κ₁ ∘ₘ Q] κ₁†Q`. -/
private theorem posterior_eq_of_withDensity_ae_eq
    [StandardBorelSpace E'] [Nonempty E']
    {Q : Measure E'} [IsFiniteMeasure Q]
    {κ₁ κ₂ : Kernel E' X'} [IsFiniteKernel κ₁] [IsFiniteKernel κ₂]
    {ρ : X' → ENNReal} (hρ : Measurable ρ)
    [IsSFiniteKernel (κ₂.withDensity (fun _ => ρ))]
    [SFinite ((κ₂ ∘ₘ Q).withDensity ρ)]
    (h_ae : κ₁ =ᵐ[Q] κ₂.withDensity (fun _ => ρ)) :
    κ₂†Q =ᵐ[κ₁ ∘ₘ Q] κ₁†Q := by
  apply ae_eq_posterior_of_compProd_eq
  have h2 : Q ⊗ₘ (κ₂.withDensity (fun _ => ρ))
      = (Q ⊗ₘ κ₂).withDensity (ρ ∘ Prod.snd) := by
    have := Measure.compProd_withDensity (κ := κ₂) (μ := Q)
      (show Measurable (Function.uncurry (fun _ => ρ)) from hρ.comp measurable_snd)
    convert this using 1
  calc (κ₁ ∘ₘ Q) ⊗ₘ (κ₂†Q)
      = ((κ₂ ∘ₘ Q).withDensity ρ) ⊗ₘ (κ₂†Q) := by
        congr 1; rw [← comp_withDensity_const hρ]; exact Measure.bind_congr_right h_ae
    _ = ((κ₂ ∘ₘ Q) ⊗ₘ (κ₂†Q)).withDensity (ρ ∘ Prod.fst) :=
        withDensity_compProd_left hρ
    _ = ((Q ⊗ₘ κ₂).map Prod.swap).withDensity (ρ ∘ Prod.fst) := by
        rw [compProd_posterior_eq_map_swap]
    _ = ((Q ⊗ₘ κ₂).withDensity (ρ ∘ Prod.snd)).map Prod.swap := by
        rw [map_swap_withDensity_fst hρ]
    _ = (Q ⊗ₘ (κ₂.withDensity (fun _ => ρ))).map Prod.swap := by rw [h2]
    _ = (Q ⊗ₘ κ₁).map Prod.swap := by rw [Measure.compProd_congr h_ae]

end PosteriorEquality

section DensityIndependence

variable {K : ℕ} [Nonempty (Fin K)]

/-- The history distribution under any algorithm is a `withDensity` of the history distribution
under the uniform algorithm, with a density that does not depend on the reward kernel `ν`.
This is the key factorization property: the density ratio only involves action probabilities. -/
private lemma exists_density_independent_of_env
    (hK : 0 < K) (alg : Algorithm (Fin K) ℝ) (t : ℕ) :
    ∃ ρ : (Iic t → Fin K × ℝ) → ENNReal, Measurable ρ ∧ (∀ h, ρ h ≠ ⊤) ∧
    ∀ (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν],
    (trajMeasure alg (stationaryEnv ν)).map (IT.hist t) =
    ((trajMeasure (Bandits.uniformAlgorithm hK) (stationaryEnv ν)).map
      (IT.hist t)).withDensity ρ := by
  set unif := Bandits.uniformAlgorithm hK
  induction t with
  | zero =>
    set e := MeasurableEquiv.piUnique (fun _ : Iic (0 : ℕ) => Fin K × ℝ)
    refine ⟨(alg.p0.rnDeriv unif.p0 ∘ Prod.fst) ∘ e,
      (Measure.measurable_rnDeriv _ _).comp (measurable_fst.comp e.measurable),
      fun h => rnDeriv_ne_top_of_forall_singleton_pos (uniformAlgorithm_p0_pos hK) _, ?_⟩
    intro ν _
    have h_ac : alg.p0 ≪ unif.p0 :=
      absolutelyContinuous_of_forall_singleton_pos (uniformAlgorithm_p0_pos hK)
    simp only [IT.hist_eq_frestrictLe, trajMeasure,
      Kernel.trajMeasure_map_frestrictLe, Kernel.partialTraj_self,
      Measure.id_comp, stationaryEnv_ν0]
    conv_lhs => rw [← Measure.withDensity_rnDeriv_eq _ _ h_ac]
    rw [withDensity_compProd_left (Measure.measurable_rnDeriv _ _)]
    exact withDensity_map_equiv_symm
      ((Measure.measurable_rnDeriv _ _).comp measurable_fst)
  | succ n ih =>
    obtain ⟨ρ_n, hρ_n_meas, hρ_n_ne_top, hρ_n⟩ := ih
    let σ : (Iic n → Fin K × ℝ) → (Fin K × ℝ) → ENNReal :=
      fun h ar => Kernel.rnDeriv (alg.policy n) (unif.policy n) h ar.1
    let e := MeasurableEquiv.IicSuccProd (fun _ : ℕ => Fin K × ℝ) n
    have hσ_meas : Measurable (Function.uncurry σ) :=
      (Kernel.measurable_rnDeriv _ _).comp
        (measurable_fst.prodMk (measurable_fst.comp measurable_snd))
    refine ⟨(ρ_n ∘ Prod.fst * Function.uncurry σ) ∘ e, ?_, ?_, ?_⟩
    · exact ((hρ_n_meas.comp measurable_fst).mul hσ_meas).comp e.measurable
    · intro h
      exact ENNReal.mul_ne_top (hρ_n_ne_top _)
        (kernel_rnDeriv_ne_top_of_forall_singleton_pos
          (fun h' a => uniformAlgorithm_policy_pos hK n h' a) _ _)
    · intro ν _inst
      have h_step : stepKernel alg (stationaryEnv ν) n =
          (stepKernel unif (stationaryEnv ν) n).withDensity σ := by
        ext h : 1
        rw [Kernel.withDensity_apply _ hσ_meas]
        have h_alg : stepKernel alg (stationaryEnv ν) n h = (alg.policy n h) ⊗ₘ ν := by
          ext s hs
          simp only [stepKernel, stationaryEnv, Kernel.compProd_apply hs,
            Measure.compProd_apply hs, Kernel.prodMkLeft_apply]
        have h_unif : stepKernel unif (stationaryEnv ν) n h = (unif.policy n h) ⊗ₘ ν := by
          ext s hs
          simp only [stepKernel, stationaryEnv, Kernel.compProd_apply hs,
            Measure.compProd_apply hs, Kernel.prodMkLeft_apply]
        have h_wd : ((unif.policy n) h).withDensity
            (Kernel.rnDeriv (alg.policy n) (unif.policy n) h) = alg.policy n h := by
          rw [← Kernel.withDensity_apply _ (Kernel.measurable_rnDeriv _ _)]
          exact Kernel.withDensity_rnDeriv_eq (κ := alg.policy n) (η := unif.policy n)
            (absolutelyContinuous_of_forall_singleton_pos (uniformAlgorithm_policy_pos hK n h))
        rw [h_alg, h_unif, ← h_wd]
        haveI : SFinite ((unif.policy n h).withDensity
            (Kernel.rnDeriv (alg.policy n) (unif.policy n) h)) := by
          rw [h_wd]; infer_instance
        exact withDensity_compProd_left
          (Kernel.measurable_rnDeriv (alg.policy n) (unif.policy n)).of_uncurry_left
      haveI : IsSFiniteKernel ((stepKernel unif (stationaryEnv ν) n).withDensity σ) := by
        rw [← h_step]; infer_instance
      rw [map_hist_succ_eq_compProd_map alg (stationaryEnv ν) n,
          map_hist_succ_eq_compProd_map unif (stationaryEnv ν) n,
          hρ_n ν, h_step,
          withDensity_compProd_withDensity hρ_n_meas hσ_meas]
      exact withDensity_map_equiv_symm
        ((hρ_n_meas.comp measurable_fst).mul hσ_meas)

end DensityIndependence

section PosteriorIndependence

/-! ### Algorithm-independence of the posterior

The key theorem: the posterior distribution on the best arm given the observed history
is independent of the algorithm used to generate the data. The proof routes through
the uniform algorithm as a reference measure. The posterior on the environment given history
is algorithm-independent (ae wrt the algorithm's own history distribution), and this
transfers to the posterior on the best arm via `condDistrib_comp`.
-/

variable {K : ℕ} [Nonempty (Fin K)]
variable {E : Type*} [MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
variable (Q : Measure E) [IsProbabilityMeasure Q]
variable (κ : Kernel (Fin K × E) ℝ) [IsMarkovKernel κ]
variable {Ω : Type*} [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
variable {A : ℕ → Ω → Fin K} {R' : ℕ → Ω → E × ℝ}
variable {alg : Algorithm (Fin K) ℝ}
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- Maps an environment to the best arm (the arm with highest mean reward). -/
noncomputable def envToBestArm (κ : Kernel (Fin K × E) ℝ) : E → Fin K :=
  measurableArgmax fun e a ↦ (κ (a, e))[id]

omit [StandardBorelSpace E] [Nonempty E] [IsMarkovKernel κ] in
lemma measurable_envToBestArm : Measurable (envToBestArm κ) :=
  measurable_measurableArgmax fun _ ↦
    stronglyMeasurable_id.integral_kernel.measurable.comp (measurable_const.prodMk measurable_id)

omit [StandardBorelSpace E] [Nonempty E] [IsMarkovKernel κ] [MeasurableSpace Ω]
    [IsProbabilityMeasure P] [Nonempty Ω] in
lemma bestArm_eq_envToBestArm_comp_env :
    IsBayesAlgEnvSeq.bestArm κ R' = envToBestArm κ ∘ IsBayesAlgEnvSeq.env R' := by
  funext ω
  simp only [Function.comp_apply, IsBayesAlgEnvSeq.bestArm, envToBestArm,
    IsBayesAlgEnvSeq.env]
  exact (measurableArgmax_eq_of_eq _ _ _ ω).trans (measurableArgmax_congr _ _ ω _ rfl)

/-- The marginal on the history equals `condDistrib (hist) (env) P ∘ₘ Q`. -/
private lemma map_hist_eq_condDistrib_comp
    {Ω' : Type*} [MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
    {A' : ℕ → Ω' → Fin K} {R'' : ℕ → Ω' → E × ℝ}
    {alg' : Algorithm (Fin K) ℝ} {P' : Measure Ω'} [IsProbabilityMeasure P']
    (h' : IsBayesAlgEnvSeq Q κ A' R'' alg' P') (t : ℕ) :
    P'.map (IsBayesAlgEnvSeq.hist A' R'' t) =
    condDistrib (IsBayesAlgEnvSeq.hist A' R'' t) (IsBayesAlgEnvSeq.env R'') P' ∘ₘ Q := by
  calc P'.map (IsBayesAlgEnvSeq.hist A' R'' t)
    _ = (P'.map (fun ω => (IsBayesAlgEnvSeq.env R'' ω,
          IsBayesAlgEnvSeq.hist A' R'' t ω))).snd :=
        (Measure.snd_map_prodMk h'.measurable_env).symm
    _ = (P'.map (IsBayesAlgEnvSeq.env R'') ⊗ₘ condDistrib
          (IsBayesAlgEnvSeq.hist A' R'' t) (IsBayesAlgEnvSeq.env R'') P').snd := by
        rw [compProd_map_condDistrib (h'.measurable_hist t).aemeasurable]
    _ = (Q ⊗ₘ condDistrib (IsBayesAlgEnvSeq.hist A' R'' t)
          (IsBayesAlgEnvSeq.env R'') P').snd := by rw [h'.hasLaw_env.map_eq]
    _ = _ := Measure.snd_compProd Q _

/-- The history distribution under any algorithm is absolutely continuous w.r.t. the
    history distribution under the uniform algorithm (since uniform gives positive
    probability to every action). -/
lemma absolutelyContinuous_map_hist_uniform
    (h : IsBayesAlgEnvSeq Q κ A R' alg P) (hK : 0 < K)
    {Ωu : Type*} [MeasurableSpace Ωu] [StandardBorelSpace Ωu] [Nonempty Ωu]
    {Au : ℕ → Ωu → Fin K} {Ru : ℕ → Ωu → E × ℝ}
    {Pu : Measure Ωu} [IsProbabilityMeasure Pu]
    (hu : IsBayesAlgEnvSeq Q κ Au Ru (Bandits.uniformAlgorithm hK) Pu)
    (t : ℕ) :
    P.map (IsBayesAlgEnvSeq.hist A R' t) ≪
    Pu.map (IsBayesAlgEnvSeq.hist Au Ru t) := by
  set κ_alg := condDistrib (IsBayesAlgEnvSeq.hist A R' t)
    (IsBayesAlgEnvSeq.env R') P
  set κ_unif := condDistrib (IsBayesAlgEnvSeq.hist Au Ru t)
    (IsBayesAlgEnvSeq.env Ru) Pu
  rw [map_hist_eq_condDistrib_comp Q κ h t, map_hist_eq_condDistrib_comp Q κ hu t,
    ← Measure.snd_compProd, ← Measure.snd_compProd]
  exact (Measure.AbsolutelyContinuous.compProd_right
    (show ∀ᵐ e ∂Q, κ_alg e ≪ κ_unif e from by
      filter_upwards [condDistrib_hist_env_eq_traj Q κ h t,
        condDistrib_hist_env_eq_traj Q κ hu t] with e he_alg he_unif
      rw [he_alg, he_unif]
      exact absolutelyContinuous_map_hist_stationary hK alg _ t)).map
    measurable_snd

/-- The posterior on the environment given history is algorithm-independent. -/
lemma condDistrib_env_hist_alg_indep
    (h : IsBayesAlgEnvSeq Q κ A R' alg P) (hK : 0 < K)
    {Ωu : Type*} [MeasurableSpace Ωu] [StandardBorelSpace Ωu] [Nonempty Ωu]
    {Au : ℕ → Ωu → Fin K} {Ru : ℕ → Ωu → E × ℝ}
    {Pu : Measure Ωu} [IsProbabilityMeasure Pu]
    (hu : IsBayesAlgEnvSeq Q κ Au Ru (Bandits.uniformAlgorithm hK) Pu)
    (t : ℕ) :
    condDistrib (IsBayesAlgEnvSeq.env R') (IsBayesAlgEnvSeq.hist A R' t) P
      =ᵐ[P.map (IsBayesAlgEnvSeq.hist A R' t)]
    condDistrib (IsBayesAlgEnvSeq.env Ru) (IsBayesAlgEnvSeq.hist Au Ru t) Pu := by
  set κ_alg := condDistrib (IsBayesAlgEnvSeq.hist A R' t) (IsBayesAlgEnvSeq.env R') P
  set κ_unif := condDistrib (IsBayesAlgEnvSeq.hist Au Ru t) (IsBayesAlgEnvSeq.env Ru) Pu
  obtain ⟨ρ, hρ_meas, hρ_ne_top, hρ⟩ := exists_density_independent_of_env hK alg t
  -- Key factorization: κ_alg =ᵐ[Q] κ_unif.withDensity (fun _ => ρ)
  have h_wd_ae : κ_alg =ᵐ[Q] κ_unif.withDensity (fun _ => ρ) := by
    filter_upwards [condDistrib_hist_env_eq_traj Q κ h t,
      condDistrib_hist_env_eq_traj Q κ hu t] with e he_alg he_unif
    rw [Kernel.withDensity_apply _
      (show Measurable (Function.uncurry (fun (_ : E) => ρ)) from hρ_meas.comp measurable_snd),
      he_alg, he_unif]
    exact hρ _
  haveI : IsSFiniteKernel (κ_unif.withDensity (fun _ => ρ)) :=
    Kernel.IsSFiniteKernel.withDensity _ (fun _ b => hρ_ne_top b)
  -- Posterior equality via density factorization
  have h_post : posterior κ_unif Q
      =ᵐ[P.map (IsBayesAlgEnvSeq.hist A R' t)] posterior κ_alg Q := by
    rw [map_hist_eq_condDistrib_comp Q κ h t]
    exact posterior_eq_of_withDensity_ae_eq hρ_meas h_wd_ae
  -- Bayes' rule for both algorithms
  have h1 := h.condDistrib_env_hist_eq_posterior t
  have h2' : condDistrib (IsBayesAlgEnvSeq.env Ru) (IsBayesAlgEnvSeq.hist Au Ru t) Pu
      =ᵐ[P.map (IsBayesAlgEnvSeq.hist A R' t)] posterior κ_unif Q :=
    (absolutelyContinuous_map_hist_uniform Q κ h hK hu t).ae_le
      (hu.condDistrib_env_hist_eq_posterior t)
  exact h1.trans (h_post.symm.trans h2'.symm)

/-- The posterior on the best arm equals the uniform algorithm's posterior. -/
lemma posteriorBestArm_eq_uniform
    (h : IsBayesAlgEnvSeq Q κ A R' alg P) (hK : 0 < K) (t : ℕ) :
    condDistrib (IsBayesAlgEnvSeq.bestArm κ R') (IsBayesAlgEnvSeq.hist A R' t) P
      =ᵐ[P.map (IsBayesAlgEnvSeq.hist A R' t)]
    IT.posteriorBestArm Q κ (Bandits.uniformAlgorithm hK) t := by
  unfold IT.posteriorBestArm
  set Pu := IT.bayesTrajMeasure Q κ (Bandits.uniformAlgorithm hK)
  set histf := IsBayesAlgEnvSeq.hist A R' t
  set histfu := IsBayesAlgEnvSeq.hist IT.action IT.reward t
  set envf := IsBayesAlgEnvSeq.env R'
  set envfu := IsBayesAlgEnvSeq.env (E := E) IT.reward
  set bau := IsBayesAlgEnvSeq.bestArm (Ω := ℕ → Fin K × E × ℝ) κ IT.reward
  have h_ITu := IT.isBayesAlgEnvSeq_bayesianTrajMeasure Q κ (Bandits.uniformAlgorithm hK)
  -- LHS: condDistrib (bestArm κ R') histf P
  --   =ᵐ (condDistrib envf histf P).map (envToBestArm κ)
  have h_comp_alg : condDistrib (IsBayesAlgEnvSeq.bestArm κ R') histf P
      =ᵐ[P.map histf] (condDistrib envf histf P).map (envToBestArm κ) := by
    rw [bestArm_eq_envToBestArm_comp_env κ]
    exact condDistrib_comp (mβ := MeasurableSpace.pi) histf
      h.measurable_env.aemeasurable (measurable_envToBestArm κ)
  -- RHS: condDistrib bau histfu Pu
  --   =ᵐ (condDistrib envfu histfu Pu).map (envToBestArm κ)
  have h_comp_unif : condDistrib bau histfu Pu
      =ᵐ[Pu.map histfu] (condDistrib envfu histfu Pu).map (envToBestArm κ) := by
    change condDistrib (IsBayesAlgEnvSeq.bestArm κ IT.reward) histfu Pu
      =ᵐ[Pu.map histfu] (condDistrib envfu histfu Pu).map (envToBestArm κ)
    rw [bestArm_eq_envToBestArm_comp_env κ]
    exact condDistrib_comp (mβ := MeasurableSpace.pi) histfu
      h_ITu.measurable_env.aemeasurable (measurable_envToBestArm κ)
  -- Environment posterior independence
  have h_env_indep := condDistrib_env_hist_alg_indep Q κ h hK h_ITu t
  -- Map both sides by envToBestArm
  have h_map_indep : (condDistrib envf histf P).map (envToBestArm κ)
      =ᵐ[P.map histf] (condDistrib envfu histfu Pu).map (envToBestArm κ) := by
    filter_upwards [h_env_indep] with x hx
    simp only [Kernel.map_apply _ (measurable_envToBestArm κ)]
    rw [hx]
  -- Transfer h_comp_unif from ae[Pu.map histfu] to ae[P.map histf]
  exact h_comp_alg.trans (h_map_indep.trans
    (h_comp_unif.filter_mono
      (absolutelyContinuous_map_hist_uniform Q κ h hK h_ITu t).ae_le).symm)

end PosteriorIndependence

end Learning
