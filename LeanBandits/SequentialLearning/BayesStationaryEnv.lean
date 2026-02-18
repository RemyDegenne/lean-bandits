/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.Bandit.Regret
import LeanBandits.SequentialLearning.StationaryEnv
import Mathlib.Probability.Kernel.Posterior

/-! # Bayesian stationary environments -/

open MeasureTheory ProbabilityTheory Finset

namespace Learning

variable {α E R : Type*} [mα : MeasurableSpace α] [mE : MeasurableSpace E] [mR : MeasurableSpace R]

/-- Given a prior distribution `Q` over "environments" and a kernel `k` that defines a reward
distribution `κ (a, e)` for each action `a : α` and "environment" `e : E`, a `bayesStationaryEnv`
corresponds to an environment (with an observation space `E × R`) that draws an "environment"
`e : E` at the very first step and defines a stationary environment from `k (·, e)`. -/
noncomputable
def bayesStationaryEnv
    (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R) [IsMarkovKernel κ] :
    Environment α (E × R) where
  feedback n :=
    let g : (Iic n → α × E × R) × α → α × E := fun (h, a) => (a, (h ⟨0, by simp⟩).2.1)
    (Kernel.deterministic (Prod.snd ∘ g) (by fun_prop)) ×ₖ (κ.comap g (by fun_prop))
  ν0 := (Kernel.const α Q) ⊗ₖ κ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- A Bayesian algorithm-environment sequence: a sequence of actions and observations from an
algorithm that ignores the underlying "environment" while interacting with a Bayesian stationary
environment. The environment `E'` is drawn from a prior `Q`, and rewards follow a kernel `κ`
conditioned on the action and environment. -/
structure IsBayesAlgEnvSeq
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R) [IsMarkovKernel κ]
    (E' : Ω → E) (A : ℕ → Ω → α) (R' : ℕ → Ω → R) (alg : Algorithm α R)
    (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  measurable_E : Measurable E' := by fun_prop
  measurable_A n : Measurable (A n) := by fun_prop
  measurable_R n : Measurable (R' n) := by fun_prop
  hasLaw_env : HasLaw E' Q P
  hasCondDistrib_action_zero : HasCondDistrib (A 0) E' (Kernel.const _ alg.p0) P
  hasCondDistrib_reward_zero : HasCondDistrib (R' 0) (fun ω ↦ (A 0 ω, E' ω)) κ P
  hasCondDistrib_action n :
    HasCondDistrib (A (n + 1)) (fun ω ↦ (E' ω, IsAlgEnvSeq.hist A R' n ω))
      ((alg.policy n).prodMkLeft _) P
  hasCondDistrib_reward n :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω, E' ω))
      (κ.prodMkLeft _) P

namespace IsBayesAlgEnvSeq

variable [StandardBorelSpace α] [Nonempty α]
variable [StandardBorelSpace R] [Nonempty R]

variable {Q : Measure E} [IsProbabilityMeasure Q] {κ : Kernel (α × E) R} [IsMarkovKernel κ]
variable {E' : Ω → E} {A : ℕ → Ω → α} {R' : ℕ → Ω → R}
variable {alg : Algorithm α R}
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The trajectory of actions and rewards as a function into the IT space. -/
def traj (A : ℕ → Ω → α) (R' : ℕ → Ω → R) (ω : Ω) : ℕ → α × R :=
  fun n => (A n ω, R' n ω)

@[fun_prop]
lemma measurable_traj (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) : Measurable (traj A R') :=
  measurable_pi_lambda _ fun n => (h.measurable_A n).prodMk (h.measurable_R n)

section Real

variable {E' : Ω → E} {R' : ℕ → Ω → ℝ}
variable {κ : Kernel (α × E) ℝ} [IsMarkovKernel κ]
variable {alg : Algorithm α ℝ}

/-- The mean of action `a : α` in the underlying "environment". -/
noncomputable
def armMean (κ : Kernel (α × E) ℝ) (E' : Ω → E) (a : α) (ω : Ω) : ℝ := (κ (a, E' ω))[id]

@[fun_prop]
lemma measurable_armMean (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) (a : α) :
    Measurable (armMean κ E' a) :=
  stronglyMeasurable_id.integral_kernel.measurable.comp (measurable_const.prodMk h.measurable_E)

/-- An action with the highest mean in the underlying "environment". -/
noncomputable
def bestArm [Fintype α] [Encodable α] (κ : Kernel (α × E) ℝ) (E' : Ω → E) :=
  measurableArgmax (fun ω a ↦ armMean κ E' a ω)

@[fun_prop]
lemma measurable_bestArm [Fintype α] [Encodable α] (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) :
    Measurable (bestArm κ E') :=
  measurable_measurableArgmax h.measurable_armMean

/-- Regret of a sequence of pulls at time `t` considering the underlying "environment". -/
noncomputable
def regret (κ : Kernel (α × E) ℝ) (A : ℕ → Ω → α) (E' : Ω → E) (t : ℕ) (ω : Ω) : ℝ :=
  Bandits.regret (κ.comap (·, E' ω) (by fun_prop)) A t ω

lemma measurable_regret [Encodable α] (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) (t : ℕ) :
    Measurable (regret κ A E' t) := by
  apply Measurable.sub
  · exact Measurable.const_mul (Measurable.iSup h.measurable_armMean) _
  · exact Finset.measurable_sum _ fun s _ ↦
      stronglyMeasurable_id.integral_kernel.measurable.comp
        ((h.measurable_A s).prodMk h.measurable_E)

/-- If `IsBayesAlgEnvSeq Q κ E' A R' alg P`, then `bayesRegret κ A E' P t` is the expected
regret at time `t` of the algorithm `alg` given a prior distribution over "environments" `Q`. -/
noncomputable
def bayesRegret (κ : Kernel (α × E) ℝ) (A : ℕ → Ω → α) (E' : Ω → E) (P : Measure Ω)
    (t : ℕ) : ℝ :=
  P[regret κ A E' t]

end Real

section Laws

lemma hasLaw_action_zero (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) :
    HasLaw (A 0) alg.p0 P :=
  h.hasCondDistrib_action_zero.hasLaw_of_const

lemma indepFun_action_zero_env [StandardBorelSpace E] [Nonempty E]
    (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) :
    IndepFun (A 0) E' P :=
  ((indepFun_iff_condDistrib_eq_const h.measurable_E.aemeasurable
    (h.measurable_A 0).aemeasurable).2 (by
      rw [h.hasLaw_action_zero.map_eq]; exact h.hasCondDistrib_action_zero.condDistrib_eq)).symm

lemma hasCondDistrib_action' (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) (n : ℕ) :
    HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R' n) (alg.policy n) P :=
  (h.hasCondDistrib_action n).comp_left (by fun_prop)

lemma hasCondDistrib_reward' (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) (n : ℕ) :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (A (n + 1) ω, E' ω)) κ P :=
  (h.hasCondDistrib_reward n).comp_left (by fun_prop)

end Laws

section Independence

lemma condIndepFun_action_env_hist [StandardBorelSpace E] [Nonempty E]
    [StandardBorelSpace Ω] (h : IsBayesAlgEnvSeq Q κ E' A R' alg P)
    (n : ℕ) :
    A (n + 1) ⟂ᵢ[IsAlgEnvSeq.hist A R' n,
      IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n; P] E' :=
  condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    h.measurable_E (h.measurable_A _) (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n)
    (h.hasCondDistrib_action n).condDistrib_eq

lemma condIndepFun_reward_hist [StandardBorelSpace Ω]
    (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) (n : ℕ) :
    R' (n + 1) ⟂ᵢ[fun ω ↦ (A (n + 1) ω, E' ω),
      (h.measurable_A (n + 1)).prodMk h.measurable_E; P] IsAlgEnvSeq.hist A R' n :=
  condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n) (h.measurable_R _)
    ((h.measurable_A _).prodMk h.measurable_E)
    (h.hasCondDistrib_reward n).condDistrib_eq

end Independence

section Posterior

variable [StandardBorelSpace E] [Nonempty E]

/-- The posterior on the environment given history equals Mathlib's `posterior` applied to the
likelihood kernel and prior. This is the measure-theoretic formulation of Bayes' rule. -/
lemma hasCondDistrib_env_hist (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) (n : ℕ) :
    HasCondDistrib E' (IsAlgEnvSeq.hist A R' n)
      (posterior (condDistrib (IsAlgEnvSeq.hist A R' n) E' P) Q) P where
  aemeasurable_fst := h.measurable_E.aemeasurable
  aemeasurable_snd :=
    (IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n).aemeasurable
  condDistrib_eq := by
    have h_env_meas : Measurable E' := h.measurable_E
    have h_hist_meas : Measurable (IsAlgEnvSeq.hist A R' n) :=
      IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n
    set κ' := condDistrib (IsAlgEnvSeq.hist A R' n) E' P with hκ'
    have h_disint : P.map (fun ω => (E' ω, IsAlgEnvSeq.hist A R' n ω)) = Q ⊗ₘ κ' := by
      rw [← h.hasLaw_env.map_eq, compProd_map_condDistrib (h_hist_meas.aemeasurable)]
    have h_marg : P.map (IsAlgEnvSeq.hist A R' n) = κ' ∘ₘ Q := by
      have : P.map (IsAlgEnvSeq.hist A R' n) =
          (P.map (fun ω => (E' ω, IsAlgEnvSeq.hist A R' n ω))).snd := by
        rw [Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)]; rfl
      rw [this, h_disint, Measure.snd_compProd]
    rw [condDistrib_ae_eq_iff_measure_eq_compProd _ h_env_meas.aemeasurable]
    rw [show P.map (fun ω => (IsAlgEnvSeq.hist A R' n ω, E' ω)) =
        (Q ⊗ₘ κ').map Prod.swap from by
      rw [← h_disint, Measure.map_map (by fun_prop) (by fun_prop)]; rfl]
    rw [← compProd_posterior_eq_map_swap (κ := κ') (μ := Q), h_marg]

end Posterior

section StationaryEnvConnection

variable [StandardBorelSpace E] [Nonempty E]

omit mα mE mR mΩ [StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace R] [Nonempty R] in
/-- The traj function commutes with IT projections: IT.action n ∘ traj = A n -/
lemma IT_action_comp_traj (n : ℕ) : IT.action n ∘ traj A R' = A n := by
  ext ω; simp [IT.action, traj]

omit mα mE mR mΩ [StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace R] [Nonempty R] in
/-- The traj function commutes with IT projections: IT.reward n ∘ traj = R' n -/
lemma IT_reward_comp_traj (n : ℕ) : IT.reward n ∘ traj A R' = R' n := by
  ext ω; simp [IT.reward, traj]

omit mα mE mR mΩ [StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace R] [Nonempty R] in
/-- The traj function commutes with IT projections: IT.hist n ∘ traj = IsAlgEnvSeq.hist n -/
lemma IT_hist_comp_traj (n : ℕ) :
    IT.hist n ∘ traj A R' = IsAlgEnvSeq.hist A R' n := by
  ext ω i : 2
  simp only [Function.comp_apply, IT.hist, traj, IsAlgEnvSeq.hist]

omit mα mE mR mΩ [StandardBorelSpace α] [Nonempty α]
  [StandardBorelSpace R] [Nonempty R] in
/-- The pair (IT.hist n, IT.action (n+1)) commutes with traj. -/
lemma IT_hist_action_comp_traj (n : ℕ) :
    (fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω)) ∘ traj A R' =
      fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω) := by
  ext ω : 1
  simp only [Function.comp_apply, IT.action, traj, Prod.mk.injEq]
  exact ⟨funext fun _ => rfl, trivial⟩

lemma condDistrib_traj_action_zero (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) :
    ∀ᵐ e ∂(P.map E'),
      (condDistrib (traj A R') E' P e).map (IT.action 0) = alg.p0 := by
  have h_comp : condDistrib (IT.action 0 ∘ traj A R') E' P
      =ᵐ[P.map E'] (condDistrib (traj A R') E' P).map (IT.action 0) :=
    condDistrib_comp E' (h.measurable_traj.aemeasurable) (IT.measurable_action 0)
  rw [IT_action_comp_traj] at h_comp
  filter_upwards [h_comp, condDistrib_of_indepFun h.indepFun_action_zero_env.symm
    h.measurable_E.aemeasurable (h.measurable_A 0).aemeasurable] with e h_comp_e h_indep_e
  rw [← Kernel.map_apply _ (IT.measurable_action 0), ← h_comp_e, h_indep_e, Kernel.const_apply]
  exact h.hasLaw_action_zero.map_eq

omit [StandardBorelSpace E] [Nonempty E] in
lemma hasCondDistrib_reward_zero_condDistrib (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) :
    ∀ᵐ e ∂(P.map E'),
      HasCondDistrib (IT.reward 0) (IT.action 0) (κ.comap (·, e) (by fun_prop))
        (condDistrib (traj A R') E' P e) := by
  have h_swap : HasCondDistrib (R' 0) (fun ω ↦ (E' ω, A 0 ω))
      (κ.comap Prod.swap (by fun_prop)) P := by
    convert h.hasCondDistrib_reward_zero.comp_right
      (MeasurableEquiv.prodComm : α × E ≃ᵐ E × α) using 2
  have h_prod := condDistrib_prod_left (h.measurable_A 0).aemeasurable
    (h.measurable_R 0).aemeasurable h.measurable_E.aemeasurable (μ := P)
  have h_comp_pair : condDistrib ((fun ω ↦ (IT.action 0 ω, IT.reward 0 ω)) ∘ traj A R') E' P
      =ᵐ[P.map E'] (condDistrib (traj A R') E' P).map
        (fun ω ↦ (IT.action 0 ω, IT.reward 0 ω)) :=
    condDistrib_comp E' h.measurable_traj.aemeasurable (by fun_prop)
  have h_comp_action : condDistrib (IT.action 0 ∘ traj A R') E' P
      =ᵐ[P.map E'] (condDistrib (traj A R') E' P).map (IT.action 0) :=
    condDistrib_comp E' h.measurable_traj.aemeasurable (IT.measurable_action 0)
  rw [show (fun ω ↦ (IT.action 0 ω, IT.reward 0 ω)) ∘ traj A R' =
      fun ω ↦ (A 0 ω, R' 0 ω) from by
    ext ω : 1; simp only [Function.comp_apply, IT.action, IT.reward, traj]] at h_comp_pair
  rw [IT_action_comp_traj] at h_comp_action
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

omit [StandardBorelSpace E] [Nonempty E] in
lemma hasCondDistrib_action_condDistrib (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) (n : ℕ) :
    ∀ᵐ e ∂(P.map E'),
      HasCondDistrib (IT.action (n + 1)) (IT.hist n) (alg.policy n)
        (condDistrib (traj A R') E' P e) := by
  have h_hist_meas := IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n
  have h_prod := condDistrib_prod_left h_hist_meas.aemeasurable
    (h.measurable_A (n + 1)).aemeasurable h.measurable_E.aemeasurable (μ := P)
  have h_action_env := (h.hasCondDistrib_action n).condDistrib_eq
  have h_comp_pair : condDistrib ((fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω)) ∘ traj A R')
      E' P =ᵐ[P.map E'] (condDistrib (traj A R') E' P).map
        (fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω)) :=
    condDistrib_comp E' h.measurable_traj.aemeasurable (by fun_prop)
  have h_comp_hist : condDistrib (IT.hist n ∘ traj A R') E' P
      =ᵐ[P.map E'] (condDistrib (traj A R') E' P).map (IT.hist n) :=
    condDistrib_comp E' h.measurable_traj.aemeasurable (IT.measurable_hist n)
  rw [IT_hist_action_comp_traj] at h_comp_pair
  rw [IT_hist_comp_traj] at h_comp_hist
  rw [(compProd_map_condDistrib h_hist_meas.aemeasurable).symm] at h_action_env
  filter_upwards [h_prod, h_comp_pair, h_comp_hist,
    (Measure.ae_compProd_iff (Kernel.measurableSet_eq _ _)).mp h_action_env]
    with e h_prod_e h_pair_e h_hist_e h_nested_e
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
  rw [← Kernel.map_apply _ (by fun_prop), ← h_pair_e]
  conv_rhs => rw [← Kernel.map_apply _ (IT.measurable_hist n), ← h_hist_e]
  rw [h_prod_e, Kernel.compProd_apply_eq_compProd_sectR]
  refine Measure.compProd_congr ?_
  filter_upwards [h_nested_e] with _ ha
  ext s _
  rw [Kernel.sectR_apply, ha, Kernel.prodMkLeft_apply]

omit [StandardBorelSpace E] [Nonempty E] in
lemma hasCondDistrib_reward_condDistrib (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) (n : ℕ) :
    ∀ᵐ e ∂(P.map E'),
      HasCondDistrib (IT.reward (n + 1)) (fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω))
        ((κ.comap (·, e) (by fun_prop)).prodMkLeft _)
        (condDistrib (traj A R') E' P e) := by
  have h_hist_meas := IsAlgEnvSeq.measurable_hist h.measurable_A h.measurable_R n
  have h_prod := condDistrib_prod_left
    (Measurable.prodMk h_hist_meas (h.measurable_A (n + 1))).aemeasurable
    (h.measurable_R (n + 1)).aemeasurable h.measurable_E.aemeasurable (μ := P)
  have h_swap : HasCondDistrib (R' (n + 1))
      (fun ω ↦ (E' ω, IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
      (κ.comap (fun p ↦ (p.2.2, p.1)) (by fun_prop)) P :=
    (h.hasCondDistrib_reward n).comp_right
      (MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm)
  have h_swap_eq := h_swap.condDistrib_eq
  have h_comp_triple : condDistrib
      ((fun ω ↦ ((IT.hist n ω, IT.action (n + 1) ω), IT.reward (n + 1) ω)) ∘ traj A R') E' P
      =ᵐ[P.map E'] (condDistrib (traj A R') E' P).map
        (fun ω ↦ ((IT.hist n ω, IT.action (n + 1) ω), IT.reward (n + 1) ω)) :=
    condDistrib_comp E' h.measurable_traj.aemeasurable (by fun_prop)
  have h_comp_pair : condDistrib ((fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω)) ∘ traj A R')
      E' P =ᵐ[P.map E'] (condDistrib (traj A R') E' P).map
        (fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω)) :=
    condDistrib_comp E' h.measurable_traj.aemeasurable (by fun_prop)
  rw [show (fun ω ↦ ((IT.hist n ω, IT.action (n + 1) ω), IT.reward (n + 1) ω)) ∘
      traj A R' = fun ω ↦ ((IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω), R' (n + 1) ω) from by
    ext ω : 1
    simp only [Function.comp_apply, IT.action, IT.reward, traj, Prod.mk.injEq]
    exact ⟨⟨funext fun i => rfl, trivial⟩, trivial⟩] at h_comp_triple
  rw [IT_hist_action_comp_traj] at h_comp_pair
  rw [(compProd_map_condDistrib (Measurable.prodMk h_hist_meas
    (h.measurable_A (n + 1))).aemeasurable).symm] at h_swap_eq
  filter_upwards [h_prod, h_comp_triple, h_comp_pair,
    (Measure.ae_compProd_iff (Kernel.measurableSet_eq _ _)).mp h_swap_eq]
    with e h_prod_e h_triple_e h_pair_e h_nested_e
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
  rw [← Kernel.map_apply _ (by fun_prop), ← h_triple_e]
  conv_rhs => rw [← Kernel.map_apply _ (by fun_prop), ← h_pair_e]
  rw [h_prod_e, Kernel.compProd_apply_eq_compProd_sectR]
  refine Measure.compProd_congr ?_
  filter_upwards [h_nested_e] with _ ha
  ext s _
  rw [Kernel.sectR_apply, ha, Kernel.comap_apply, Kernel.prodMkLeft_apply, Kernel.comap_apply]

lemma condDistrib_traj_isAlgEnvSeq (h : IsBayesAlgEnvSeq Q κ E' A R' alg P) :
    ∀ᵐ e ∂(P.map E'),
      IsAlgEnvSeq IT.action IT.reward alg
        (stationaryEnv (κ.comap (·, e) (by fun_prop)))
        (condDistrib (traj A R') E' P e) := by
  filter_upwards [condDistrib_traj_action_zero h,
    hasCondDistrib_reward_zero_condDistrib h,
    ae_all_iff.2 (hasCondDistrib_action_condDistrib h),
    ae_all_iff.2 (hasCondDistrib_reward_condDistrib h)] with e h_law h_r0 h_a h_r
  exact {
    hasLaw_action_zero := ⟨by fun_prop, h_law⟩
    hasCondDistrib_reward_zero := h_r0
    hasCondDistrib_action := h_a
    hasCondDistrib_reward := h_r
  }

end StationaryEnvConnection

end IsBayesAlgEnvSeq

/-- Bridge theorem: an `IsAlgEnvSeq` for `(alg.prod_left E)` and `(bayesStationaryEnv Q κ)`
gives rise to an `IsBayesAlgEnvSeq`. -/
theorem IsAlgEnvSeq.toIsBayesAlgEnvSeq
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace E] [Nonempty E]
    [StandardBorelSpace R] [Nonempty R]
    {Q : Measure E} [IsProbabilityMeasure Q] {κ : Kernel (α × E) R} [IsMarkovKernel κ]
    {A : ℕ → Ω → α} {R'' : ℕ → Ω → E × R} {alg : Algorithm α R}
    {P : Measure Ω} [IsProbabilityMeasure P]
    (h : IsAlgEnvSeq A R'' (alg.prod_left E) (bayesStationaryEnv Q κ) P) :
    IsBayesAlgEnvSeq Q κ (fun ω ↦ (R'' 0 ω).1) A (fun n ω ↦ (R'' n ω).2) alg P where
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
    let f : (Iic n → α × E × R) → E × (Iic n → α × R) :=
      fun h ↦ ((h ⟨0, by simp⟩).2.1, fun i ↦ ((h i).1, (h i).2.2))
    suffices h' : HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R'' n)
        (((alg.policy n).comap Prod.snd (by fun_prop)).comap f (by fun_prop)) P from
      h'.comp_left (f := f)
    exact h.hasCondDistrib_action n
  hasCondDistrib_reward n := by
    let f : (Iic n → α × E × R) × α → (Iic n → α × R) × α × E :=
      fun p ↦ ((fun i ↦ ((p.1 i).1, (p.1 i).2.2)), p.2, (p.1 ⟨0, by simp⟩).2.1)
    have hf : Measurable f := by fun_prop
    suffices h' : HasCondDistrib (fun ω ↦ (R'' (n + 1) ω).2)
        (fun ω ↦ (IsAlgEnvSeq.hist A R'' n ω, A (n + 1) ω))
        ((κ.comap Prod.snd (by fun_prop)).comap f hf) P from h'.comp_left hf
    simpa [bayesStationaryEnv, Kernel.snd_prod] using (h.hasCondDistrib_reward n).snd

namespace IT

/-- Measure on the sequence of actions and observations generated by an algorithm that ignores the
underlying "environment" while interacting with a `bayesStationaryEnv`. -/
noncomputable
def bayesTrajMeasure (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R)
    [IsMarkovKernel κ] (alg : Algorithm α R) : Measure (ℕ → α × E × R) :=
  trajMeasure (alg.prod_left E) (bayesStationaryEnv Q κ)
deriving IsProbabilityMeasure

lemma isBayesAlgEnvSeq_bayesianTrajMeasure
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace E] [Nonempty E]
    [StandardBorelSpace R] [Nonempty R]
    (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R) [IsMarkovKernel κ]
    (alg : Algorithm α R) :
    IsBayesAlgEnvSeq Q κ (fun ω ↦ (ω 0).2.1) action (fun n ω ↦ (ω n).2.2)
      alg (bayesTrajMeasure Q κ alg) :=
  (isAlgEnvSeq_trajMeasure _ _).toIsBayesAlgEnvSeq

/-- The conditional distribution over the best arm given the observed history. -/
noncomputable
def posteriorBestArm [StandardBorelSpace α] [Nonempty α] [Fintype α] [Encodable α]
    (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) ℝ) [IsMarkovKernel κ]
    (alg : Algorithm α ℝ) (n : ℕ) : Kernel (Iic n → α × ℝ) α :=
  condDistrib (IsBayesAlgEnvSeq.bestArm κ (fun ω ↦ (ω 0).2.1))
    (IsAlgEnvSeq.hist action (fun n ω ↦ (ω n).2.2) n)
    (bayesTrajMeasure Q κ alg)
deriving IsMarkovKernel

/-- The initial distribution over the best arm. -/
noncomputable
def priorBestArm [StandardBorelSpace α] [Nonempty α] [Fintype α] [Encodable α]
    (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) ℝ) [IsMarkovKernel κ]
    (alg : Algorithm α ℝ) : Measure α :=
  (bayesTrajMeasure Q κ alg).map (IsBayesAlgEnvSeq.bestArm κ (fun ω ↦ (ω 0).2.1))

instance [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace E] [Nonempty E] [Fintype α]
    [Encodable α] (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) ℝ) [IsMarkovKernel κ]
    (alg : Algorithm α ℝ) : IsProbabilityMeasure (priorBestArm Q κ alg) :=
  Measure.isProbabilityMeasure_map
    (measurable_measurableArgmax
      (IsBayesAlgEnvSeq.measurable_armMean
        (isBayesAlgEnvSeq_bayesianTrajMeasure Q κ alg))).aemeasurable

end IT

end Learning
