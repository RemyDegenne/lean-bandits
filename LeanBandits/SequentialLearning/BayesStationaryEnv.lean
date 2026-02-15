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
algorithm that ignores the underlying "environment" while interacting with `bayesStationaryEnv`. -/
def IsBayesAlgEnvSeq
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace E] [Nonempty E]
    [StandardBorelSpace R] [Nonempty R]
    (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R) [IsMarkovKernel κ]
    (A : ℕ → Ω → α) (R' : ℕ → Ω → E × R) (alg : Algorithm α R)
    (P : Measure Ω) [IsFiniteMeasure P] :=
  IsAlgEnvSeq A R' (alg.prod_left E) (bayesStationaryEnv Q κ) P

namespace IsBayesAlgEnvSeq

variable [StandardBorelSpace α] [Nonempty α]
variable [StandardBorelSpace E] [Nonempty E]
variable [StandardBorelSpace R] [Nonempty R]

variable {Q : Measure E} [IsProbabilityMeasure Q] {κ : Kernel (α × E) R} [IsMarkovKernel κ]
variable {A : ℕ → Ω → α} {R' : ℕ → Ω → E × R}
variable {alg : Algorithm α R}
variable {P : Measure Ω} [IsProbabilityMeasure P]

/-- The underlying "environment". -/
def env (R' : ℕ → Ω → E × R) (ω : Ω) : E := (R' 0 ω).1

@[fun_prop]
lemma measurable_env (h : IsBayesAlgEnvSeq Q κ A R' alg P) : Measurable (env R') :=
  (h.measurable_R 0).fst

/-- The reward at time `n`. -/
def reward (R' : ℕ → Ω → E × R) (n : ℕ) (ω : Ω) : R := (R' n ω).2

@[fun_prop]
lemma measurable_reward (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) : Measurable (reward R' n) :=
  (h.measurable_R n).snd

/-- The history of actions and rewards up to time `n`. -/
def hist (A : ℕ → Ω → α) (R' : ℕ → Ω → E × R) (n : ℕ) (ω : Ω) : Iic n → α × R :=
  fun i ↦ (A i ω, (R' i ω).2)

@[fun_prop]
lemma measurable_hist (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) : Measurable (hist A R' n) :=
  measurable_pi_iff.2 fun i => ((h.measurable_A i).prodMk (h.measurable_R i).snd)

/-- The action at time `n` together with the underlying "environment". -/
def action_env (A : ℕ → Ω → α) (R' : ℕ → Ω → E × R) (n : ℕ) (ω : Ω) : α × E := (A n ω, (R' 0 ω).1)

@[fun_prop]
lemma measurable_action_env (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    Measurable (action_env A R' n) :=
  (h.measurable_A n).prodMk h.measurable_env

section Real

variable {R' : ℕ → Ω → E × ℝ}
variable {κ : Kernel (α × E) ℝ} [IsMarkovKernel κ]
variable {alg : Algorithm α ℝ}

/-- The mean of action `a : α` in the underlying "environment". -/
noncomputable
def armMean (κ : Kernel (α × E) ℝ) (R' : ℕ → Ω → E × ℝ) (a : α) (ω : Ω) : ℝ := (κ (a, env R' ω))[id]

@[fun_prop]
lemma measurable_armMean (h : IsBayesAlgEnvSeq Q κ A R' alg P) (a : α) :
    Measurable (armMean κ R' a) :=
  stronglyMeasurable_id.integral_kernel.measurable.comp (measurable_const.prodMk h.measurable_env)

/-- An action with the highest mean in the underlying "environment". -/
noncomputable
def bestArm [Fintype α] [Encodable α] (κ : Kernel (α × E) ℝ) (R' : ℕ → Ω → E × ℝ) :=
  measurableArgmax (fun ω a ↦ armMean κ R' a ω)

@[fun_prop]
lemma measurable_bestArm [Fintype α] [Encodable α] (h : IsBayesAlgEnvSeq Q κ A R' alg P) :
    Measurable (bestArm κ R') :=
  measurable_measurableArgmax h.measurable_armMean

/-- Regret of a sequence of pulls at time `t` considering the underlying "environment". -/
noncomputable
def regret (κ : Kernel (α × E) ℝ) (A : ℕ → Ω → α) (R' : ℕ → Ω → E × ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Bandits.regret (κ.comap (·, env R' ω) (by fun_prop)) A t ω

lemma measurable_regret [Encodable α] (h : IsBayesAlgEnvSeq Q κ A R' alg P) (t : ℕ) :
    Measurable (regret κ A R' t) := by
  apply Measurable.sub
  · exact Measurable.const_mul (Measurable.iSup h.measurable_armMean) _
  · exact Finset.measurable_sum _ fun s _ ↦
      stronglyMeasurable_id.integral_kernel.measurable.comp (h.measurable_action_env s)

/-- If `IsBayesAlgEnvSeq Q κ A R' alg P`, then `bayesRegret κ A R' P t` is the expected
regret at time `t` of the algorithm `alg` given a prior distribution over "environments" `Q`. -/
noncomputable
def bayesRegret (κ : Kernel (α × E) ℝ) (A : ℕ → Ω → α) (R' : ℕ → Ω → E × ℝ) (P : Measure Ω)
    (t : ℕ) : ℝ :=
  P[regret κ A R' t]

end Real

section Laws

lemma hasLaw_env (h : IsBayesAlgEnvSeq Q κ A R' alg P) : HasLaw (env R') Q P := by
  apply HasCondDistrib.hasLaw_of_const
  simpa [bayesStationaryEnv] using h.hasCondDistrib_reward_zero.fst

lemma hasCondDistrib_action' (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    HasCondDistrib (A (n + 1)) (hist A R' n) (alg.policy n) P :=
  (h.hasCondDistrib_action n).comp_left (by fun_prop)

lemma hasCondDistrib_reward_zero' (h : IsBayesAlgEnvSeq Q κ A R' alg P) :
    HasCondDistrib (reward R' 0) (action_env A R' 0) κ P := by
  simpa [bayesStationaryEnv] using h.hasCondDistrib_reward_zero.of_compProd

lemma hasCondDistrib_reward' (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    HasCondDistrib (reward R' (n + 1)) (action_env A R' (n + 1)) κ P := by
  have hr := (h.hasCondDistrib_reward n).snd
  simp_rw [bayesStationaryEnv, Kernel.snd_prod] at hr
  exact hr.comp_left (by fun_prop)

-- Auxiliary lemma for `condIndepFun_action_env_hist` (Claude)
lemma hasCondDistrib_action_env_hist (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    HasCondDistrib (A (n + 1)) (fun ω ↦ (env R' ω, hist A R' n ω))
      ((alg.policy n).prodMkLeft E) P := by
  let f : (Iic n → α × E × R) → E × (Iic n → α × R) :=
    fun h ↦ ((h ⟨0, by simp⟩).2.1, fun i ↦ ((h i).1, (h i).2.2))
  suffices h' : HasCondDistrib (A (n + 1)) (IsAlgEnvSeq.hist A R' n)
      (((alg.policy n).comap Prod.snd (by fun_prop)).comap f (by fun_prop)) P from h'.comp_left
  exact h.hasCondDistrib_action n

-- Auxiliary lemma for `condIndepFun_reward_hist_action_env` (Claude)
lemma hasCondDistrib_reward_hist_action_env (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    HasCondDistrib (reward R' (n + 1)) (fun ω ↦ (hist A R' n ω, A (n + 1) ω, env R' ω))
      (κ.prodMkLeft _) P := by
  let f : (Iic n → α × E × R) × α → (Iic n → α × R) × α × E :=
    fun p ↦ ((fun i ↦ ((p.1 i).1, (p.1 i).2.2)), p.2, (p.1 ⟨0, by simp⟩).2.1)
  have hf : Measurable f := by fun_prop
  suffices h' : HasCondDistrib (reward R' (n + 1))
      (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
      ((κ.comap Prod.snd (by fun_prop)).comap f hf) P from h'.comp_left hf
  simpa [bayesStationaryEnv, Kernel.snd_prod] using (h.hasCondDistrib_reward n).snd

end Laws

section Independence

lemma indepFun_action_zero_env (h : IsBayesAlgEnvSeq Q κ A R' alg P) :
    IndepFun (A 0) (env R') P := by
  rw [indepFun_iff_condDistrib_eq_const (h.measurable_A 0).aemeasurable
    h.measurable_env.aemeasurable, h.hasLaw_env.map_eq]
  simpa [bayesStationaryEnv] using h.hasCondDistrib_reward_zero.fst.condDistrib_eq

lemma condIndepFun_action_env_hist [StandardBorelSpace Ω] (h : IsBayesAlgEnvSeq Q κ A R' alg P)
    (n : ℕ) : A (n + 1) ⟂ᵢ[hist A R' n, h.measurable_hist n; P] (env R') :=
  condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    (h.measurable_env) (h.measurable_A _) (h.measurable_hist n)
    (hasCondDistrib_action_env_hist h n).condDistrib_eq

lemma condIndepFun_reward_hist_action_env [StandardBorelSpace Ω]
    (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    reward R' (n + 1) ⟂ᵢ[action_env A R' (n + 1), h.measurable_action_env (n + 1); P] hist A R' n :=
  condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    (h.measurable_hist n) (h.measurable_reward _) (h.measurable_action_env _)
    (hasCondDistrib_reward_hist_action_env h n).condDistrib_eq

end Independence

section Posterior

/-- The posterior on the environment given history equals Mathlib's `posterior` applied to the
likelihood kernel and prior. This is the measure-theoretic formulation of Bayes' rule. -/
lemma condDistrib_env_hist_eq_posterior (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    condDistrib (env R') (hist A R' n) P
      =ᵐ[P.map (hist A R' n)] posterior (condDistrib (hist A R' n) (env R') P) Q := by
  -- The key is to show P.map (env, hist) = Q ⊗ₘ condDistrib hist env P
  -- Then use compProd_posterior_eq_map_swap and uniqueness of conditional kernels
  have h_env_meas : Measurable (env R') := h.measurable_env
  have h_hist_meas : Measurable (hist A R' n) := h.measurable_hist n
  set κ' := condDistrib (hist A R' n) (env R') P with hκ'
  have h_disint : P.map (fun ω => (env R' ω, hist A R' n ω)) = Q ⊗ₘ κ' := by
    rw [← h.hasLaw_env.map_eq, compProd_map_condDistrib (h_hist_meas.aemeasurable)]
  have h_marg : P.map (hist A R' n) = κ' ∘ₘ Q := by
    have : P.map (hist A R' n) = (P.map (fun ω => (env R' ω, hist A R' n ω))).snd := by
      rw [Measure.snd, Measure.map_map (by fun_prop) (by fun_prop)]; rfl
    rw [this, h_disint, Measure.snd_compProd]
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
  rw [show P.map (fun ω => (hist A R' n ω, env R' ω)) = (Q ⊗ₘ κ').map Prod.swap from by
    rw [← h_disint, Measure.map_map (by fun_prop) (by fun_prop)]; rfl]
  rw [← compProd_posterior_eq_map_swap (κ := κ') (μ := Q), h_marg]

end Posterior

section StationaryEnvConnection

def traj (A : ℕ → Ω → α) (R' : ℕ → Ω → E × R) (ω : Ω) : ℕ → α × R :=
  fun n => (A n ω, (R' n ω).2)

@[fun_prop]
lemma measurable_traj (h : IsBayesAlgEnvSeq Q κ A R' alg P) : Measurable (traj A R') :=
  measurable_pi_lambda _ fun n => (h.measurable_A n).prodMk (h.measurable_R n).snd

omit mα mE mR mΩ [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace E] [Nonempty E]
  [StandardBorelSpace R] [Nonempty R] in
/-- The traj function commutes with IT projections: IT.action n ∘ traj = A n -/
lemma IT_action_comp_traj (n : ℕ) : IT.action n ∘ traj A R' = A n := by
  ext ω; simp [IT.action, traj]

omit mα mE mR mΩ [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace E] [Nonempty E]
  [StandardBorelSpace R] [Nonempty R] in
/-- The traj function commutes with IT projections: IT.reward n ∘ traj = reward n -/
lemma IT_reward_comp_traj (n : ℕ) : IT.reward n ∘ traj A R' = reward R' n := by
  ext ω; simp [IT.reward, traj, reward]

omit mα mE mR mΩ [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace E] [Nonempty E]
  [StandardBorelSpace R] [Nonempty R] in
/-- The traj function commutes with IT projections: IT.hist n ∘ traj = hist n -/
lemma IT_hist_comp_traj (n : ℕ) : IT.hist n ∘ traj A R' = hist A R' n := by
  ext ω i : 2
  simp only [Function.comp_apply, IT.hist, traj, hist]

omit mα mE mR mΩ [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace E] [Nonempty E]
  [StandardBorelSpace R] [Nonempty R] in
/-- The pair (IT.hist n, IT.action (n+1)) commutes with traj. -/
lemma IT_hist_action_comp_traj (n : ℕ) :
    (fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω)) ∘ traj A R' =
      fun ω ↦ (hist A R' n ω, A (n + 1) ω) := by
  ext ω : 1
  simp only [Function.comp_apply, IT.action, traj, Prod.mk.injEq]
  exact ⟨funext fun _ => rfl, trivial⟩

lemma condDistrib_traj_action_zero (h : IsBayesAlgEnvSeq Q κ A R' alg P) :
    ∀ᵐ e ∂(P.map (env R')),
      (condDistrib (traj A R') (env R') P e).map (IT.action 0) = alg.p0 := by
  have h_comp : condDistrib (IT.action 0 ∘ traj A R') (env R') P
      =ᵐ[P.map (env R')] (condDistrib (traj A R') (env R') P).map (IT.action 0) :=
    condDistrib_comp (env R') (h.measurable_traj.aemeasurable) (IT.measurable_action 0)
  rw [IT_action_comp_traj] at h_comp
  filter_upwards [h_comp, condDistrib_of_indepFun h.indepFun_action_zero_env.symm
    h.measurable_env.aemeasurable (h.measurable_A 0).aemeasurable] with e h_comp_e h_indep_e
  rw [← Kernel.map_apply _ (IT.measurable_action 0), ← h_comp_e, h_indep_e, Kernel.const_apply]
  simp only [h.hasLaw_action_zero.map_eq, Algorithm.prod_left]

lemma hasCondDistrib_reward_zero_condDistrib (h : IsBayesAlgEnvSeq Q κ A R' alg P) :
    ∀ᵐ e ∂(P.map (env R')),
      HasCondDistrib (IT.reward 0) (IT.action 0) (κ.comap (·, e) (by fun_prop))
        (condDistrib (traj A R') (env R') P e) := by
  have h_swap : HasCondDistrib (reward R' 0) (fun ω ↦ (env R' ω, A 0 ω))
      (κ.comap Prod.swap (by fun_prop)) P := by
    convert h.hasCondDistrib_reward_zero'.comp_right
      (MeasurableEquiv.prodComm : α × E ≃ᵐ E × α) using 2
  have h_prod := condDistrib_prod_left (h.measurable_A 0).aemeasurable
    (h.measurable_reward 0).aemeasurable h.measurable_env.aemeasurable (μ := P)
  have h_comp_pair : condDistrib ((fun ω ↦ (IT.action 0 ω, IT.reward 0 ω)) ∘ traj A R') (env R') P
      =ᵐ[P.map (env R')] (condDistrib (traj A R') (env R') P).map
        (fun ω ↦ (IT.action 0 ω, IT.reward 0 ω)) :=
    condDistrib_comp (env R') h.measurable_traj.aemeasurable (by fun_prop)
  have h_comp_action : condDistrib (IT.action 0 ∘ traj A R') (env R') P
      =ᵐ[P.map (env R')] (condDistrib (traj A R') (env R') P).map (IT.action 0) :=
    condDistrib_comp (env R') h.measurable_traj.aemeasurable (IT.measurable_action 0)
  rw [show (fun ω ↦ (IT.action 0 ω, IT.reward 0 ω)) ∘ traj A R' =
      fun ω ↦ (A 0 ω, reward R' 0 ω) from by
    ext ω : 1; simp only [Function.comp_apply, IT.action, IT.reward, traj, reward]] at h_comp_pair
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

lemma hasCondDistrib_action_condDistrib (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    ∀ᵐ e ∂(P.map (env R')),
      HasCondDistrib (IT.action (n + 1)) (IT.hist n) (alg.policy n)
        (condDistrib (traj A R') (env R') P e) := by
  have h_prod := condDistrib_prod_left (h.measurable_hist n).aemeasurable
    (h.measurable_A (n + 1)).aemeasurable h.measurable_env.aemeasurable (μ := P)
  have h_action_env := (hasCondDistrib_action_env_hist h n).condDistrib_eq
  have h_comp_pair : condDistrib ((fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω)) ∘ traj A R')
      (env R') P =ᵐ[P.map (env R')] (condDistrib (traj A R') (env R') P).map
        (fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω)) :=
    condDistrib_comp (env R') h.measurable_traj.aemeasurable (by fun_prop)
  have h_comp_hist : condDistrib (IT.hist n ∘ traj A R') (env R') P
      =ᵐ[P.map (env R')] (condDistrib (traj A R') (env R') P).map (IT.hist n) :=
    condDistrib_comp (env R') h.measurable_traj.aemeasurable (IT.measurable_hist n)
  rw [IT_hist_action_comp_traj] at h_comp_pair
  rw [IT_hist_comp_traj] at h_comp_hist
  rw [(compProd_map_condDistrib (h.measurable_hist n).aemeasurable).symm] at h_action_env
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

lemma hasCondDistrib_reward_condDistrib (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    ∀ᵐ e ∂(P.map (env R')),
      HasCondDistrib (IT.reward (n + 1)) (fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω))
        ((κ.comap (·, e) (by fun_prop)).prodMkLeft _)
        (condDistrib (traj A R') (env R') P e) := by
  have h_prod := condDistrib_prod_left
    (Measurable.prodMk (h.measurable_hist n) (h.measurable_A (n + 1))).aemeasurable
    (h.measurable_reward (n + 1)).aemeasurable h.measurable_env.aemeasurable (μ := P)
  have h_swap : HasCondDistrib (reward R' (n + 1)) (fun ω ↦ (env R' ω, hist A R' n ω, A (n + 1) ω))
      (κ.comap (fun p ↦ (p.2.2, p.1)) (by fun_prop)) P :=
    (hasCondDistrib_reward_hist_action_env h n).comp_right
      (MeasurableEquiv.prodAssoc.symm.trans MeasurableEquiv.prodComm)
  have h_swap_eq := h_swap.condDistrib_eq
  have h_comp_triple : condDistrib
      ((fun ω ↦ ((IT.hist n ω, IT.action (n + 1) ω), IT.reward (n + 1) ω)) ∘ traj A R') (env R') P
      =ᵐ[P.map (env R')] (condDistrib (traj A R') (env R') P).map
        (fun ω ↦ ((IT.hist n ω, IT.action (n + 1) ω), IT.reward (n + 1) ω)) :=
    condDistrib_comp (env R') h.measurable_traj.aemeasurable (by fun_prop)
  have h_comp_pair : condDistrib ((fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω)) ∘ traj A R')
      (env R') P =ᵐ[P.map (env R')] (condDistrib (traj A R') (env R') P).map
        (fun ω ↦ (IT.hist n ω, IT.action (n + 1) ω)) :=
    condDistrib_comp (env R') h.measurable_traj.aemeasurable (by fun_prop)
  rw [show (fun ω ↦ ((IT.hist n ω, IT.action (n + 1) ω), IT.reward (n + 1) ω)) ∘
      traj A R' = fun ω ↦ ((hist A R' n ω, A (n + 1) ω), reward R' (n + 1) ω) from by
    ext ω : 1
    simp only [Function.comp_apply, IT.action, IT.reward, traj, reward, Prod.mk.injEq]
    exact ⟨⟨funext fun i => rfl, trivial⟩, trivial⟩] at h_comp_triple
  rw [IT_hist_action_comp_traj] at h_comp_pair
  rw [(compProd_map_condDistrib (Measurable.prodMk (h.measurable_hist n)
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

lemma condDistrib_traj_isAlgEnvSeq (h : IsBayesAlgEnvSeq Q κ A R' alg P) :
    ∀ᵐ e ∂(P.map (env R')),
      IsAlgEnvSeq IT.action IT.reward alg
        (stationaryEnv (κ.comap (·, e) (by fun_prop)))
        (condDistrib (traj A R') (env R') P e) := by
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
    (alg : Algorithm α R) : IsBayesAlgEnvSeq Q κ action reward alg (bayesTrajMeasure Q κ alg) :=
  isAlgEnvSeq_trajMeasure _ _

/-- The conditional distribution over the best arm given the observed history. -/
noncomputable
def posteriorBestArm [StandardBorelSpace α] [Nonempty α] [Fintype α] [Encodable α]
    (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) ℝ) [IsMarkovKernel κ]
    (alg : Algorithm α ℝ) (n : ℕ) : Kernel (Iic n → α × ℝ) α :=
  condDistrib (IsBayesAlgEnvSeq.bestArm κ reward) (IsBayesAlgEnvSeq.hist action reward n)
    (bayesTrajMeasure Q κ alg)
deriving IsMarkovKernel

/-- The initial distribution over the best arm. -/
noncomputable
def priorBestArm [StandardBorelSpace α] [Nonempty α] [Fintype α] [Encodable α]
    (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) ℝ) [IsMarkovKernel κ]
    (alg : Algorithm α ℝ) : Measure α :=
  (bayesTrajMeasure Q κ alg).map (IsBayesAlgEnvSeq.bestArm κ reward)

instance [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace E] [Nonempty E] [Fintype α]
    [Encodable α] (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) ℝ) [IsMarkovKernel κ]
    (alg : Algorithm α ℝ) : IsProbabilityMeasure (priorBestArm Q κ alg) :=
  Measure.isProbabilityMeasure_map
    (measurable_measurableArgmax
      (IsBayesAlgEnvSeq.measurable_armMean
        (isBayesAlgEnvSeq_bayesianTrajMeasure Q κ alg))).aemeasurable

end IT

end Learning
