/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.Bandit.Regret
import LeanBandits.SequentialLearning.IonescuTulceaSpace

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
    (P : Measure Ω) [IsFiniteMeasure P]
    := IsAlgEnvSeq A R' (alg.prod_left E) (bayesStationaryEnv Q κ) P

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
