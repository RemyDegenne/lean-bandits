/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.Bandit.Regret
import LeanBandits.SequentialLearning.IonescuTulceaSpace

open MeasureTheory ProbabilityTheory Finset

namespace Learning

variable {α E R : Type*} [mα : MeasurableSpace α] [mE : MeasurableSpace E] [mR : MeasurableSpace R]

noncomputable
def bayesStationaryEnv
    (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R) [IsMarkovKernel κ] :
    Environment α (E × R) where
  feedback n :=
    let g : (Iic n → α × E × R) × α → α × E := fun (h, a) => (a, (h ⟨0, by simp⟩).2.1)
    (Kernel.deterministic (Prod.snd ∘ g) (by fun_prop)) ×ₖ (κ.comap g (by fun_prop))
  ν0 := (Kernel.const α Q) ⊗ₖ κ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

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

def env (R' : ℕ → Ω → E × R) (ω : Ω) : E := (R' 0 ω).1

@[fun_prop]
lemma measurable_env (h : IsBayesAlgEnvSeq Q κ A R' alg P) : Measurable (env R') :=
  (h.measurable_R 0).fst

def reward (R' : ℕ → Ω → E × R) (n : ℕ) (ω : Ω) : R := (R' n ω).2

@[fun_prop]
lemma measurable_reward (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    Measurable (reward R' n) :=
  (h.measurable_R n).snd

def hist (A : ℕ → Ω → α) (R' : ℕ → Ω → E × R) (n : ℕ) (ω : Ω) : Iic n → α × R :=
  fun i ↦ (A i ω, (R' i ω).2)

@[fun_prop]
lemma measurable_hist (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) : Measurable (hist A R' n) :=
  measurable_pi_lambda _ fun i => (h.measurable_A i).prodMk (h.measurable_R i).snd

def action_env (A : ℕ → Ω → α) (R' : ℕ → Ω → E × R) (n : ℕ) (ω : Ω) : α × E := (A n ω, (R' 0 ω).1)

@[fun_prop]
lemma measurable_action_env (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    Measurable (action_env A R' n) :=
  (h.measurable_A n).prodMk h.measurable_env

section Real

variable {R' : ℕ → Ω → E × ℝ}
variable {κ : Kernel (α × E) ℝ} [IsMarkovKernel κ]
variable {alg : Algorithm α ℝ}

noncomputable
def armMean (κ : Kernel (α × E) ℝ) (R' : ℕ → Ω → E × ℝ) (a : α) (ω : Ω) : ℝ :=
  (κ (a, env R' ω))[id]

lemma measurable_armMean (h : IsBayesAlgEnvSeq Q κ A R' alg P) (a : α) :
    Measurable (armMean κ R' a) :=
  stronglyMeasurable_id.integral_kernel.measurable.comp
    (measurable_const.prodMk h.measurable_env)

noncomputable
def bestArm (κ : Kernel (α × E) ℝ) [Fintype α] [Encodable α] (R' : ℕ → Ω → E × ℝ) :=
  measurableArgmax (fun ω a ↦ armMean κ R' a ω)

lemma measurable_bestArm [Fintype α] [Encodable α] [MeasurableSingletonClass α]
    (h : IsBayesAlgEnvSeq Q κ A R' alg P) :
    Measurable (bestArm κ R') :=
  measurable_measurableArgmax h.measurable_armMean

noncomputable
def regret (κ : Kernel (α × E) ℝ) (A : ℕ → Ω → α) (R' : ℕ → Ω → E × ℝ) (t : ℕ) (ω : Ω) : ℝ :=
  Bandits.regret (κ.comap (·, env R' ω) (by fun_prop)) A t ω

-- -- Claude
lemma measurable_regret [Fintype α] [Encodable α] (h : IsBayesAlgEnvSeq Q κ A R' alg P) (t : ℕ) :
    Measurable (regret κ A R' t) := by
  unfold regret Bandits.regret
  apply Measurable.sub
  · apply Measurable.const_mul
    exact Measurable.iSup h.measurable_armMean
  · apply Finset.measurable_sum
    intro s _
    exact stronglyMeasurable_id.integral_kernel.measurable.comp
      ((h.measurable_A s).prodMk h.measurable_env)

noncomputable
def bayesRegret (κ : Kernel (α × E) ℝ) (A : ℕ → Ω → α) (R' : ℕ → Ω → E × ℝ) (P : Measure Ω)
    (t : ℕ) : ℝ :=
  P[regret κ A R' t]

end Real

section Laws

lemma hasLaw_env (h : IsBayesAlgEnvSeq Q κ A R' alg P) : HasLaw (env R') Q P := by
  apply HasCondDistrib.hasLaw_of_const
  simpa [bayesStationaryEnv] using h.hasCondDistrib_reward_zero.fst

-- (Claude)
lemma hasCondDistrib_action' (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    HasCondDistrib (A (n + 1)) (hist A R' n) (alg.policy n) P :=
  (h.hasCondDistrib_action n).comp_left (by fun_prop)

--(Claude)
lemma hasCondDistrib_reward_zero' (h : IsBayesAlgEnvSeq Q κ A R' alg P) :
    HasCondDistrib (reward R' 0) (action_env A R' 0) κ P := by
  simpa [bayesStationaryEnv] using h.hasCondDistrib_reward_zero.of_compProd

-- (Claude)
lemma hasCondDistrib_reward' (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    HasCondDistrib (reward R' (n + 1)) (action_env A R' (n + 1)) κ P := by
  have h := (h.hasCondDistrib_reward n).snd
  simp_rw [bayesStationaryEnv, Kernel.snd_prod] at h
  exact h.comp_left (by fun_prop)

-- (Claude)
lemma hasCondDistrib_action_env_hist (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    HasCondDistrib (A (n + 1)) (fun ω ↦ (env R' ω, hist A R' n ω))
      ((alg.policy n).prodMkLeft E) P := by
  have h := h.hasCondDistrib_action n
  simp only [Algorithm.prod_left, Kernel.prodMkLeft] at h ⊢
  have hf : Measurable (fun h : Iic n → α × E × R ↦
      ((h ⟨0, by simp⟩).2.1, fun i ↦ ((h i).1, (h i).2.2))) := by fun_prop
  have h' : HasCondDistrib (A (n + 1)) (Learning.IsAlgEnvSeq.hist A R' n)
      (((alg.policy n).comap Prod.snd (by fun_prop)).comap
        (fun h : Iic n → α × E × R ↦ ((h ⟨0, by simp⟩).2.1, fun i ↦ ((h i).1, (h i).2.2))) hf)
      P := by convert h using 2
  convert h'.comp_left hf using 2

-- -- (Claude)
lemma hasCondDistrib_reward_hist_action_env (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    HasCondDistrib (reward R' (n + 1)) (fun ω ↦ (hist A R' n ω, A (n + 1) ω, env R' ω))
      (κ.prodMkLeft _) P := by
  have h := (h.hasCondDistrib_reward n).snd
  simp_rw [bayesStationaryEnv, Kernel.snd_prod, Kernel.prodMkLeft] at h ⊢
  have hf : Measurable (fun (p : (Iic n → α × (E × R)) × α) ↦
      ((fun i ↦ ((p.1 i).1, (p.1 i).2.2)), p.2, (p.1 ⟨0, by simp⟩).2.1)) := by fun_prop
  have h' : HasCondDistrib (reward R' (n + 1))
      (fun ω ↦ (Learning.IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
      ((κ.comap Prod.snd (by fun_prop)).comap (fun (p : (Iic n → α × (E × R)) × α) ↦
        ((fun i ↦ ((p.1 i).1, (p.1 i).2.2)), p.2, (p.1 ⟨0, by simp⟩).2.1)) hf)
      P := by convert h using 2
  convert h'.comp_left hf using 2

-- (Claude)
lemma condIndepFun_action_env_hist [StandardBorelSpace Ω] (h : IsBayesAlgEnvSeq Q κ A R' alg P)
    (n : ℕ) : A (n + 1) ⟂ᵢ[hist A R' n, h.measurable_hist n; P] (env R') :=
  condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    (h.measurable_env) (h.measurable_A _) (h.measurable_hist n)
    (hasCondDistrib_action_env_hist h n).condDistrib_eq

-- Claude
lemma condIndepFun_reward_hist_action_env [StandardBorelSpace Ω]
    (h : IsBayesAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    reward R' (n + 1) ⟂ᵢ[action_env A R' (n + 1), h.measurable_action_env (n + 1); P]
      hist A R' n :=
  condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    (h.measurable_hist n) (h.measurable_reward _) (h.measurable_action_env _)
    (hasCondDistrib_reward_hist_action_env h n).condDistrib_eq

end Laws

end IsBayesAlgEnvSeq

namespace IT

variable [StandardBorelSpace α] [Nonempty α]
variable [StandardBorelSpace E] [Nonempty E]
variable [StandardBorelSpace R] [Nonempty R]

noncomputable
def bayesTrajMeasure (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R)
    [IsMarkovKernel κ] (alg : Algorithm α R) : Measure (ℕ → α × E × R) :=
    trajMeasure (alg.prod_left E) (bayesStationaryEnv Q κ)
deriving IsProbabilityMeasure

lemma isBayesAlgEnvSeq_bayesianTrajMeasure
     (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R) [IsMarkovKernel κ]
     (alg : Algorithm α R) : IsBayesAlgEnvSeq Q κ action reward alg (bayesTrajMeasure Q κ alg) :=
  isAlgEnvSeq_trajMeasure _ _

noncomputable
def posteriorBestArm [Fintype α] [Encodable α] (Q : Measure E) [IsProbabilityMeasure Q]
    (κ : Kernel (α × E) ℝ) [IsMarkovKernel κ] (alg : Algorithm α ℝ) (n : ℕ) :
    Kernel (Iic n → α × ℝ) α :=
  condDistrib (IsBayesAlgEnvSeq.bestArm κ reward) (IsBayesAlgEnvSeq.hist action reward n)
    (IT.bayesTrajMeasure Q κ alg)
deriving IsMarkovKernel

noncomputable
def priorBestArm [Fintype α] [Encodable α] (Q : Measure E) [IsProbabilityMeasure Q]
    (κ : Kernel (α × E) ℝ) [IsMarkovKernel κ] (alg : Algorithm α ℝ) : Measure α :=
  (bayesTrajMeasure Q κ alg).map (IsBayesAlgEnvSeq.bestArm κ IT.reward)

instance [Fintype α] [Encodable α] [MeasurableSingletonClass α]
    (Q : Measure E) [IsProbabilityMeasure Q]
    (κ : Kernel (α × E) ℝ) [IsMarkovKernel κ] (alg : Algorithm α ℝ) :
    IsProbabilityMeasure (priorBestArm Q κ alg) :=
  Measure.isProbabilityMeasure_map
    (measurable_measurableArgmax
      (IsBayesAlgEnvSeq.measurable_armMean
        (isBayesAlgEnvSeq_bayesianTrajMeasure Q κ alg))).aemeasurable

end IT

end Learning
