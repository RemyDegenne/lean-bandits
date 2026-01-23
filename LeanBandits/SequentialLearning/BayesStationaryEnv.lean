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
variable (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R) [IsMarkovKernel κ]

noncomputable
def BayesianStationaryEnv : Environment α (E × R) where
  feedback n :=
    let g : (Iic n → α × E × R) × α → α × E := fun (h, a) => (a, (h ⟨0, by simp⟩).2.1)
    (Kernel.deterministic (Prod.snd ∘ g) (by fun_prop)) ×ₖ (κ.comap g (by fun_prop))
  ν0 := (Kernel.const α Q) ⊗ₖ κ

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

structure IsBayesianAlgEnvSeq
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace E] [Nonempty E]
    [StandardBorelSpace R] [Nonempty R]
    (A : ℕ → Ω → α) (R' : ℕ → Ω → E × R) (alg : Algorithm α R)
    (P : Measure Ω) [IsFiniteMeasure P]
    extends IsAlgEnvSeq A R' (alg.prod_left E) (BayesianStationaryEnv Q κ) P

variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (A : ℕ → Ω → α) (R' : ℕ → Ω → E × R) (alg : Algorithm α R)

def IsBayesianAlgEnvSeq.env (ω : Ω) : E := (R' 0 ω).1

@[fun_prop]
lemma IsBayesianAlgEnvSeq.measurable_env (hR' : ∀ n, Measurable (R' n)) : Measurable (env R'):=
  (hR' 0).fst

def IsBayesianAlgEnvSeq.reward (n : ℕ) (ω : Ω) : R := (R' n ω).2

@[fun_prop]
lemma IsBayesianAlgEnvSeq.measurable_reward (hR' : ∀ n, Measurable (R' n)) (n : ℕ) :
    Measurable (reward R' n) := by
  unfold reward
  fun_prop

def IsBayesianAlgEnvSeq.hist (n : ℕ) (ω : Ω) : Iic n → α × R := fun i ↦ (A i ω, (R' i ω).2)

@[fun_prop]
lemma IsBayesianAlgEnvSeq.measurable_hist (hA : ∀ n, Measurable (A n))
    (hR' : ∀ n, Measurable (R' n)) (n : ℕ) : Measurable (hist A R' n) := by
  unfold hist
  fun_prop

noncomputable
def IsBayesianAlgEnvSeq.posterior [StandardBorelSpace E] [Nonempty E] (n : ℕ) :
    Kernel (Iic n → α × R) E :=
  condDistrib (env R') (hist A R' n) P

instance (n : ℕ) [StandardBorelSpace E] [Nonempty E] :
    IsMarkovKernel (IsBayesianAlgEnvSeq.posterior P A R' n) := by
  unfold IsBayesianAlgEnvSeq.posterior
  infer_instance

section Laws

variable [StandardBorelSpace α] [Nonempty α]
variable [StandardBorelSpace E] [Nonempty E]
variable [StandardBorelSpace R] [Nonempty R]

-- (Claude)
lemma IsBayesianAlgEnvSeq.hasLaw_env (h : IsBayesianAlgEnvSeq Q κ A R' alg P) :
    HasLaw (env R') Q P := by
  apply HasCondDistrib.hasLaw_of_const
  simpa [BayesianStationaryEnv] using h.hasCondDistrib_reward_zero.fst

-- (Claude)
lemma IsBayesianAlgEnvSeq.hasCondDistrib_action' (h : IsBayesianAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    HasCondDistrib (A (n + 1)) (hist A R' n) (alg.policy n) P :=
  (h.hasCondDistrib_action n).comp_left (by fun_prop)

--(Claude)
lemma IsBayesianAlgEnvSeq.hasCondDistrib_reward_zero' (h : IsBayesianAlgEnvSeq Q κ A R' alg P) :
    HasCondDistrib (reward R' 0) (fun ω ↦ (A 0 ω, env R' ω)) κ P := by
  simpa [BayesianStationaryEnv] using h.hasCondDistrib_reward_zero.of_compProd

-- (Claude)
lemma IsBayesianAlgEnvSeq.hasCondDistrib_reward' (h : IsBayesianAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    HasCondDistrib (reward R' (n + 1)) (fun ω ↦ (A (n + 1) ω, env R' ω)) κ P := by
  have h := (h.hasCondDistrib_reward n).snd
  simp_rw [BayesianStationaryEnv, Kernel.snd_prod] at h
  exact h.comp_left (by fun_prop)

-- (Claude)
lemma IsBayesianAlgEnvSeq.hasCondDistrib_action_env_hist (h : IsBayesianAlgEnvSeq Q κ A R' alg P)
    (n : ℕ) : HasCondDistrib (A (n + 1)) (fun ω ↦ (env R' ω, hist A R' n ω))
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
lemma IsBayesianAlgEnvSeq.hasCondDistrib_reward_hist (h : IsBayesianAlgEnvSeq Q κ A R' alg P)
    (n : ℕ) :
    HasCondDistrib (reward R' (n + 1)) (fun ω ↦ (hist A R' n ω, A (n + 1) ω, env R' ω))
      (κ.prodMkLeft _) P := by
  have h := (h.hasCondDistrib_reward n).snd
  simp_rw [BayesianStationaryEnv, Kernel.snd_prod, Kernel.prodMkLeft] at h ⊢
  have hf : Measurable (fun (p : (Iic n → α × (E × R)) × α) ↦
      ((fun i ↦ ((p.1 i).1, (p.1 i).2.2)), p.2, (p.1 ⟨0, by simp⟩).2.1)) := by fun_prop
  have h' : HasCondDistrib (reward R' (n + 1))
      (fun ω ↦ (Learning.IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
      ((κ.comap Prod.snd (by fun_prop)).comap (fun (p : (Iic n → α × (E × R)) × α) ↦
        ((fun i ↦ ((p.1 i).1, (p.1 i).2.2)), p.2, (p.1 ⟨0, by simp⟩).2.1)) hf)
      P := by convert h using 2
  convert h'.comp_left hf using 2

-- (Claude)
lemma IsBayesianAlgEnvSeq.condIndepFun_action_env_hist [StandardBorelSpace Ω]
    (h : IsBayesianAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    A (n + 1) ⟂ᵢ[hist A R' n, measurable_hist A R' h.measurable_A h.measurable_R n; P] (env R') :=
  condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft (measurable_env R' h.measurable_R)
    (h.measurable_A _) (measurable_hist A R' h.measurable_A h.measurable_R n)
    (hasCondDistrib_action_env_hist Q κ P A R' alg h n).condDistrib_eq

-- Claude
lemma IsBayesianAlgEnvSeq.condIndepFun_reward_hist [StandardBorelSpace Ω]
    (h : IsBayesianAlgEnvSeq Q κ A R' alg P) (n : ℕ) :
    reward R' (n + 1)
      ⟂ᵢ[(fun ω ↦ (A (n + 1) ω, env R' ω)),
        (h.measurable_A _).prodMk (measurable_env R' h.measurable_R); P]
      hist A R' n :=
  condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    (measurable_hist A R' h.measurable_A h.measurable_R n)
    (measurable_reward R' h.measurable_R _)
    ((h.measurable_A _).prodMk (measurable_env R' h.measurable_R))
    (hasCondDistrib_reward_hist Q κ P A R' alg h n).condDistrib_eq

end Laws

section Real

variable (κ : Kernel (α × E) ℝ)
variable (A : ℕ → Ω → α) (R' : ℕ → Ω → E × ℝ) (alg : Algorithm α ℝ)

-- κ?
noncomputable
def IsBayesianAlgEnvSeq.actionValue (ω : Ω) (a : α) : ℝ := (κ (a, env R' ω))[id]

noncomputable
def IsBayesianAlgEnvSeq.bestAction [Nonempty α] [Fintype α] [Encodable α]
    [MeasurableSingletonClass α] (ω : Ω) : α := measurableArgmax (actionValue κ R') ω

noncomputable
def IsBayesianAlgEnvSeq.condDistribBestAction [StandardBorelSpace α] [Nonempty α] [Fintype α]
    [Encodable α] (n : ℕ) : Kernel (Iic n → α × ℝ) α :=
  condDistrib (bestAction κ R') (hist A R' n) P

instance [StandardBorelSpace α] [Nonempty α] [Fintype α]
    [Encodable α] (n : ℕ) :
    IsMarkovKernel (IsBayesianAlgEnvSeq.condDistribBestAction P κ A R' n) := by
  unfold IsBayesianAlgEnvSeq.condDistribBestAction
  infer_instance

noncomputable
def IsBayesianAlgEnvSeq.regret (t : ℕ) (ω : Ω) : ℝ :=
    Bandits.regret (κ.comap (·, env R' ω) (by fun_prop)) A t ω

-- Claude
lemma IsBayesianAlgEnvSeq.measurable_regret [Fintype α] (hA : ∀ n, Measurable (A n))
    (hR' : ∀ n, Measurable (R' n)) (t : ℕ) : Measurable (regret κ A R' t) := by
  unfold regret Bandits.regret
  have hmean : Measurable fun (p : α × E) ↦ (κ p)[id] :=
    stronglyMeasurable_id.integral_kernel.measurable
  apply Measurable.sub
  · apply Measurable.const_mul
    have h : ∀ a, Measurable fun (ω : Ω) ↦ (κ (a, env R' ω))[id] := fun a ↦
      hmean.comp (measurable_const.prodMk (measurable_env R' hR'))
    exact Measurable.iSup h
  · apply Finset.measurable_sum
    intro s _
    exact hmean.comp ((hA s).prodMk (measurable_env R' hR'))

noncomputable
def IsBayesianAlgEnvSeq.bayesianRegret
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace E] [Nonempty E]
    [IsMarkovKernel κ] (t : ℕ) : ℝ :=
  P[IsBayesianAlgEnvSeq.regret κ A R' t]

end Real

namespace IT

noncomputable
def bayesianTrajMeasure (alg : Algorithm α R) : Measure (ℕ → α × E × R) :=
    trajMeasure (alg.prod_left E) (BayesianStationaryEnv Q κ)
deriving IsProbabilityMeasure

lemma isBayesianAlgEnvSeq_bayesianTrajMeasure
    [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace E] [Nonempty E]
    [StandardBorelSpace R] [Nonempty R] (alg : Algorithm α R) :
    IsBayesianAlgEnvSeq Q κ action reward alg (bayesianTrajMeasure Q κ alg) :=
  ⟨isAlgEnvSeq_trajMeasure _ _⟩

end IT

end Learning
