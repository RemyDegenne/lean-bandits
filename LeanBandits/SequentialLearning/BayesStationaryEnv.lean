/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.Bandit.Regret

open MeasureTheory ProbabilityTheory Finset

namespace Learning.Bayes

variable {α R E : Type*} [mα : MeasurableSpace α] [mR : MeasurableSpace R] [mE : MeasurableSpace E]
variable (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R) [IsMarkovKernel κ]

/-- Given a prior distribution `Q` over "environments" and a kernel `k` that defines a reward
distribution `κ (a, e)` for each action `a : α` and "environment" `e : E`, a StationaryEnv
represents an environment (with an observation space `E × R`) that draws an "environment" `e : E` at
the very first step which, together with `k`, defines how the bandit process behaves. Because the
"environment" `e` is repeated at every step and reveals the best arm, it only makes sense to study
algorithms that ignore the information in `E` and just receive the information in `R`. -/
noncomputable
def StationaryEnv : Environment α (E × R) where
  feedback n :=
    let g : (Iic n → α × E × R) × α → α × E := fun (h, a) => (a, (h ⟨0, by simp⟩).2.1)
    (Kernel.deterministic (Prod.snd ∘ g) (by fun_prop)) ×ₖ (κ.comap g (by fun_prop))
  ν0 := (Kernel.const α Q) ⊗ₖ κ

variable {Ω : Type*} [MeasurableSpace Ω]
variable (P : Measure Ω) [IsProbabilityMeasure P]
variable (A : ℕ → Ω → α) (R' : ℕ → Ω → E × R)

namespace IsAlgEnvSeq

def env (ω : Ω) : E := (R' 0 ω).1

@[fun_prop]
lemma measurable_env (hR' : ∀ n, Measurable (R' n)) : Measurable (env R'):= (hR' 0).fst

def reward (n : ℕ) (ω : Ω) : R := (R' n ω).2

@[fun_prop]
lemma measurable_reward (hR' : ∀ n, Measurable (R' n)) (n : ℕ) : Measurable (reward R' n) := by
  unfold reward
  fun_prop

def hist (n : ℕ) (ω : Ω) : Iic n → α × R := fun i ↦ (A i ω, (R' i ω).2)

@[fun_prop]
lemma measurable_hist (hA : ∀ n, Measurable (A n)) (hR' : ∀ n, Measurable (R' n)) (n : ℕ) :
    Measurable (hist A R' n) := by
  unfold hist
  fun_prop

variable [StandardBorelSpace α] [Nonempty α]
variable [StandardBorelSpace E] [Nonempty E]
variable [StandardBorelSpace R] [Nonempty R]

/-- The posterior over "environments" for every given history (for a fixed algorithm). -/
noncomputable
def posterior (n : ℕ) : Kernel (Iic n → α × R) E :=
  condDistrib (env R') (hist A R' n) P

instance [StandardBorelSpace E] [Nonempty E] (n : ℕ) : IsMarkovKernel (posterior P A R' n) := by
  unfold posterior
  infer_instance

section Laws

variable (alg : Algorithm α R)

-- Revise (Claude)
lemma hasLaw_env (h : IsAlgEnvSeq A R' (alg.prod_left E) (StationaryEnv Q κ) P) :
    HasLaw (env R') Q P := by
  apply HasCondDistrib.hasLaw_of_const
  simpa [StationaryEnv] using h.hasCondDistrib_reward_zero.fst

-- Revise (Claude)
lemma hasCondDistrib_action (h : IsAlgEnvSeq A R' (alg.prod_left E) (StationaryEnv Q κ) P) (n : ℕ) :
    HasCondDistrib (A (n + 1)) (hist A R' n) (alg.policy n) P :=
  (h.hasCondDistrib_action n).comp_left (by fun_prop)

-- Revise (Claude)
lemma hasCondDistrib_reward_zero (h : IsAlgEnvSeq A R' (alg.prod_left E) (StationaryEnv Q κ) P) :
    HasCondDistrib (reward R' 0) (fun ω ↦ (A 0 ω, env R' ω)) κ P := by
  simpa [StationaryEnv] using h.hasCondDistrib_reward_zero.of_compProd

-- Revise (Claude)
lemma hasCondDistrib_reward (h : IsAlgEnvSeq A R' (alg.prod_left E) (StationaryEnv Q κ) P) (n : ℕ) :
    HasCondDistrib (reward R' (n + 1)) (fun ω ↦ (A (n + 1) ω, env R' ω)) κ P := by
  have h := (h.hasCondDistrib_reward n).snd
  simp_rw [StationaryEnv, Kernel.snd_prod] at h
  exact h.comp_left (by fun_prop)

-- Revise (Claude)
lemma hasCondDistrib_action_env_hist (h : IsAlgEnvSeq A R' (alg.prod_left E) (StationaryEnv Q κ) P)
    (n : ℕ) :
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

-- -- Revise (Claude)
lemma hasCondDistrib_reward_hist (h : IsAlgEnvSeq A R' (alg.prod_left E) (StationaryEnv Q κ) P)
    (n : ℕ) :
    HasCondDistrib (reward R' (n + 1)) (fun ω ↦ (hist A R' n ω, A (n + 1) ω, env R' ω))
      (κ.prodMkLeft _) P := by
  have h := (h.hasCondDistrib_reward n).snd
  simp_rw [StationaryEnv, Kernel.snd_prod, Kernel.prodMkLeft] at h ⊢
  have hf : Measurable (fun (p : (Iic n → α × (E × R)) × α) ↦
      ((fun i ↦ ((p.1 i).1, (p.1 i).2.2)), p.2, (p.1 ⟨0, by simp⟩).2.1)) := by fun_prop
  have h' : HasCondDistrib (reward R' (n + 1))
      (fun ω ↦ (Learning.IsAlgEnvSeq.hist A R' n ω, A (n + 1) ω))
      ((κ.comap Prod.snd (by fun_prop)).comap (fun (p : (Iic n → α × (E × R)) × α) ↦
        ((fun i ↦ ((p.1 i).1, (p.1 i).2.2)), p.2, (p.1 ⟨0, by simp⟩).2.1)) hf)
      P := by convert h using 2
  convert h'.comp_left hf using 2

variable [StandardBorelSpace Ω]

-- Revise (Claude)
lemma condIndepFun_action_env_hist (h : IsAlgEnvSeq A R' (alg.prod_left E) (StationaryEnv Q κ) P)
    (n : ℕ) :
    A (n + 1) ⟂ᵢ[hist A R' n, measurable_hist A R' h.measurable_A h.measurable_R n; P] (env R') :=
  condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft (measurable_env R' h.measurable_R)
    (h.measurable_A _) (measurable_hist A R' h.measurable_A h.measurable_R n)
    (hasCondDistrib_action_env_hist Q κ P A R' alg h n).condDistrib_eq

-- Revise (Claude)
lemma condIndepFun_reward_hist (h : IsAlgEnvSeq A R' (alg.prod_left E) (StationaryEnv Q κ) P)
    (n : ℕ) :
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

section Regret

variable (κ : Kernel (α × E) ℝ)
variable (alg : Algorithm α ℝ)

noncomputable
def regretAt (t : ℕ) (ω : Ω) : ℝ :=
  Bandits.regret (κ.comap (·, env R' ω) (by fun_prop)) A t ω

omit [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace E] [Nonempty E]
    [StandardBorelSpace R] [Nonempty R] in
lemma measurable_regretAt [Fintype α] (hA : ∀ n, Measurable (A n))
    (hR' : ∀ n, Measurable (R' n)) (t : ℕ) : Measurable (regretAt A R' κ t) := by
  unfold regretAt Bandits.regret
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
def regret [IsMarkovKernel κ] (t : ℕ) : ℝ := P[regretAt A R' κ t]

end Regret

end IsAlgEnvSeq

end Learning.Bayes
