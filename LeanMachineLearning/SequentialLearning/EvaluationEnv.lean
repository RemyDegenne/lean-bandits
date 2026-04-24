/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/
module

public import LeanMachineLearning.SequentialLearning.StationaryEnv
public import LeanMachineLearning.Probability.Independence.CondDistrib

/-!
# Function evaluation environments

A stationary environment where the reward is given by evaluating a fixed measurable function `f` at
the chosen action.

## Main definitions

* `evalEnv hf`: A stationary environment where the reward is given by a deterministic kernel that
  evaluates a fixed measurable function at the chosen action.

## Main statements

* `reward_ae_eq_evals_actions`: For almost all `ω`, the reward at time `n` is equal to `f`
  evaluated at the action taken at time `n`.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory

namespace Learning

variable {α R : Type*} [MeasurableSpace α] [MeasurableSpace R]

/-- The evaluation environment where the reward is given by evaluating a fixed measurable function
`f` at the chosen action. -/
noncomputable def evalEnv {f : α → R} (hf : Measurable f) :=
  stationaryEnv <| Kernel.deterministic f hf

namespace EvalEnv

variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm α R} {f : α → R} {hf : Measurable f}
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → α} {R' : ℕ → Ω → R}

lemma hascondDistrib_reward_evalEnv (h : IsAlgEnvSeq A R' alg (evalEnv hf) P) (n : ℕ) :
    HasCondDistrib (R' n) (A n) (Kernel.deterministic f hf) P :=
  have hRn := h.measurable_R n
  have hAn := h.measurable_A n
  ⟨hRn.aemeasurable, hAn.aemeasurable, h.condDistrib_reward_stationaryEnv n⟩

lemma reward_ae_eq_eval_action (h : IsAlgEnvSeq A R' alg (evalEnv hf) P) (n : ℕ) :
    R' n =ᵐ[P] f ∘ A n :=
  ae_eq_of_condDistrib_eq_deterministic hf (h.measurable_A n).aemeasurable
    (h.measurable_R n).aemeasurable (hascondDistrib_reward_evalEnv h n).condDistrib_eq

lemma reward_ae_eq_evals_actions (h : IsAlgEnvSeq A R' alg (evalEnv hf) P) :
    ∀ᵐ ω ∂P, ∀ n, R' n ω = f (A n ω) := by
  rw [ae_all_iff]
  intro n
  exact reward_ae_eq_eval_action h n

open Finset in
lemma reward_ae_eq_evals_actions_comp {β : Type*} (h : IsAlgEnvSeq A R' alg (evalEnv hf) P) {n : ℕ}
    (g : (Iic n → R) → β) : ∀ᵐ ω ∂P, g (fun i ↦ R' i ω) = g (fun i ↦ f (A i ω)) := by
  filter_upwards [reward_ae_eq_evals_actions h] with ω hω
  simp_rw [hω]

end EvalEnv

end Learning
