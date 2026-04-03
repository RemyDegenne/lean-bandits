/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanBandits.SequentialLearning.StationaryEnv
import LeanBandits.ForMathlib.CondDistrib

/-!
# Function evaluation environments
-/

open MeasureTheory ProbabilityTheory

namespace Learning

variable {α R : Type*} [MeasurableSpace α] [MeasurableSpace R]

noncomputable def evalEnv {f : α → R} (hf : Measurable f) :=
  stationaryEnv <| Kernel.deterministic f hf

namespace IsAlgEnvSeq

variable [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {Ω : Type*} {mΩ : MeasurableSpace Ω} {alg : Algorithm α R} {f : α → R} (hf : Measurable f)
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → α} {R' : ℕ → Ω → R}

lemma hascondDistrib_reward_evalEnv (h : IsAlgEnvSeq A R' alg (evalEnv hf) P) (n : ℕ) :
    HasCondDistrib (R' n) (A n) (Kernel.deterministic f hf) P :=
  have hRn := h.measurable_R n
  have hAn := h.measurable_A n
  ⟨hRn.aemeasurable, hAn.aemeasurable, h.condDistrib_reward_stationaryEnv n⟩

lemma reward_eq_eval_action (h : IsAlgEnvSeq A R' alg (evalEnv hf) P) (n : ℕ) :
    R' n =ᵐ[P] f ∘ A n :=
  ae_eq_of_condDistrib_eq_deterministic hf (h.measurable_A n).aemeasurable
    (h.measurable_R n).aemeasurable (hascondDistrib_reward_evalEnv hf h n).condDistrib_eq

lemma reward_eq_evals_actions (h : IsAlgEnvSeq A R' alg (evalEnv hf) P) :
    ∀ᵐ ω ∂P, ∀ n, R' n ω = f (A n ω) := by
  rw [ae_all_iff]
  intro n
  exact reward_eq_eval_action hf h n

open Finset in
lemma reward_eq_evals_actions_comp (h : IsAlgEnvSeq A R' alg (evalEnv hf) P) {n : ℕ}
    (g : (Iic n → R) → R) : ∀ᵐ ω ∂P, g (fun i ↦ R' i ω) = g (fun i ↦ f (A i ω)) := by
  filter_upwards [reward_eq_evals_actions hf h] with ω hω
  simp_rw [hω]

lemma neg [Neg R] [MeasurableNeg R] (h : IsAlgEnvSeq A R' alg (evalEnv hf) P) :
    IsAlgEnvSeq A (-R') alg (evalEnv <| Measurable.neg hf) P where
  measurable_A n := h.measurable_A n
  measurable_R n := Measurable.neg <| h.measurable_R n
  hasLaw_action_zero := h.hasLaw_action_zero
  hasCondDistrib_reward_zero := by
    have hA := h.measurable_A 0
    have hR := h.measurable_R 0
    refine ⟨(Measurable.neg <| h.measurable_R 0).aemeasurable, by fun_prop, ?_⟩
    have : (- R') 0 =ᶠ[ae P] (-f) ∘ A 0 := by
      have := reward_eq_eval_action hf h 0
      filter_upwards [this] with ω hω
      simp [hω]
    rw [condDistrib_congr this (ae_eq_rfl)]
    filter_upwards [condDistrib_comp_self (f := (-f)) (A 0) (Measurable.neg hf)] with ω hω
    simpa using hω
  hasCondDistrib_action := by sorry
  hasCondDistrib_reward := by sorry

end IsAlgEnvSeq

end Learning
