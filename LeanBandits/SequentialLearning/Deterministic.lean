/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.SequentialLearning.IonescuTulceaSpace

/-!
# Deterministic algorithms
-/

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {α R : Type*} {mα : MeasurableSpace α} {mR : MeasurableSpace R}

/-- A deterministic algorithm, which chooses the action given by the function `nextAction`. -/
@[simps]
noncomputable
def detAlgorithm (nextAction : (n : ℕ) → (Iic n → α × R) → α)
    (h_next : ∀ n, Measurable (nextAction n)) (action0 : α) :
    Algorithm α R where
  policy n := Kernel.deterministic (nextAction n) (h_next n)
  p0 := Measure.dirac action0

variable {nextAction : (n : ℕ) → (Iic n → α × R) → α} {h_next : ∀ n, Measurable (nextAction n)}
  {action0 : α} {env : Environment α R}

namespace IsAlgEnvSeq

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}
  [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
  {alg : Algorithm α R} {ν : Kernel α R} [IsMarkovKernel ν]
  {P : Measure Ω} [IsProbabilityMeasure P] {A : ℕ → Ω → α} {R' : ℕ → Ω → R}

lemma HasLaw_action_zero_detAlgorithm
    (h : IsAlgEnvSeq A R' (detAlgorithm nextAction h_next action0) env P) :
    HasLaw (A 0) (Measure.dirac action0) P where
  aemeasurable := have hA := h.measurable_A; by fun_prop
  map_eq := (hasLaw_action_zero h).map_eq

lemma action_zero_detAlgorithm
    (h : IsAlgEnvSeq A R' (detAlgorithm nextAction h_next action0) env P) :
    A 0 =ᵐ[P] fun _ ↦ action0 := by
  have h_eq : ∀ᵐ x ∂(P.map (A 0)), x = action0 := by
    rw [(hasLaw_action_zero h).map_eq]
    simp [detAlgorithm]
  have hA := h.measurable_A
  exact ae_of_ae_map (by fun_prop) h_eq

lemma action_detAlgorithm_ae_eq
    (h : IsAlgEnvSeq A R' (detAlgorithm nextAction h_next action0) env P) (n : ℕ) :
    A (n + 1) =ᵐ[P] fun ω ↦ nextAction n (hist A R' n ω) := by
  have hA := h.measurable_A
  have hR' := h.measurable_R
  exact ae_eq_of_condDistrib_eq_deterministic (by fun_prop) (by fun_prop) (by fun_prop)
    (h.hasCondDistrib_action n).condDistrib_eq

lemma action_detAlgorithm_ae_all_eq
    (h : IsAlgEnvSeq A R' (detAlgorithm nextAction h_next action0) env P) :
    ∀ᵐ ω ∂P, A 0 ω = action0 ∧ ∀ n, A (n + 1) ω = nextAction n (hist A R' n ω) := by
  rw [eventually_and, ae_all_iff]
  exact ⟨action_zero_detAlgorithm h, action_detAlgorithm_ae_eq h⟩

end IsAlgEnvSeq

namespace IT

local notation "𝔓" => trajMeasure (detAlgorithm nextAction h_next action0) env

lemma HasLaw_action_zero_detAlgorithm : HasLaw (IT.action 0) (Measure.dirac action0) 𝔓 where
  map_eq := (IT.hasLaw_action_zero _ _).map_eq

lemma action_zero_detAlgorithm [MeasurableSingletonClass α] :
    IT.action 0 =ᵐ[𝔓] fun _ ↦ action0 := by
  have h_eq : ∀ᵐ x ∂((𝔓).map (IT.action 0)), x = action0 := by
    rw [(IT.hasLaw_action_zero _ _).map_eq]
    simp [detAlgorithm]
  exact ae_of_ae_map (by fun_prop) h_eq

lemma action_detAlgorithm_ae_eq [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R]
    [Nonempty R] (n : ℕ) : IT.action (n + 1) =ᵐ[𝔓] fun h ↦ nextAction n (IT.hist n h) :=
  ae_eq_of_condDistrib_eq_deterministic (by fun_prop) (by fun_prop) (by fun_prop)
    (IT.condDistrib_action (detAlgorithm nextAction h_next action0) env n)

lemma action_detAlgorithm_ae_all_eq
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R] :
    ∀ᵐ h ∂𝔓, IT.action 0 h = action0 ∧ ∀ n, IT.action (n + 1) h = nextAction n (IT.hist n h) := by
  rw [eventually_and, ae_all_iff]
  exact ⟨action_zero_detAlgorithm, action_detAlgorithm_ae_eq⟩

end IT

end Learning
