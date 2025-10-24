/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.SequentialLearning.Algorithm

/-!
# Deterministic algorithms
-/

open MeasureTheory ProbabilityTheory Filter Real Finset

open scoped ENNReal NNReal

namespace Learning

variable {α R : Type*} {mα : MeasurableSpace α} {mR : MeasurableSpace R}

/-- A deterministic algorithm. -/
@[simps]
noncomputable
def detAlgorithm (nextaction : (n : ℕ) → (Iic n → α × R) → α)
    (h_next : ∀ n, Measurable (nextaction n)) (action0 : α) :
    Algorithm α R where
  policy n := Kernel.deterministic (nextaction n) (h_next n)
  p0 := Measure.dirac action0

variable {nextaction : (n : ℕ) → (Iic n → α × R) → α} {h_next : ∀ n, Measurable (nextaction n)}
  {action0 : α} {env : Environment α R}

local notation "𝔓" => trajMeasure (detAlgorithm nextaction h_next action0) env

lemma HasLaw_action_zero_detAlgorithm : HasLaw (action 0) (Measure.dirac action0) 𝔓 where
  map_eq := (hasLaw_action_zero _ _).map_eq

lemma action_zero_detAlgorithm [MeasurableSingletonClass α] : action 0 =ᵐ[𝔓] fun _ ↦ action0 := by
  have h_eq : ∀ᵐ x ∂((𝔓).map (action 0)), x = action0 := by
    rw [(hasLaw_action_zero _ _).map_eq]
    simp [detAlgorithm]
  exact ae_of_ae_map (by fun_prop) h_eq

lemma action_detAlgorithm_ae_eq
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (n : ℕ) :
    action (n + 1) =ᵐ[𝔓] fun h ↦ nextaction n (fun i ↦ h i) := by
  have h := condDistrib_action (detAlgorithm nextaction h_next action0) env n
  simp only [detAlgorithm_policy] at h
  sorry

example [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R] :
    ∀ᵐ h ∂𝔓, action 0 h = action0 ∧ ∀ n, action (n + 1) h = nextaction n (fun i ↦ h i) := by
  rw [eventually_and, ae_all_iff]
  exact ⟨action_zero_detAlgorithm, action_detAlgorithm_ae_eq⟩

end Learning
