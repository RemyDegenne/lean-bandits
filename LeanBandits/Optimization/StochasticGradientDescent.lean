/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.SequentialLearning.Deterministic
import LeanBandits.SequentialLearning.StationaryEnv
import Mathlib

/-!
# Stochastic Gradient Descent
-/

open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped Gradient ENNReal NNReal

namespace Learning

/- The stochastic gradient environment is simply a stationary environment, with kernel having the
property that its mean at `x` is the gradient of the function `f` at `x`. -/

variable {E : Type} {mE : MeasurableSpace E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [MeasurableSub₂ E] [SecondCountableTopology E]
  {f : E → ℝ} {x x₀ x_star : E}
  {κ : Kernel E E} [IsMarkovKernel κ]
  {hκf : ∀ x, (κ x)[id] = ∇ f x}
  {hκ_var : ∀ x, ∫⁻ y, ‖y - (κ x)[id]‖ₑ ^ 2 ∂(κ x) ≠ ∞}

variable (E) in
noncomputable
def sgd (γ : ℕ → ℝ) (x₀ : E) : Algorithm E E :=
  detAlgorithm (fun n hist ↦ (hist ⟨n, by grind⟩).1 - γ n • (hist ⟨n, by grind⟩).2) (by fun_prop) x₀

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → E} {G : ℕ → Ω → E}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {γ : ℕ → ℝ}
  {h_seq : IsAlgEnvSeq X G (sgd E γ x₀) (stationaryEnv κ) P}
  {L : ℝ≥0} {hf_smooth : LipschitzWith L (∇ f)}
  {hf_convex : ConvexOn ℝ Set.univ f}
  {hf_min : IsMinOn f Set.univ x_star}
  {hγ_pos : ∀ n, 0 < γ n} {hγ_le : ∀ n, γ n ≤ 1 / (4 * L)}

noncomputable
def avgIterate (X : ℕ → Ω → E) (γ : ℕ → ℝ) (n : ℕ) (ω : Ω) : E :=
  (∑ n ∈ range n, γ n)⁻¹ • (∑ n ∈ range n, γ n • X n ω)

noncomputable
def gradientNoise (f : E → ℝ) (κ : Kernel E E) : ℝ :=
  ⨅ (x : E) (_ : IsMinOn f Set.univ x), (κ x)[fun y ↦ ‖y - (κ x)[id]‖ ^ 2]

lemma todo (hκf : ∀ x, (κ x)[id] = ∇ f x) (hκ_var : ∀ x, ∫⁻ y, ‖y - (κ x)[id]‖ₑ ^ 2 ∂(κ x) ≠ ∞)
    (x : E) :
    (κ x)[fun y ↦ ‖y‖ ^ 2] ≤ 4 * L * (f x - f x_star) + 2 * gradientNoise f κ := by
  sorry



theorem integral_error_sgd_le (n : ℕ) :
    P[fun ω ↦ f (avgIterate X γ n ω) - f x_star] ≤
      (∑ k ∈ range n, γ k)⁻¹ •
      (‖x₀ - x_star‖ ^ 2 + 2 * gradientNoise f κ * (∑ k ∈ range n, (γ k) ^ 2)) := by
  sorry

end Learning
