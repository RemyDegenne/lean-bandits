/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.SequentialLearning.Deterministic
import LeanBandits.SequentialLearning.StationaryEnv
import Mathlib

/-!
# Online Convex Optimization
-/

open MeasureTheory ProbabilityTheory Filter Real Finset
open scoped Gradient ENNReal NNReal

namespace Learning

variable {E : Type} {mE : MeasurableSpace E}
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E] [BorelSpace E]
  [MeasurableSub₂ E] [SecondCountableTopology E]
  {f : ℕ → E → ℝ} {hf : ∀ n, Measurable (∇ (f n))} {x x₀ : E}
  {s : Set E} (hs_cvx : Convex ℝ s) (hs_closed : IsClosed s) (hs_nonempty : s.Nonempty)

noncomputable
def ocoEnv (hf : ∀ n, Measurable (∇ (f n))) : Environment E E where
  feedback n := Kernel.prodMkLeft _ (Kernel.deterministic (∇ (f (n + 1))) (hf (n + 1)))
  ν0 := Kernel.deterministic (fun x ↦ ∇ (f 0) x) (hf 0)

variable (E) in
/-- Online gradient descent, without projection. -/
noncomputable
def ogd (γ : ℕ → ℝ) (x₀ : E) : Algorithm E E :=
  detAlgorithm (fun n hist ↦ (hist ⟨n, by grind⟩).1 - γ n • (hist ⟨n, by grind⟩).2) (by fun_prop) x₀

-- TODO: we need the projection on `s`, and we need it to be measurable.
-- this is a measurable argmin. From measurable selection? Or from a more direct construction,
-- using the fact that `s` is a countable intersection of half-spaces?

variable (E) in
/-- Projected online gradient descent. -/
noncomputable
def pogd (γ : ℕ → ℝ) (x₀ : E) : Algorithm E E :=
  detAlgorithm (fun n hist ↦ sorry) sorry x₀

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {X : ℕ → Ω → E} {G : ℕ → Ω → E}
  {P : Measure Ω} [IsProbabilityMeasure P]
  {γ : ℕ → ℝ}
  {h_seq : IsAlgEnvSeq X G (ogd E γ x₀) (ocoEnv hf) P}
  {L : ℝ≥0} {hf_smooth : ∀ n, LipschitzWith L (∇ (f n))}
  {hf_convex : ∀ n, ConvexOn ℝ Set.univ (f n)}
  {hγ_pos : ∀ n, 0 < γ n} {hγ_le : ∀ n, γ n ≤ 1 / (4 * L)}



end Learning
