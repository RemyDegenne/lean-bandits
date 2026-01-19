/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.SequentialLearning.Algorithm

open MeasureTheory ProbabilityTheory Finset
open Learning

variable {α R : Type*} [mα : MeasurableSpace α] [mR : MeasurableSpace R]
variable {ℰ : Type*} [mℰ : MeasurableSpace ℰ]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

structure isStationaryBayesAlgEnvSeq
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    (alg : Algorithm α R)
    (Q : Measure ℰ) [IsProbabilityMeasure Q] (κ : Kernel (ℰ × α) R) [IsMarkovKernel κ]
    (E : Ω → ℰ) (A : ℕ → Ω → α) (R' : ℕ → Ω → R)
    (P : Measure Ω) [IsFiniteMeasure P] : Prop where
  measurable_E : Measurable E := by fun_prop
  measurable_A n : Measurable (A n) := by fun_prop
  measurable_R n : Measurable (R' n) := by fun_prop
  hasLaw_env : HasLaw E Q P
  hasLaw_action_zero : HasLaw (fun ω ↦ (A 0 ω)) alg.p0 P
  hasCondDistrib_reward_zero : HasCondDistrib (R' 0) (fun ω ↦ (E ω, A 0 ω)) κ P
  hasCondDistrib_action n :
    HasCondDistrib (A (n + 1)) (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, E ω))
      ((alg.policy n).prodMkRight _) P
  hasCondDistrib_reward n :
    HasCondDistrib (R' (n + 1)) (fun ω ↦ (IsAlgEnvSeq.hist A R' n ω, E ω, A (n + 1) ω))
      (κ.prodMkLeft _) P



-- structure Algorithm (α R : Type*) [MeasurableSpace α] [MeasurableSpace R] where
--   /-- Policy or sampling rule: distribution of the next action. -/
--   policy : (n : ℕ) → Kernel (Iic n → α × R) α
--   [h_policy : ∀ n, IsMarkovKernel (policy n)]
--   /-- Distribution of the first action. -/
--   p0 : Measure α
--   [hp0 : IsProbabilityMeasure p0]


-- noncomputable
-- def tsAlgorithm : Algorithm (Fin K) ℝ where
--   policy := tsPolicy hK μ ℓ
--   h_policy := isMarkovKernel_tsPolicy hK μ ℓ
--   p0 := tsInitialPolicy hK μ ℓ
--   hp0 := isProbabilityMeasure_tsInitialPolicy hK μ ℓ
