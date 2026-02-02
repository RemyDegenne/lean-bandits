/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.SubGaussian
import LeanBandits.BanditAlgorithms.Uniform
import LeanBandits.SequentialLearning.BayesStationaryEnv

/-! # The Thompson Sampling Algorithm -/

open MeasureTheory ProbabilityTheory Finset Learning

namespace Bandits

namespace TS

variable {K : ℕ} (hK : 0 < K)
variable {E : Type*} [mE : MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
variable (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (Fin K × E) ℝ) [IsMarkovKernel κ]

/-- The distribution over actions for every given history for TS. -/
noncomputable
def policy (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  IT.posteriorBestArm Q κ (uniformAlgorithm hK) n
deriving IsMarkovKernel

/-- The initial distribution over actions for TS. -/
noncomputable
def initialPolicy : Measure (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  IT.priorBestArm Q κ (uniformAlgorithm hK)

instance : IsProbabilityMeasure (initialPolicy hK Q κ) := by
  unfold initialPolicy
  infer_instance

end TS

variable {K : ℕ}
variable {E : Type*} [mE : MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]

/-- The Thompson Sampling (TS) algorithm: actions are chosen according to the probability that they
are optimal given prior knowledge represented by a prior distribution `Q` and a data generation
model represented by a kernel `κ`. -/
noncomputable
def tsAlgorithm (hK : 0 < K) (Q : Measure E) [IsProbabilityMeasure Q]
    (κ : Kernel (Fin K × E) ℝ) [IsMarkovKernel κ] : Algorithm (Fin K) ℝ where
  policy := TS.policy hK Q κ
  p0 := TS.initialPolicy hK Q κ

section Regret

variable (hK : 0 < K)
variable {Ω : Type*} [MeasurableSpace Ω]
variable (A : ℕ → Ω → (Fin K)) (R' : ℕ → Ω → E × ℝ)
variable (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (Fin K × E) ℝ) [IsMarkovKernel κ]
variable (P : Measure Ω) [IsFiniteMeasure P]

lemma TS.bayesRegret_le [Nonempty (Fin K)]
    (h : IsBayesAlgEnvSeq Q κ A R' (tsAlgorithm hK Q κ) P)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (a, e))[id]) 1 (κ (a, e)))
    (hm : ∀ a e, (κ (a, e))[id] ∈ (Set.Icc 0 1)) (t : ℕ) :
    IsBayesAlgEnvSeq.bayesRegret κ A R' P t ≤ 4 * K + 8 * √(K * t * Real.log t) :=
  sorry

end Regret

end Bandits
