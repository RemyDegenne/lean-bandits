/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.BanditAlgorithms.Uniform
import LeanBandits.SequentialLearning.BayesStationaryEnv
import LeanBandits.ForMathlib.SubGaussian

open MeasureTheory ProbabilityTheory Finset Learning

namespace Bandits

variable {K : ℕ}
variable {E : Type*} [mE : MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]

variable (hK : 0 < K)
variable (Q : Measure E) [IsProbabilityMeasure Q]
variable (κ : Kernel (Fin K × E) ℝ) [IsMarkovKernel κ]

namespace TS

/-- The distribution over actions for every given history for TS. -/
noncomputable
def tsPolicy (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  IT.posteriorBestArm Q κ (uniformAlgorithm hK) n

instance (n : ℕ) : IsMarkovKernel (tsPolicy hK Q κ n) := by
  unfold tsPolicy
  infer_instance

/-- The initial distribution over actions for TS. -/
noncomputable
def tsInitPolicy : Measure (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  IT.priorBestArm Q κ (uniformAlgorithm hK)

instance : IsProbabilityMeasure (tsInitPolicy hK Q κ) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  unfold tsInitPolicy
  infer_instance

/-- The Thompson Sampling (TS) algorithm: actions are chosen according to the probability that they
are optimal given prior knowledge represented by a prior distribution `Q` and a data generation
model represented by a kernel `κ`. -/
noncomputable
def tsAlgorithm : Algorithm (Fin K) ℝ where
  policy := tsPolicy hK Q κ
  p0 := tsInitPolicy hK Q κ


variable {Ω : Type*} [MeasurableSpace Ω]
variable {A : ℕ → Ω → (Fin K)} {R' : ℕ → Ω → E × ℝ}
variable {P : Measure Ω} [IsFiniteMeasure P]

def bayesian_regret_le [Nonempty (Fin K)]
    (h : IsBayesAlgEnvSeq Q κ A R' (tsAlgorithm hK Q κ) P)
    (hs : ∀ a e, HasSubgaussianMGF (fun x ↦ x - (κ (a, e))[id]) 1 (κ (a, e)))
    (hm : ∀ a e, (κ (a, e))[id] ∈ (Set.Icc 0 1)) :
    ∃ C > 0, ∀ n : ℕ,
      (IsBayesAlgEnvSeq.bayesRegret κ A R' P n) ≤ C * √(K * n * Real.log n) :=
  sorry

end TS

end Bandits
