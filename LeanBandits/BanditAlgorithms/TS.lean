/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.BanditAlgorithms.Uniform
import LeanBandits.SequentialLearning.BayesStationaryEnv

open MeasureTheory ProbabilityTheory Finset Learning

namespace Bandits

variable {K : ℕ}
variable {E : Type*} [mE : MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]

variable (hK : 0 < K)
variable (Q : Measure E) [IsProbabilityMeasure Q]
variable (κ : Kernel (Fin K × E) ℝ) [IsMarkovKernel κ]

/-- The distribution over actions for every given history for TS. -/
noncomputable
def tsPolicy (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  IsBayesianAlgEnvSeq.condDistribBestAction (IT.bayesianTrajMeasure Q κ (uniformAlgorithm hK)) κ
    IT.action IT.reward n

instance (n : ℕ) : IsMarkovKernel (tsPolicy hK Q κ n) := by
  unfold tsPolicy
  infer_instance

/-- The initial distribution over actions for TS. -/
noncomputable
def tsInitPolicy : Measure (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  Q.map (measurableArgmax (fun e k ↦ (κ (k, e))[id]))

instance : IsProbabilityMeasure (tsInitPolicy hK Q κ) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  exact (measurable_measurableArgmax fun k =>
    (stronglyMeasurable_id.integral_kernel (κ := κ.comap (k, ·) (by fun_prop))).measurable)

/-- The Thompson Sampling (TS) algorithm: actions are chosen according to the probability that they
are optimal given prior knowledge represented by a prior distribution `Q` and a data generation
model represented by a kernel `κ`. -/
noncomputable
def tsAlgorithm : Algorithm (Fin K) ℝ where
  policy := tsPolicy hK Q κ
  p0 := tsInitPolicy hK Q κ

end Bandits
