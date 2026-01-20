/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
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

noncomputable
def tsPosterior (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) E :=
  Learning.Bayes.posterior Q κ (uniformAlgorithm hK) n

noncomputable
def isMarkovKernel_tsPosterior (n : ℕ) : IsMarkovKernel (tsPosterior hK Q κ n) := by
  unfold tsPosterior Bayes.posterior
  infer_instance

noncomputable
def tsPolicy (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  (tsPosterior hK Q κ n).map (measurableArgmax (fun e k ↦ (κ (k, e))[id]))

def isMarkovKernel_tsPolicy (n : ℕ) : IsMarkovKernel (tsPolicy hK Q κ n) := by
  have : IsMarkovKernel (tsPosterior hK Q κ n) := isMarkovKernel_tsPosterior hK Q κ n
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  apply Kernel.IsMarkovKernel.map
  exact measurable_measurableArgmax fun k =>
    (stronglyMeasurable_id.integral_kernel (κ := κ.comap (k, ·) (by fun_prop))).measurable

noncomputable
def tsInitPolicy : Measure (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  Q.map (measurableArgmax (fun e k ↦ (κ (k, e))[id]))

def isProbabilityMeasure_tsInitPolicy : IsProbabilityMeasure (tsInitPolicy hK Q κ) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  exact (measurable_measurableArgmax fun k =>
    (stronglyMeasurable_id.integral_kernel (κ := κ.comap (k, ·) (by fun_prop))).measurable)

noncomputable
def tsAlgorithm : Algorithm (Fin K) ℝ where
  policy := tsPolicy hK Q κ
  h_policy := isMarkovKernel_tsPolicy hK Q κ
  p0 := tsInitPolicy hK Q κ
  hp0 := isProbabilityMeasure_tsInitPolicy hK Q κ

end Bandits
