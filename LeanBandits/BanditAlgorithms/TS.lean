/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import Mathlib.Probability.Distributions.Uniform
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.SequentialLearning.Algorithm

open MeasureTheory ProbabilityTheory Finset
open Learning

section StationaryBayesAlgEnvSeq

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

end StationaryBayesAlgEnvSeq

section Uniform

variable {K : ℕ} (hK : 0 < K)

noncomputable
def uniformAlgorithm : Algorithm (Fin K) ℝ :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  { policy _ := Kernel.const _ (PMF.uniformOfFintype (Fin K)).toMeasure
    p0 := (PMF.uniformOfFintype (Fin K)).toMeasure }

end Uniform

section ThompsonSampling

variable {K : ℕ} (hK : 0 < K)

variable {ℰ : Type*} [mℰ : MeasurableSpace ℰ] [StandardBorelSpace ℰ] [Nonempty ℰ]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

variable (Q : Measure ℰ) [IsProbabilityMeasure Q] (κ : Kernel (ℰ × (Fin K)) ℝ) [IsMarkovKernel κ]
variable (E : Ω → ℰ) (A : ℕ → Ω → (Fin K)) (R' : ℕ → Ω → ℝ)
variable (P : Measure Ω) [IsFiniteMeasure P]

noncomputable
def tsPosterior (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) ℰ :=
  condDistrib E (IsAlgEnvSeq.hist A R' n) P

noncomputable
def isMarkovKernel_tsPosterior (n : ℕ) : IsMarkovKernel (tsPosterior E A R' P n) := by
  unfold tsPosterior
  infer_instance

noncomputable
def tsPolicy (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  (tsPosterior E A R' P n).map (measurableArgmax (fun e k ↦ (κ (e, k))[id]))

def isMarkovKernel_tsPolicy (n : ℕ) : IsMarkovKernel (tsPolicy hK κ E A R' P n) := by
  have : IsMarkovKernel (tsPosterior E A R' P n) := isMarkovKernel_tsPosterior E A R' P n
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  apply Kernel.IsMarkovKernel.map
  exact measurable_measurableArgmax fun k =>
    (stronglyMeasurable_id.integral_kernel (κ := κ.comap (·, k) (by fun_prop))).measurable

noncomputable
def tsInitPolicy : Measure (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  Q.map (measurableArgmax (fun e k ↦ (κ (e, k))[id]))

def isProbabilityMeasure_tsInitPolicy : IsProbabilityMeasure (tsInitPolicy hK Q κ) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  apply Measure.isProbabilityMeasure_map
  apply Measurable.aemeasurable
  exact (measurable_measurableArgmax fun k =>
    (stronglyMeasurable_id.integral_kernel (κ := κ.comap (·, k) (by fun_prop))).measurable)

noncomputable
def tsAlgorithm : Algorithm (Fin K) ℝ where
  policy := tsPolicy hK κ E A R' P
  h_policy := isMarkovKernel_tsPolicy hK κ E A R' P
  p0 := tsInitPolicy hK Q κ
  hp0 := isProbabilityMeasure_tsInitPolicy hK Q κ

end ThompsonSampling
