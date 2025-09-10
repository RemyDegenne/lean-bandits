/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Moments.SubGaussian
import LeanBandits.AlgorithmBuilding

/-! # The Explore-Then-Commit Algorithm

-/

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

namespace Bandits

variable {K : ℕ}

/-- Arm pulled by the ETC algorithm at time `n + 1`. -/
noncomputable
def etcNextArm (hK : 0 < K) (m n : ℕ) (h : Iic n → Fin K × ℝ) : Fin K :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  if hn : n < K * m - 1 then
    ⟨(n + 1) % K, Nat.mod_lt _ hK⟩ -- for `n = 0` we have pulled arm 0 already, and we pull arm 1
  else
    if hn_eq : n = K * m - 1 then measurableArgmax (empMean' n) h
    else (h ⟨n - 1, by simp⟩).1

@[fun_prop]
lemma measurable_etcNextArm (hK : 0 < K) (m n : ℕ) : Measurable (etcNextArm hK m n) := by
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  unfold etcNextArm
  simp only [dite_eq_ite]
  refine Measurable.ite (by simp) (by fun_prop) ?_
  refine Measurable.ite (by simp) ?_ (by fun_prop)
  exact measurable_measurableArgmax fun a ↦ by fun_prop

/-- The Explore-Then-Commit algorithm. -/
noncomputable
def etcAlgorithm (hK : 0 < K) (m : ℕ) : Algorithm (Fin K) ℝ where
  policy n := Kernel.deterministic (etcNextArm hK m n) (by fun_prop)
  p0 := Measure.dirac ⟨0, hK⟩

lemma ETC.arm_zero (hK : 0 < K) (m : ℕ) (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν] :
    arm 0 =ᵐ[Bandit.trajMeasure (etcAlgorithm hK m) ν] fun _ ↦ ⟨0, hK⟩ := by
  have h_eq : ∀ᵐ x ∂((Bandit.trajMeasure (etcAlgorithm hK m) ν).map (arm 0)), x = ⟨0, hK⟩ := by
    have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
    rw [(hasLaw_arm_zero _ _).map_eq]
    simp [etcAlgorithm]
  exact ae_of_ae_map (by fun_prop) h_eq

lemma ETC.arm_ae_eq_etcNextArm (hK : 0 < K) (m : ℕ) (ν : Kernel (Fin K) ℝ) [IsMarkovKernel ν]
    (n : ℕ) :
    arm (n + 1) =ᵐ[(Bandit.trajMeasure (etcAlgorithm hK m) ν)]
      fun h ↦ etcNextArm hK m n (fun i ↦ h i) := by
  sorry

end Bandits
