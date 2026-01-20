/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.MeasurableArgMax
import LeanBandits.SequentialLearning.Algorithm

open MeasureTheory ProbabilityTheory Finset
open Learning

section Algorithm -- SequentialLearning/Algorithm.lean

variable {α R : Type*} [mα : MeasurableSpace α] [mR : MeasurableSpace R]

namespace Learning

def Algorithm.prod_left (E : Type*) [MeasurableSpace E] (alg : Algorithm α R) :
    Algorithm α (E × R) where
  policy n := (alg.policy n).comap (fun h i ↦ ((h i).1, (h i).2.2)) (by fun_prop)
  p0 := alg.p0

variable {Ω E : Type*} [mΩ : MeasurableSpace Ω] [mE : MeasurableSpace E]

def IsPOAlgEnvSeq
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R]
    [StandardBorelSpace E] [Nonempty E]
    (A : ℕ → Ω → α) (R' : ℕ → Ω → R) (E' : ℕ → Ω → E)
    (alg : Algorithm α R) (env : Environment α (E × R)) (P : Measure Ω) [IsFiniteMeasure P]
    := IsAlgEnvSeq A (fun n ω ↦ (E' n ω, R' n ω)) (alg.prod_left E) env P

end Learning

end Algorithm

section StationaryEnv -- SequentialLearning/StationaryEnv.lean

variable {α R E : Type*} [mα : MeasurableSpace α] [mR : MeasurableSpace R] [mE : MeasurableSpace E]

noncomputable
def BayesStationaryEnv (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R)
    [IsMarkovKernel κ] : Environment α (E × R) where
  feedback n :=
    let g : (Iic n → α × (E × R)) × α → (α × E) := fun (h, a) => (a, (h ⟨0, by simp⟩).2.1)
    (Kernel.deterministic (Prod.snd ∘ g) (by fun_prop)) ×ₖ (κ.comap g (by fun_prop))
  h_feedback := inferInstance
  ν0 := (Kernel.const α Q) ⊗ₖ κ
  hp0 := Kernel.IsMarkovKernel.compProd _ _

end StationaryEnv

section ThompsonSampling -- BanditAlgorithms/TS.lean

variable {K : ℕ}
variable {E : Type*} [mE : MeasurableSpace E] [StandardBorelSpace E] [Nonempty E]
variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

variable (hK : 0 < K)
variable (Q : Measure E) [IsProbabilityMeasure Q]
variable (κ : Kernel (E × Fin K) ℝ) [IsMarkovKernel κ]
variable (A : ℕ → Ω → Fin K) (R' : ℕ → Ω → ℝ) (E' : ℕ → Ω → E)
variable (P : Measure Ω) [IsFiniteMeasure P]

noncomputable
def tsPosterior (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) E :=
  condDistrib (E' 0) (IsAlgEnvSeq.hist A R' n) P

noncomputable
def isMarkovKernel_tsPosterior (n : ℕ) : IsMarkovKernel (tsPosterior A R' E' P n) := by
  unfold tsPosterior
  infer_instance

noncomputable
def tsPolicy (n : ℕ) : Kernel (Iic n → (Fin K) × ℝ) (Fin K) :=
  have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
  (tsPosterior A R' E' P n).map (measurableArgmax (fun e k ↦ (κ (e, k))[id]))

def isMarkovKernel_tsPolicy (n : ℕ) : IsMarkovKernel (tsPolicy hK κ A R' E' P n) := by
  have : IsMarkovKernel (tsPosterior A R' E' P n) := isMarkovKernel_tsPosterior A R' E' P n
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
  policy := tsPolicy hK κ A R' E' P
  h_policy := isMarkovKernel_tsPolicy hK κ A R' E' P
  p0 := tsInitPolicy hK Q κ
  hp0 := isProbabilityMeasure_tsInitPolicy hK Q κ

end ThompsonSampling

-- section Uniform

-- variable {K : ℕ} (hK : 0 < K)

-- noncomputable
-- def uniformAlgorithm : Algorithm (Fin K) ℝ :=
--   have : Nonempty (Fin K) := Fin.pos_iff_nonempty.mp hK
--   { policy _ := Kernel.const _ (PMF.uniformOfFintype (Fin K)).toMeasure
--     p0 := (PMF.uniformOfFintype (Fin K)).toMeasure }

-- end Uniform
