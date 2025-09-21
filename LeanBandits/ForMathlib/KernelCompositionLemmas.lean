import Mathlib.Probability.Kernel.Composition.Lemmas
import LeanBandits.ForMathlib.KernelCompositionParallelComp

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
  {μ : Measure α} {ν : Measure β} {κ : Kernel α β}

-- PR: https://github.com/leanprover-community/mathlib4/pull/29555
lemma MeasureTheory.Measure.compProd_map [SFinite μ] [IsSFiniteKernel κ]
    {f : β → γ} (hf : Measurable f) :
    μ ⊗ₘ (κ.map f) = (μ ⊗ₘ κ).map (Prod.map id f) := by
  calc μ ⊗ₘ (κ.map f)
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (Kernel.id ×ₖ κ) ∘ₘ μ := by
    rw [comp_assoc, Kernel.parallelComp_comp_prod, compProd_eq_comp_prod,
      Kernel.id_comp, Kernel.deterministic_comp_eq_map]
  _ = (Kernel.id ∥ₖ Kernel.deterministic f hf) ∘ₘ (μ ⊗ₘ κ) := by rw [compProd_eq_comp_prod]
  _ = (μ ⊗ₘ κ).map (Prod.map id f) := by
    rw [Kernel.id, Kernel.deterministic_parallelComp_deterministic, deterministic_comp_eq_map]
