import Mathlib.Probability.Kernel.Composition.ParallelComp

open MeasureTheory
open scoped ENNReal

namespace ProbabilityTheory.Kernel

variable {α β γ δ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mγ : MeasurableSpace γ} {mδ : MeasurableSpace δ}
  {κ : Kernel α β} {η : Kernel γ δ} {x : α × γ}

-- PR: https://github.com/leanprover-community/mathlib4/pull/29555
lemma parallelComp_apply_prod [IsSFiniteKernel κ] [IsSFiniteKernel η] (s : Set β) (t : Set δ) :
    (κ ∥ₖ η) x (s ×ˢ t) = (κ x.1 s) * (η x.2 t) := by
  rw [parallelComp_apply, Measure.prod_prod]

-- PR: https://github.com/leanprover-community/mathlib4/pull/29555
lemma deterministic_parallelComp_deterministic
    {f : α → γ} {g : β → δ} (hf : Measurable f) (hg : Measurable g) :
    (deterministic f hf) ∥ₖ (deterministic g hg)
      = deterministic (Prod.map f g) (hf.prodMap hg) := by
  ext x : 1
  rw [parallelComp_apply, deterministic_apply, deterministic_apply, deterministic_apply, Prod.map,
    Measure.dirac_prod_dirac]

end ProbabilityTheory.Kernel
