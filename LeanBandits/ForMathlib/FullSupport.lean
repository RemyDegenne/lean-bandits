/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import Mathlib.Probability.Kernel.RadonNikodym
import Mathlib.Probability.Kernel.Composition.MeasureCompProd

/-!
# Absolute continuity and rnDeriv finiteness from full support

When a reference measure gives positive mass to every singleton, any measure is absolutely
continuous with respect to it, and the Radon-Nikodym derivative is pointwise finite.
-/

open MeasureTheory ProbabilityTheory

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν : Measure α}

namespace Measure

/-- Any measure is absolutely continuous wrt any measure giving positive mass to all singletons. -/
lemma absolutelyContinuous_of_forall_singleton_pos (hν : ∀ a : α, ν {a} > 0) : μ ≪ ν := by
  intro s hs
  rcases s.eq_empty_or_nonempty with rfl | ⟨a, ha⟩
  · exact measure_empty
  · exact absurd (measure_mono_null (Set.singleton_subset_iff.mpr ha) hs) (hν a).ne'

/-- An ae property holds everywhere when the reference measure gives positive mass
    to every singleton. -/
lemma forall_of_ae_of_forall_singleton_pos (hν : ∀ a, ν {a} > 0) {p : α → Prop}
    (hp : ∀ᵐ a ∂ν, p a) (a : α) : p a := by
  by_contra h
  exact absurd (measure_mono_null (Set.singleton_subset_iff.mpr h) (ae_iff.mp hp)) (hν a).ne'

/-- `rnDeriv` is pointwise finite when the reference measure has full support on singletons. -/
lemma rnDeriv_ne_top_of_forall_singleton_pos [SigmaFinite μ]
    (hν : ∀ a, ν {a} > 0) (a : α) : μ.rnDeriv ν a ≠ ⊤ :=
  (forall_of_ae_of_forall_singleton_pos hν (Measure.rnDeriv_lt_top μ ν) a).ne

end Measure

namespace Kernel

/-- Kernel `rnDeriv` is pointwise finite when the reference kernel has full support
    on singletons. -/
lemma rnDeriv_ne_top_of_forall_singleton_pos
    [MeasurableSpace.CountableOrCountablyGenerated α β]
    {κ η : Kernel α β} [IsFiniteKernel κ] [IsFiniteKernel η]
    (hη : ∀ a b, η a {b} > 0) (a : α) (b : β) :
    Kernel.rnDeriv κ η a b ≠ ⊤ :=
  (Measure.forall_of_ae_of_forall_singleton_pos (hη a) (Kernel.rnDeriv_lt_top κ η) b).ne

end Kernel

variable {γ : Type*} {mγ : MeasurableSpace γ}

namespace Measure.AbsolutelyContinuous

/-- If `κ a` is absolutely continuous wrt `η a`, then so is the kernel compProd at `a`. -/
lemma kernel_compProd_left {κ η : Kernel α β} [IsSFiniteKernel κ] [IsSFiniteKernel η]
  {ξ : Kernel (α × β) γ} [IsSFiniteKernel ξ] {a : α} (hac : κ a ≪ η a) :
  (κ ⊗ₖ ξ) a ≪ (η ⊗ₖ ξ) a := by
  simp_rw [Kernel.compProd_apply_eq_compProd_sectR, hac.compProd_left _]

end Measure.AbsolutelyContinuous
