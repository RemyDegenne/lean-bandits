/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import Mathlib.Probability.Kernel.CompProdEqIff
import Mathlib.Probability.Kernel.Composition.MeasureComp
/-!
# Interactions of `withDensity` with `compProd`, `map`, and `swap`

Lemmas for pushing `Measure.withDensity` and `Kernel.withDensity` through
`compProd`, `MeasurableEquiv.map`, `Prod.swap`, and composition.
-/

open MeasureTheory ProbabilityTheory

open scoped ENNReal

variable {α β γ : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
    {mγ : MeasurableSpace γ} {μ : Measure α}

namespace Measure

/-- Composing `withDensity` on the measure side of a `compProd`:
`(μ.withDensity f) ⊗ₘ κ = (μ ⊗ₘ κ).withDensity (f ∘ Prod.fst)`. -/
lemma withDensity_compProd_left [SFinite μ] {κ : Kernel α β} [IsSFiniteKernel κ]
    {f : α → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f) ⊗ₘ κ = (μ ⊗ₘ κ).withDensity (f ∘ Prod.fst) := by
  ext s hs
  rw [Measure.compProd_apply hs, withDensity_apply _ hs,
    lintegral_withDensity_eq_lintegral_mul₀ hf.aemeasurable
      (Kernel.measurable_kernel_prodMk_left hs).aemeasurable,
    ← lintegral_indicator hs,
    Measure.lintegral_compProd ((hf.comp measurable_fst).indicator hs)]
  congr 1
  ext a
  simp_rw [Pi.mul_apply]
  have : (fun b ↦ s.indicator (f ∘ Prod.fst) (a, b)) =
      fun b ↦ (Prod.mk a ⁻¹' s).indicator (fun _ ↦ f a) b := by
    ext b; simp only [Function.comp, Set.indicator, Set.mem_preimage]; rfl
  rw [this, lintegral_indicator_const (hs.preimage (by fun_prop))]

/-- Mapping a `withDensity` through `MeasurableEquiv.symm`:
`(μ.withDensity f).map e.symm = (μ.map e.symm).withDensity (f ∘ e)`. -/
lemma withDensity_map_equiv_symm
    {μ : Measure β} {e : α ≃ᵐ β} {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity f).map e.symm = (μ.map e.symm).withDensity (f ∘ e) := by
  ext s hs
  rw [Measure.map_apply e.symm.measurable hs,
    withDensity_apply _ (e.symm.measurable hs),
    withDensity_apply _ hs, Measure.restrict_map e.symm.measurable hs,
    lintegral_map (hf.comp e.measurable) e.symm.measurable]
  simp_rw [Function.comp_apply, e.apply_symm_apply]

/-- Mapping a `withDensity` through a `MeasurableEquiv` from the snd component. -/
lemma map_swap_withDensity_fst
    {μ : Measure (α × β)} [SFinite μ]
    {f : β → ℝ≥0∞} (hf : Measurable f) :
    (μ.withDensity (f ∘ Prod.snd)).map Prod.swap
      = (μ.map Prod.swap).withDensity (f ∘ Prod.fst) := by
  ext s hs
  rw [Measure.map_apply measurable_swap hs, withDensity_apply _ (measurable_swap hs),
    withDensity_apply _ hs, Measure.restrict_map measurable_swap hs]
  exact (lintegral_map (hf.comp measurable_fst) measurable_swap).symm

/-- `(μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f`. -/
lemma map_withDensity_comp
    {g : α → γ} {f : γ → ℝ≥0∞}
    (hg : Measurable g) (hf : Measurable f) :
    (μ.withDensity (f ∘ g)).map g = (μ.map g).withDensity f := by
  ext s hs
  simp only [Measure.map_apply hg hs, withDensity_apply _ (hg hs), withDensity_apply _ hs,
    setLIntegral_map hs hf hg, Function.comp]

/-- `(κ.withDensity (fun _ => f)) ∘ₘ μ = (κ ∘ₘ μ).withDensity f`. -/
lemma comp_withDensity_const
    [SFinite μ]
    {κ : Kernel α γ} [IsSFiniteKernel κ]
    {f : γ → ℝ≥0∞} (hf : Measurable f)
    [IsSFiniteKernel (κ.withDensity (fun _ => f))] :
    (κ.withDensity (fun _ => f)) ∘ₘ μ = (κ ∘ₘ μ).withDensity f := by
  rw [← Measure.snd_compProd μ (κ.withDensity (fun _ => f)),
    Measure.compProd_withDensity (show Measurable (Function.uncurry (fun (_ : α) => f)) from
      hf.comp measurable_snd),
    ← Measure.snd_compProd μ κ, Measure.snd, Measure.snd]
  exact map_withDensity_comp measurable_snd hf

/-- `(μ.withDensity f) ⊗ₘ (κ.withDensity g) = (μ ⊗ₘ κ).withDensity (f ∘ fst * uncurry g)`. -/
lemma withDensity_compProd_withDensity [SFinite μ]
    {κ : Kernel α γ} [IsSFiniteKernel κ]
    {f : α → ℝ≥0∞} {g : α → γ → ℝ≥0∞}
    (hf : Measurable f) (hg : Measurable (Function.uncurry g))
    [IsSFiniteKernel (κ.withDensity g)] :
    (μ.withDensity f) ⊗ₘ (κ.withDensity g) =
      (μ ⊗ₘ κ).withDensity (f ∘ Prod.fst * Function.uncurry g) := by
  rw [Measure.compProd_withDensity hg, withDensity_compProd_left hf]
  exact (withDensity_mul _ (hf.comp measurable_fst) hg).symm

end Measure
