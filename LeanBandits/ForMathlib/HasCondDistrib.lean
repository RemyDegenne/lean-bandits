/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.CondDistrib
import Mathlib.Probability.HasLaw

/-!
# A predicate for having a specified conditional distribution
-/

open MeasureTheory

namespace ProbabilityTheory

variable {α β γ Ω Ω' : Type*}
  {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [Nonempty Ω]
  {mΩ' : MeasurableSpace Ω'} [StandardBorelSpace Ω'] [Nonempty Ω']
  {μ : Measure α} {X : α → β} {Y : α → Ω} {κ : Kernel β Ω}

structure HasCondDistrib (Y : α → Ω) (X : α → β) (κ : Kernel β Ω)
  (μ : Measure α) [IsFiniteMeasure μ] : Prop where
  aemeasurable_fst : AEMeasurable Y μ := by fun_prop
  aemeasurable_snd : AEMeasurable X μ := by fun_prop
  condDistrib_eq : condDistrib Y X μ =ᵐ[μ.map X] κ

lemma hasCondDistrib_fst_prod {Y : α → Ω} {X : α → β}
    {κ : Kernel β Ω}
    {μ : Measure α} [IsFiniteMeasure μ] {ν : Measure γ} [IsProbabilityMeasure ν]
    (h : HasCondDistrib Y X κ μ) :
    HasCondDistrib (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) κ (μ.prod ν) where
  aemeasurable_fst := by have := h.aemeasurable_fst; fun_prop
  aemeasurable_snd := by have := h.aemeasurable_snd; fun_prop
  condDistrib_eq := by
    have : ((μ.prod ν).map (fun ω ↦ X ω.1)) = μ.map X := by
      conv_rhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst]
      rw [AEMeasurable.map_map_of_aemeasurable _ (by fun_prop)]
      · rfl
      · have := h.aemeasurable_snd
        simpa
    rw [this]
    exact (condDistrib_fst_prod X h.aemeasurable_fst ν).trans h.condDistrib_eq

lemma HasCondDistrib.comp [IsFiniteMeasure μ]
    (h : HasCondDistrib Y X κ μ) {f : Ω → Ω'} (hf : Measurable f) :
    HasCondDistrib (fun ω ↦ f (Y ω)) X (κ.map f) μ where
  aemeasurable_fst := by have := h.aemeasurable_fst; fun_prop
  aemeasurable_snd := by have := h.aemeasurable_snd; fun_prop
  condDistrib_eq := by
    have h_comp := condDistrib_comp X (Y := Y) (f := f) (mβ := mβ) h.aemeasurable_fst hf
    refine h_comp.trans ?_
    have h' := h.condDistrib_eq
    filter_upwards [h'] with ω hω
    rw [Kernel.map_apply _ hf, hω, Kernel.map_apply _ hf]

lemma HasCondDistrib.fst {Y : α → Ω × Ω'} {κ : Kernel β (Ω × Ω')} [IsFiniteMeasure μ]
    (h : HasCondDistrib Y X κ μ) :
    HasCondDistrib (fun ω ↦ (Y ω).1) X κ.fst μ := by
  rw [Kernel.fst_eq]
  exact HasCondDistrib.comp h measurable_fst

lemma HasCondDistrib.snd {Y : α → Ω × Ω'} {κ : Kernel β (Ω × Ω')} [IsFiniteMeasure μ]
    (h : HasCondDistrib Y X κ μ) :
    HasCondDistrib (fun ω ↦ (Y ω).2) X κ.snd μ := by
  rw [Kernel.snd_eq]
  exact HasCondDistrib.comp h measurable_snd

lemma HasLaw.prod_of_hasCondDistrib {P : Measure β} [IsFiniteMeasure μ] [IsSFiniteKernel κ]
    (h1 : HasLaw X P μ) (h2 : HasCondDistrib Y X κ μ) :
    HasLaw (fun ω ↦ (X ω, Y ω)) (P ⊗ₘ κ) μ := by
  have hX := h1.aemeasurable
  have hY := h2.aemeasurable_fst
  refine ⟨by fun_prop, ?_⟩
  rw [← compProd_map_condDistrib (by fun_prop), h1.map_eq]
  refine Measure.compProd_congr ?_
  rw [← h1.map_eq]
  exact h2.condDistrib_eq

lemma HasCondDistrib.prod [IsFiniteMeasure μ] [IsFiniteKernel κ]
    {Z : α → Ω'} {η : Kernel (β × Ω) Ω'} [IsFiniteKernel η]
    (h1 : HasCondDistrib Y X κ μ) (h2 : HasCondDistrib Z (fun ω ↦ (X ω, Y ω)) η μ) :
    HasCondDistrib (fun ω ↦ (Y ω, Z ω)) X (κ ⊗ₖ η) μ := by
  have hX := h1.aemeasurable_snd
  have hY := h1.aemeasurable_fst
  have hZ := h2.aemeasurable_fst
  refine ⟨by fun_prop, by fun_prop, ?_⟩
  have h_condDistrib_Y := h1.condDistrib_eq
  have h_condDistrib_Z := h2.condDistrib_eq
  have h_prod := condDistrib_prod_left hY hZ hX
  have h_prod' : 𝓛[fun ω ↦ (Y ω, Z ω) | X; μ] =ᵐ[μ.map X] (κ ⊗ₖ 𝓛[Z | fun ω ↦ (X ω, Y ω); μ]) := by
    filter_upwards [h_condDistrib_Y, h_prod] with ω hω₁ hω₂
    rw [hω₂]
    ext s hs
    rw [Kernel.compProd_apply hs, Kernel.compProd_apply hs]
    simp [hω₁]
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
    at h_condDistrib_Z h_condDistrib_Y ⊢
  rw [← Measure.compProd_assoc', ← h_condDistrib_Y, ← h_condDistrib_Z,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

end ProbabilityTheory
