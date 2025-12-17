/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import Mathlib.Probability.Kernel.RadonNikodym

/-!
# Kernels substraction

-/

open MeasureTheory MeasurableSpace
open scoped ENNReal

namespace MeasureTheory.Measure

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {μ ν ξ : Measure α}

lemma sub_le_iff_add_of_le [IsFiniteMeasure ν] (h_le : ν ≤ μ) : μ - ν ≤ ξ ↔ μ ≤ ξ + ν := by
  refine ⟨fun h ↦ ?_, Measure.sub_le_of_le_add⟩
  rw [Measure.le_iff] at h ⊢
  intro s hs
  specialize h s hs
  simp only [Measure.coe_add, Pi.add_apply]
  rwa [Measure.sub_apply hs h_le, tsub_le_iff_right] at h

lemma sub_le_iff_add [IsFiniteMeasure μ] [IsFiniteMeasure ν] : μ - ν ≤ ξ ↔ μ ≤ ξ + ν := by
  refine ⟨fun h ↦ ?_, Measure.sub_le_of_le_add⟩
  obtain ⟨s, hs⟩ := exists_isHahnDecomposition μ ν
  suffices μ.restrict s ≤ ξ.restrict s + ν.restrict s
      ∧ μ.restrict sᶜ ≤ ξ.restrict sᶜ + ν.restrict sᶜ by
    have h_eq_restrict (μ : Measure α) : μ = μ.restrict s + μ.restrict sᶜ := by
      rw [Measure.restrict_add_restrict_compl hs.measurableSet]
    rw [h_eq_restrict μ, h_eq_restrict ξ, h_eq_restrict ν]
    suffices μ.restrict s + μ.restrict sᶜ
        ≤ ξ.restrict s + ν.restrict s + (ξ.restrict sᶜ + ν.restrict sᶜ) by
      refine this.trans_eq ?_
      abel
    gcongr
    · exact this.1
    · exact this.2
  constructor
  · have h_le := hs.le_on
    refine h_le.trans ?_
    exact Measure.le_add_left le_rfl
  · have h_le := hs.ge_on_compl
    have h' : μ.restrict sᶜ - ν.restrict sᶜ ≤ ξ.restrict sᶜ := by
      rw [← Measure.restrict_sub_eq_restrict_sub_restrict hs.measurableSet.compl]
      exact Measure.restrict_mono subset_rfl h
    exact (Measure.sub_le_iff_add_of_le h_le).mp h'

lemma add_sub_of_mutuallySingular (h : μ ⟂ₘ ξ) : μ + (ν - ξ) = μ + ν - ξ := by
  let s := h.nullSet
  have hs : MeasurableSet s := h.measurableSet_nullSet
  suffices μ.restrict s + (ν - ξ).restrict s = μ.restrict s + ν.restrict s - ξ.restrict s
      ∧ μ.restrict sᶜ + (ν - ξ).restrict sᶜ = μ.restrict sᶜ + ν.restrict sᶜ - ξ.restrict sᶜ by
    calc μ + (ν - ξ)
    _ = μ.restrict s + μ.restrict sᶜ + (ν - ξ).restrict s + (ν - ξ).restrict sᶜ := by
      rw [restrict_add_restrict_compl hs, add_assoc, restrict_add_restrict_compl hs]
    _ = μ.restrict s + (ν - ξ).restrict s + (μ.restrict sᶜ + (ν - ξ).restrict sᶜ) := by abel
    _ = (μ.restrict s + ν.restrict s - ξ.restrict s) +
        (μ.restrict sᶜ + ν.restrict sᶜ - ξ.restrict sᶜ) := by rw [this.1, this.2]
    _ = (μ + ν - ξ).restrict s + (μ + ν - ξ).restrict sᶜ := by
        simp [restrict_sub_eq_restrict_sub_restrict hs,
          restrict_sub_eq_restrict_sub_restrict hs.compl]
    _ = μ + ν - ξ := by rw [restrict_add_restrict_compl hs]
  constructor
  · rw [h.restrict_nullSet, restrict_sub_eq_restrict_sub_restrict hs]
    simp
  · rw [restrict_sub_eq_restrict_sub_restrict hs.compl, h.restrict_compl_nullSet]
    simp

lemma withDensity_sub_aux {f g : α → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity g)]
    (hg : Measurable g) (hgf : g ≤ᵐ[μ] f) :
    (μ.withDensity f - μ.withDensity g) = μ.withDensity (f - g) := by
  refine le_antisymm ?_ ?_
  · refine sub_le_of_le_add ?_
    rw [← withDensity_add_right _ hg]
    refine withDensity_mono (ae_of_all _ fun x ↦ ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    exact le_tsub_add
  · rw [sub_def, le_sInf_iff]
    intro ξ hξ
    simp only [Set.mem_setOf_eq] at hξ
    rw [le_iff] at hξ ⊢
    intro s hs
    specialize hξ s hs
    simp only [coe_add, Pi.add_apply] at hξ
    simp_rw [withDensity_apply _ hs] at hξ ⊢
    simp only [Pi.sub_apply]
    rw [lintegral_sub hg]
    · rwa [tsub_le_iff_right]
    · rw [← withDensity_apply _ hs]
      simp
    · exact ae_restrict_of_ae hgf

lemma withDensity_sub {f g : α → ℝ≥0∞} [IsFiniteMeasure (μ.withDensity g)]
    (hf : Measurable f) (hg : Measurable g) :
    (μ.withDensity f - μ.withDensity g) = μ.withDensity (f - g) := by
  refine le_antisymm ?_ ?_
  · refine sub_le_of_le_add ?_
    rw [← withDensity_add_right _ hg]
    refine withDensity_mono (ae_of_all _ fun x ↦ ?_)
    simp only [Pi.add_apply, Pi.sub_apply]
    exact le_tsub_add
  · let t := {x | f x ≤ g x}
    have ht : MeasurableSet t := measurableSet_le hf hg
    rw [← restrict_add_restrict_compl (μ := μ.withDensity (f - g)) ht,
      ← restrict_add_restrict_compl (μ := μ.withDensity f - μ.withDensity g) ht]
    have h_zero : (μ.withDensity (f - g)).restrict t = 0 := by
      simp only [restrict_eq_zero]
      rw [withDensity_apply _ ht, lintegral_eq_zero_iff (by fun_prop)]
      refine ae_restrict_of_forall_mem ht fun x hx ↦ ?_
      simpa [tsub_eq_zero_iff_le]
    rw [h_zero, zero_add]
    suffices (μ.withDensity (f - g)).restrict tᶜ
        ≤ (μ.withDensity f - μ.withDensity g).restrict tᶜ by
      refine this.trans ?_
      exact Measure.le_add_left le_rfl
    rw [restrict_sub_eq_restrict_sub_restrict ht.compl]
    simp_rw [restrict_withDensity ht.compl]
    have : IsFiniteMeasure ((μ.restrict tᶜ).withDensity g) := by
      rw [← restrict_withDensity ht.compl]
      infer_instance
    rw [withDensity_sub_aux hg]
    refine ae_restrict_of_forall_mem ht.compl fun x hx ↦ ?_
    simp only [Set.mem_compl_iff, Set.mem_setOf_eq, not_le, t] at hx
    exact hx.le

lemma sub_apply_eq_rnDeriv_add_singularPart [IsFiniteMeasure μ] [IsFiniteMeasure ν] (s : Set α) :
    (μ - ν) s = ν.withDensity (fun a ↦ μ.rnDeriv ν a - 1) s + μ.singularPart ν s := by
  have hμ : μ = ν.withDensity (fun a ↦ μ.rnDeriv ν a) + μ.singularPart ν := by
    rw [rnDeriv_add_singularPart]
  have hν : ν = ν.withDensity 1 := by rw [withDensity_one]
  conv_lhs => rw [hν, hμ, add_comm _ (μ.singularPart ν)]
  rw [← add_sub_of_mutuallySingular]
  swap
  · simp only [withDensity_one]
    exact mutuallySingular_singularPart μ ν
  simp only [coe_add, Pi.add_apply]
  have : IsFiniteMeasure (ν.withDensity 1) := by simp only [withDensity_one]; infer_instance
  rw [add_comm, withDensity_sub (by fun_prop) (by fun_prop)]
  congr

end MeasureTheory.Measure

namespace ProbabilityTheory.Kernel

variable {α β : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  [CountableOrCountablyGenerated α β] {κ η : Kernel α β}

noncomputable
instance [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)] :
    Sub (Kernel α β) where
  sub κ η := if h : IsSFiniteKernel κ ∧ IsSFiniteKernel η
    then
      have := h.1
      have := h.2
      η.withDensity (fun a ↦ κ.rnDeriv η a - 1) + κ.singularPart η
    else 0

lemma sub_def [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)] :
    κ - η = if h : IsSFiniteKernel κ ∧ IsSFiniteKernel η
    then
      have := h.1
      have := h.2
      η.withDensity (fun a ↦ κ.rnDeriv η a - 1) + κ.singularPart η
    else 0 :=
  rfl

@[simp]
lemma sub_of_not_isSFiniteKernel_left [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    (h : ¬IsSFiniteKernel κ) : κ - η = 0 := by simp [sub_def, h]

@[simp]
lemma sub_of_not_isSFiniteKernel_right [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    (h : ¬IsSFiniteKernel η) : κ - η = 0 := by simp [sub_def, h]

lemma sub_of_isSFiniteKernel [IsSFiniteKernel κ] [IsSFiniteKernel η]
    [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)] :
    κ - η = η.withDensity (fun a ↦ κ.rnDeriv η a - 1) + κ.singularPart η := by
  rw [sub_def, dif_pos]
  exact ⟨inferInstance, inferInstance⟩

-- todo name
lemma sub_apply_eq_rnDeriv_add_singularPart [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    [IsSFiniteKernel κ] [IsSFiniteKernel η] (a : α) :
    (κ - η) a = η.withDensity (fun a ↦ κ.rnDeriv η a - 1) a + κ.singularPart η a := by
  rw [sub_of_isSFiniteKernel]
  rfl

lemma sub_apply [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)] [IsFiniteKernel κ]
    [IsFiniteKernel η] (a : α) :
    (κ - η) a = κ a - η a := by
  ext s hs
  rw [sub_apply_eq_rnDeriv_add_singularPart, Kernel.withDensity_apply _ (by fun_prop),
    Kernel.singularPart_eq_singularPart_measure, Measure.sub_apply_eq_rnDeriv_add_singularPart _]
  simp only [Measure.coe_add, Pi.add_apply]
  congr 2
  refine MeasureTheory.withDensity_congr_ae ?_
  filter_upwards [Kernel.rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb
  simp [← hb]

omit [CountableOrCountablyGenerated α β] in
lemma le_iff (κ η : Kernel α β) : κ ≤ η ↔ ∀ a, κ a ≤ η a := Iff.rfl

lemma sub_le_self [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)] [IsFiniteKernel κ]
    [IsFiniteKernel η] :
    κ - η ≤ κ := by
  rw [le_iff]
  intro a
  rw [sub_apply]
  exact Measure.sub_le

instance [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    [IsFiniteKernel κ] [IsFiniteKernel η] : IsFiniteKernel (κ - η) :=
  isFiniteKernel_of_le sub_le_self

lemma sub_apply_eq_zero_iff_le [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    [IsFiniteKernel κ] [IsFiniteKernel η] (a : α) : (κ - η) a = 0 ↔ κ a ≤ η a := by
  simp_rw [sub_apply_eq_rnDeriv_add_singularPart,
    add_eq_zero_iff_of_nonneg (Measure.zero_le _) (Measure.zero_le _)]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · rw [Kernel.withDensity_apply _ (by fun_prop), withDensity_eq_zero_iff (by fun_prop)] at h
    rw [singularPart_eq_zero_iff_absolutelyContinuous κ η a] at h
    rw [← Measure.rnDeriv_le_one_iff_le h.2]
    filter_upwards [h.1, rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb1 hb2
    rw [← hb2]
    simp only [Pi.sub_apply, Pi.one_apply, Pi.zero_apply] at hb1
    rwa [tsub_eq_zero_iff_le] at hb1
  · rw [(singularPart_eq_zero_iff_absolutelyContinuous κ η a).mpr
        (Measure.absolutelyContinuous_of_le h)]
    rw [Kernel.withDensity_apply _ (by fun_prop), withDensity_eq_zero_iff (by fun_prop)]
    simp only [and_true]
    suffices κ.rnDeriv η a ≤ᵐ[η a] 1 by
      filter_upwards [this] with b hb
      simpa [tsub_eq_zero_iff_le] using hb
    filter_upwards [Measure.rnDeriv_le_one_of_le h,
      rnDeriv_eq_rnDeriv_measure (κ := κ) (η := η) (a := a)] with b hb1 hb2
    rwa [hb2]

lemma sub_eq_zero_iff_le [∀ η : Kernel α β, Decidable (IsSFiniteKernel η)]
    [IsFiniteKernel κ] [IsFiniteKernel η] : κ - η = 0 ↔ κ ≤ η := by
  simp [Kernel.ext_iff, le_iff, sub_apply_eq_zero_iff_le]

lemma measurableSet_eq_zero (κ : Kernel α β) [IsFiniteKernel κ] :
    MeasurableSet {a | κ a = 0} := by
  have h_sing : {a | κ a = 0} = {a | κ a ⟂ₘ κ a} := by ext; simp
  rw [h_sing]
  exact measurableSet_mutuallySingular κ κ

lemma measurableSet_eq (κ η : Kernel α β) [IsFiniteKernel κ] [IsFiniteKernel η] :
    MeasurableSet {a | κ a = η a} := by
  classical
  have h_sub : {a | κ a = η a} = {a | (κ - η) a = 0} ∩ {a | (η - κ) a = 0} := by
    ext1 a
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, sub_apply_eq_zero_iff_le]
    exact ⟨fun h ↦ by simp [h], fun h ↦ le_antisymm h.1 h.2⟩
  rw [h_sub]
  refine MeasurableSet.inter ?_ ?_
  · exact measurableSet_eq_zero _
  · exact measurableSet_eq_zero _

end ProbabilityTheory.Kernel
