/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne
-/
import LeanBandits.ForMathlib.KernelSub
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import Mathlib.Probability.Independence.Basic
import Mathlib.Probability.Independence.Conditional

open MeasureTheory ProbabilityTheory Finset
open scoped ENNReal NNReal

variable {α β γ δ Ω Ω' : Type*}
  {m mα : MeasurableSpace α} {μ : Measure α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
  {mδ : MeasurableSpace δ}
  [MeasurableSpace Ω] [StandardBorelSpace Ω] [Nonempty Ω]
  [mΩ' : MeasurableSpace Ω'] [StandardBorelSpace Ω'] [Nonempty Ω']
  {X : α → β} {Y : α → Ω} {Z : α → Ω'} {T : α → γ}

lemma ae_map_iff_ae_trim {f : α → β} (hf : Measurable f) {p : β → Prop}
    (hp : MeasurableSet { x | p x }) :
    (∀ᵐ y ∂μ.map f, p y) ↔ ∀ᵐ x ∂(μ.trim hf.comap_le), p (f x) := by
  rw [← map_trim_comap hf, ae_map_iff (Measurable.of_comap_le le_rfl).aemeasurable hp]

@[fun_prop]
lemma Measurable.coe_nat_enat {f : α → ℕ} (hf : Measurable f) :
    Measurable (fun a ↦ (f a : ℕ∞)) := Measurable.comp (by fun_prop) hf

@[fun_prop]
lemma Measurable.toNat {f : α → ℕ∞} (hf : Measurable f) : Measurable (fun a ↦ (f a).toNat) :=
  Measurable.comp (by fun_prop) hf

namespace MeasureTheory.Measure

lemma trim_eq_map {hm : m ≤ mα} : μ.trim hm = @Measure.map _ _ mα m id μ := by
  refine @Measure.ext _ m _ _ fun s hs ↦ ?_
  rw [trim_measurableSet_eq _ hs, Measure.map_apply _ hs]
  · simp
  · intro t ht
    simp only [Set.preimage_id_eq, id_eq]
    exact hm _ ht

lemma trim_comap_apply (hX : Measurable X) {s : Set β} (hs : MeasurableSet s) :
    μ.trim hX.comap_le (X ⁻¹' s) = μ.map X s := by
  rw [trim_measurableSet_eq, Measure.map_apply (by fun_prop) hs]
  exact ⟨s, hs, rfl⟩

end MeasureTheory.Measure

namespace ProbabilityTheory

section IndepFun

-- fix the lemma in mathlib to allow different types for the functions
theorem CondIndepFun.symm'
    [StandardBorelSpace α] {hm : m ≤ mα} [IsFiniteMeasure μ] {f : α → β} {g : α → γ}
    (hfg : CondIndepFun m hm f g μ) :
    CondIndepFun m hm g f μ :=
  Kernel.IndepFun.symm hfg

lemma Kernel.IndepFun.of_prod_right {ε Ω : Type*} {mΩ : MeasurableSpace Ω} {mε : MeasurableSpace ε}
    {μ : Measure Ω} {κ : Kernel Ω α} {X : α → β} {Y : α → γ} {T : α → ε}
    (h : IndepFun X (fun ω ↦ (Y ω, T ω)) κ μ) :
    IndepFun X Y κ μ := by
  rw [Kernel.indepFun_iff_measure_inter_preimage_eq_mul] at h ⊢
  intro s t hs ht
  specialize h s (t ×ˢ .univ) hs (ht.prod .univ)
  simpa [Set.mk_preimage_prod] using h

lemma Kernel.IndepFun.of_prod_left {ε Ω : Type*} {mΩ : MeasurableSpace Ω} {mε : MeasurableSpace ε}
    {μ : Measure Ω} {κ : Kernel Ω α} {X : α → β} {Y : α → γ} {T : α → ε}
    (h : IndepFun (fun ω ↦ (X ω, T ω)) Y κ μ) :
    IndepFun X Y κ μ := h.symm.of_prod_right.symm

lemma CondIndepFun.of_prod_right {ε : Type*} {mε : MeasurableSpace ε}
    [StandardBorelSpace α] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → γ} {Z : α → δ} {T : α → ε} (hZ : Measurable Z)
    (h : X ⟂ᵢ[Z, hZ; μ] (fun ω ↦ (Y ω, T ω))) :
    X ⟂ᵢ[Z, hZ; μ] Y :=
  Kernel.IndepFun.of_prod_right h

lemma CondIndepFun.of_prod_left {ε : Type*} {mε : MeasurableSpace ε}
    [StandardBorelSpace α] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → γ} {Z : α → δ} {T : α → ε} (hZ : Measurable Z)
    (h : (fun ω ↦ (X ω, T ω)) ⟂ᵢ[Z, hZ; μ] Y) :
    X ⟂ᵢ[Z, hZ; μ] Y :=
  Kernel.IndepFun.of_prod_left h

lemma CondIndepFun.prod_right [StandardBorelSpace α] [IsFiniteMeasure μ]
    {X : α → β} {Y : α → γ} {Z : α → δ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : X ⟂ᵢ[Z, hZ; μ] Y) :
    X ⟂ᵢ[Z, hZ; μ] (fun ω ↦ (Y ω, Z ω)) := by
  sorry

end IndepFun

section CondDistrib

variable [IsFiniteMeasure μ]

lemma condDistrib_prod_left [StandardBorelSpace β] [Nonempty β]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hT : AEMeasurable T μ) :
    condDistrib (fun ω ↦ (X ω, Y ω)) T μ
      =ᵐ[μ.map T] condDistrib X T μ ⊗ₖ condDistrib Y (fun ω ↦ (T ω, X ω)) μ := by
  refine condDistrib_ae_eq_of_measure_eq_compProd (μ := μ) T (by fun_prop) ?_
  rw [← Measure.compProd_assoc', compProd_map_condDistrib hX, compProd_map_condDistrib hY,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

lemma fst_condDistrib_prod [StandardBorelSpace β] [Nonempty β]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hT : AEMeasurable T μ) :
    (condDistrib (fun ω ↦ (X ω, Y ω)) T μ).fst =ᵐ[μ.map T] condDistrib X T μ := by
  filter_upwards [condDistrib_prod_left hX hY hT] with c hc
  rw [Kernel.fst_apply, hc, ← Kernel.fst_apply, Kernel.fst_compProd]

lemma condDistrib_of_indepFun (h : IndepFun X Y μ) (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    condDistrib Y X μ =ᵐ[μ.map X] Kernel.const β (μ.map Y) := by
  refine condDistrib_ae_eq_of_measure_eq_compProd (μ := μ) X hY ?_
  simp only [Measure.compProd_const]
  exact (indepFun_iff_map_prod_eq_prod_map_map hX hY).mp h

lemma indepFun_iff_condDistrib_eq_const (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) :
    IndepFun X Y μ ↔ condDistrib Y X μ =ᵐ[μ.map X] Kernel.const β (μ.map Y) := by
  refine ⟨fun h ↦ condDistrib_of_indepFun h hX hY, fun h ↦ ?_⟩
  rw [indepFun_iff_map_prod_eq_prod_map_map hX hY, ← compProd_map_condDistrib hY,
    Measure.compProd_congr h]
  simp

lemma Measure.snd_compProd_prodMkLeft {α β γ : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {μ : Measure (α × β)} [SFinite μ] {κ : Kernel β γ} [IsSFiniteKernel κ] :
    (μ ⊗ₘ (κ.prodMkLeft α)).snd = κ ∘ₘ μ.snd := by
  ext s hs
  rw [Measure.snd_apply hs, Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.bind_apply hs (by fun_prop), Measure.snd,
    lintegral_map (κ.measurable_coe hs) (by fun_prop)]
  simp only [Kernel.prodMkLeft_apply]
  congr

lemma Measure.snd_compProd_prodMkRight {α β γ : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {μ : Measure (α × β)} [SFinite μ] {κ : Kernel α γ} [IsSFiniteKernel κ] :
    (μ ⊗ₘ (κ.prodMkRight β)).snd = κ ∘ₘ μ.fst := by
  ext s hs
  rw [Measure.snd_apply hs, Measure.compProd_apply (hs.preimage (by fun_prop)),
    Measure.bind_apply hs (by fun_prop), Measure.fst,
    lintegral_map (κ.measurable_coe hs) (by fun_prop)]
  simp only [Kernel.prodMkRight_apply]
  congr

lemma Measure.snd_prodAssoc_compProd_prodMkLeft {α β γ : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {μ : Measure (α × β)} [SFinite μ] {κ : Kernel β γ} [IsSFiniteKernel κ] :
    (((μ ⊗ₘ (κ.prodMkLeft α))).map MeasurableEquiv.prodAssoc).snd = μ.snd ⊗ₘ κ := by
  ext s hs
  rw [Measure.snd_apply hs, Measure.map_apply (by fun_prop) (hs.preimage (by fun_prop)),
    Measure.compProd_apply, Measure.compProd_apply hs, Measure.snd, lintegral_map _ (by fun_prop)]
  · simp only [Kernel.prodMkLeft_apply]
    congr
  · exact Kernel.measurable_kernel_prodMk_left hs
  · exact hs.preimage (by fun_prop)

lemma Measure.todo {α β γ : Type*}
    {mα : MeasurableSpace α} {mβ : MeasurableSpace β} {mγ : MeasurableSpace γ}
    {μ : Measure (α × β)} [SFinite μ] {κ : Kernel α γ} [IsSFiniteKernel κ] :
    (((((μ ⊗ₘ (κ.prodMkRight β))).map Prod.swap).map MeasurableEquiv.prodAssoc.symm).fst).map
        Prod.swap
      = μ.fst ⊗ₘ κ := by
  rw [Measure.map_map (by fun_prop) (by fun_prop), Measure.fst,
    Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
  ext s hs
  rw [Measure.map_apply (by fun_prop) hs, Measure.compProd_apply hs,
    Measure.compProd_apply (hs.preimage (by fun_prop)), Measure.fst, lintegral_map _ (by fun_prop)]
  · congr
  · exact Kernel.measurable_kernel_prodMk_left hs

lemma ProbabilityMeasure.ext_iff_coe {α : Type*} {mα : MeasurableSpace α}
    {μ ν : ProbabilityMeasure α} :
    μ = ν ↔ (μ : Measure α) = ν := Subtype.ext_iff

lemma FiniteMeasure.ext_iff_coe {α : Type*} {mα : MeasurableSpace α} {μ ν : FiniteMeasure α} :
    μ = ν ↔ (μ : Measure α) = ν := Subtype.ext_iff

instance : PartialOrder (FiniteMeasure α) :=
  PartialOrder.lift _ FiniteMeasure.toMeasure_injective

lemma FiniteMeasure.le_iff_coe {μ ν : FiniteMeasure α} :
    μ ≤ ν ↔ (μ : Measure α) ≤ (ν : Measure α) := Iff.rfl

noncomputable
instance : Sub (FiniteMeasure α) :=
  ⟨fun μ ν ↦ ⟨μ.toMeasure - ν.toMeasure, inferInstance⟩⟩

lemma FiniteMeasure.sub_def (μ ν : FiniteMeasure α) :
    μ - ν = ⟨μ.toMeasure - ν.toMeasure, inferInstance⟩ :=
  rfl

@[simp, norm_cast]
theorem FiniteMeasure.toMeasure_sub (μ ν : FiniteMeasure α) : ↑(μ - ν) = (↑μ - ↑ν : Measure α) :=
  rfl

instance : CanonicallyOrderedAdd (FiniteMeasure α) where
  le_add_self := sorry -- was not needed before?
  exists_add_of_le {μ ν} hμν := by
    refine ⟨ν - μ, ?_⟩
    rw [FiniteMeasure.ext_iff_coe]
    simp only [FiniteMeasure.toMeasure_add, FiniteMeasure.toMeasure_sub]
    rw [add_comm, Measure.sub_add_cancel_of_le hμν]
  le_self_add μ ν := by
    simp only [FiniteMeasure.le_iff_coe, FiniteMeasure.toMeasure_add]
    exact Measure.le_add_right le_rfl

instance : OrderedSub (FiniteMeasure α) where
  tsub_le_iff_right μ ν ξ := by
    simp only [FiniteMeasure.le_iff_coe, FiniteMeasure.toMeasure_sub, FiniteMeasure.toMeasure_add]
    exact Measure.sub_le_iff_add

lemma Kernel.prodMkLeft_ae_eq_iff [MeasurableSpace.CountableOrCountablyGenerated α β]
    {κ η : Kernel α β} [IsFiniteKernel κ] [IsFiniteKernel η]
    {μ : Measure (γ × α)} :
    κ.prodMkLeft γ =ᵐ[μ] η.prodMkLeft γ ↔ κ =ᵐ[μ.snd] η := by
  rw [Measure.snd, Filter.EventuallyEq, Filter.EventuallyEq, ae_map_iff (by fun_prop)]
  · simp
  · classical
    exact Kernel.measurableSet_eq κ η

lemma Kernel.prodMkRight_ae_eq_iff [MeasurableSpace.CountableOrCountablyGenerated α β]
    {κ η : Kernel α β} [IsFiniteKernel κ] [IsFiniteKernel η]
    {μ : Measure (α × γ)} :
    κ.prodMkRight γ =ᵐ[μ] η.prodMkRight γ ↔ κ =ᵐ[μ.fst] η := by
  rw [Measure.fst, Filter.EventuallyEq, Filter.EventuallyEq, ae_map_iff (by fun_prop)]
  · simp
  · classical
    exact Kernel.measurableSet_eq κ η

omit [StandardBorelSpace Ω'] [Nonempty Ω'] in
lemma condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkRight
    [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) {η : Kernel Ω' Ω}
    [IsMarkovKernel η]
    (h : condDistrib Y (fun ω ↦ (Z ω, X ω)) μ =ᵐ[μ.map (fun ω ↦ (Z ω, X ω))] η.prodMkRight _) :
    Y ⟂ᵢ[Z, hZ; μ] X := by
  have hη_eq : condDistrib Y Z μ =ᵐ[μ.map Z] η := by
    rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)] at h ⊢
    have h_fst : μ.map Z = (μ.map (fun ω ↦ (Z ω, X ω))).fst := by
      rw [Measure.fst_map_prodMk hX]
    rw [h_fst, ← Measure.todo, ← h, Measure.map_map (by fun_prop) (by fun_prop),
      Measure.map_map (by fun_prop) (by fun_prop), Measure.fst,
      Measure.map_map (by fun_prop) (by fun_prop), Measure.map_map (by fun_prop) (by fun_prop)]
    congr
  symm
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY hX hZ]
  refine h.trans ?_
  rw [Kernel.prodMkRight_ae_eq_iff, Measure.fst_map_prodMk (by fun_prop)]
  exact hη_eq.symm

omit [StandardBorelSpace Ω'] [Nonempty Ω'] in
lemma condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkLeft
    [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z) {η : Kernel Ω' Ω}
    [IsMarkovKernel η]
    (h : condDistrib Y (fun ω ↦ (X ω, Z ω)) μ =ᵐ[μ.map (fun ω ↦ (X ω, Z ω))] η.prodMkLeft _) :
    Y ⟂ᵢ[Z, hZ; μ] X := by
  refine condIndepFun_of_exists_condDistrib_prod_ae_eq_prodMkRight hX hY hZ ?_ (η := η)
  sorry

/-- Law of `Y` conditioned on `X`. -/
notation "𝓛[" Y " | " X "; " μ "]" => condDistrib Y X μ

-- generalize to map instead of fst
omit [StandardBorelSpace Ω'] [Nonempty Ω'] in
lemma condIndepFun_fst_prod [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace γ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (ν : Measure γ) [IsProbabilityMeasure ν]
    (h_indep : CondIndepFun (mΩ'.comap Z) hZ.comap_le Y X μ) :
    CondIndepFun (mΩ'.comap (fun ω ↦ Z ω.1)) (hZ.comp measurable_fst).comap_le
      (fun ω ↦ Y ω.1) (fun ω ↦ X ω.1) (μ.prod ν) := by
  rw [condIndepFun_iff_map_prod_eq_prod_condDistrib_prod_condDistrib (by fun_prop)
    (by fun_prop) (by fun_prop)] at h_indep ⊢
  have h1 : 𝓛[fun ω ↦ Y ω.1 | fun ω ↦ Z ω.1; μ.prod ν] =ᵐ[μ.map Z] 𝓛[Y | Z; μ] :=
    condDistrib_fst_prod (Y := Y) (X := Z) (ν := ν) (μ := μ) (by fun_prop)
  have h2 : 𝓛[fun ω ↦ X ω.1 | fun ω ↦ Z ω.1; μ.prod ν] =ᵐ[μ.map Z] 𝓛[X | Z; μ] :=
    condDistrib_fst_prod (Y := X) (X := Z) (ν := ν) (μ := μ) (by fun_prop)
  have h_fst1 : (μ.prod ν).map (fun ω ↦ Z ω.1) = μ.map Z := by
    conv_rhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  have h_fst2 : (μ.prod ν).map (fun ω ↦ (Z ω.1, Y ω.1, X ω.1))
      = μ.map (fun ω ↦ (Z ω, Y ω, X ω)) := by
    conv_rhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst,
      Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [h_fst1, h_fst2, h_indep]
  refine Measure.bind_congr_right ?_
  filter_upwards [h1, h2] with x hx1 hx2
  simp_rw [Kernel.prod_apply]
  rw [hx1, ← hx2]

omit [StandardBorelSpace Ω] [Nonempty Ω] in
lemma indepFun_fst_prod (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (h_indep : IndepFun X Y μ)
    (ν : Measure γ) [IsProbabilityMeasure ν] :
    IndepFun (fun ω ↦ X ω.1) (fun ω ↦ Y ω.1) (μ.prod ν) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)] at h_indep ⊢
  have :  AEMeasurable (fun ω ↦ (X ω, Y ω)) (Measure.map Prod.fst (μ.prod ν)) := by
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
    fun_prop
  have :  AEMeasurable X (Measure.map Prod.fst (μ.prod ν)) := by
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
    fun_prop
  have :  AEMeasurable Y (Measure.map Prod.fst (μ.prod ν)) := by
    simp only [Measure.map_fst_prod, measure_univ, one_smul]
    fun_prop
  have h : (μ.prod ν).map (fun ω ↦ (X ω.1, Y ω.1)) = μ.map (fun ω ↦ (X ω, Y ω)) := by
    conv_rhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst,
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    rfl
  rw [h, h_indep]
  conv_lhs => rw [← Measure.fst_prod (μ := μ) (ν := ν), Measure.fst,
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop),
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

omit [StandardBorelSpace Ω] [Nonempty Ω] in
lemma indepFun_snd_prod (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (h_indep : IndepFun X Y μ)
    (ν : Measure γ) [IsProbabilityMeasure ν] :
    IndepFun (fun ω ↦ X ω.2) (fun ω ↦ Y ω.2) (ν.prod μ) := by
  rw [indepFun_iff_map_prod_eq_prod_map_map (by fun_prop) (by fun_prop)] at h_indep ⊢
  have :  AEMeasurable (fun ω ↦ (X ω, Y ω)) (Measure.map Prod.snd (ν.prod μ)) := by
    simp only [Measure.map_snd_prod, measure_univ, one_smul]
    fun_prop
  have :  AEMeasurable X (Measure.map Prod.snd (ν.prod μ)) := by
    simp only [Measure.map_snd_prod, measure_univ, one_smul]
    fun_prop
  have :  AEMeasurable Y (Measure.map Prod.snd (ν.prod μ)) := by
    simp only [Measure.map_snd_prod, measure_univ, one_smul]
    fun_prop
  have h : (ν.prod μ).map (fun ω ↦ (X ω.2, Y ω.2)) = μ.map (fun ω ↦ (X ω, Y ω)) := by
    conv_rhs => rw [← Measure.snd_prod (μ := ν) (ν := μ), Measure.snd,
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
    rfl
  rw [h, h_indep]
  conv_lhs => rw [← Measure.snd_prod (μ := ν) (ν := μ), Measure.snd,
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop),
      AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

end CondDistrib

section Cond

lemma condDistrib_ae_eq_cond [Countable β] [MeasurableSingletonClass β]
    [IsFiniteMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) :
    condDistrib Y X μ =ᵐ[μ.map X] fun b ↦ (μ[|X ⁻¹' {b}]).map Y := by
  rw [Filter.EventuallyEq, ae_iff_of_countable]
  intro b hb
  ext s hs
  rw [condDistrib_apply_of_ne_zero hY,
    Measure.map_apply hX (measurableSet_singleton _), Measure.map_apply hY hs,
    Measure.map_apply (hX.prodMk hY) ((measurableSet_singleton _).prod hs),
    cond_apply (hX (measurableSet_singleton _))]
  · congr
  · exact hb

lemma cond_of_indepFun [IsZeroOrProbabilityMeasure μ] (h : IndepFun X T μ)
    (hX : Measurable X) (hT : Measurable T) {s : Set β} (hs : MeasurableSet s)
    (hμs : μ (X ⁻¹' s) ≠ 0) :
    (μ[|X ⁻¹' s]).map T = μ.map T := by
  ext t ht
  rw [Measure.map_apply (by fun_prop) ht, Measure.map_apply (by fun_prop) ht, cond_apply (hX hs),
    IndepSet.measure_inter_eq_mul, ← mul_assoc, ENNReal.inv_mul_cancel, one_mul]
  · exact hμs
  · simp
  · rw [indepFun_iff_indepSet_preimage hX hT] at h
    exact h s t hs ht

omit [Nonempty Ω'] in
lemma cond_of_condIndepFun [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β] [Countable β]
    [Countable Ω']
    [IsZeroOrProbabilityMeasure μ]
    (hZ : Measurable Z)
    (h : CondIndepFun (MeasurableSpace.comap Z inferInstance) hZ.comap_le Y X μ)
    (hX : Measurable X) (hY : Measurable Y) {b : β} {ω : Ω'}
    (hμ : μ (Z ⁻¹' {ω} ∩ X ⁻¹' {b}) ≠ 0) :
    (μ[|Z ⁻¹' {ω} ∩ X ⁻¹' {b}]).map Y = (μ[|Z ⁻¹' {ω}]).map Y := by
  symm at h
  have h := (condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY hX hZ).mp h
  have h_left := condDistrib_ae_eq_cond (hZ.prodMk hX) hY (μ := μ)
  have h_right := condDistrib_ae_eq_cond hZ hY (μ := μ)
  rw [Filter.EventuallyEq, ae_iff_of_countable] at h h_left h_right
  specialize h (ω, b)
  specialize h_left (ω, b)
  specialize h_right ω
  rw [Measure.map_apply (by fun_prop) (measurableSet_singleton _)] at h h_left h_right
  rw [← Set.singleton_prod_singleton, Set.mk_preimage_prod] at h h_left
  have hZ_ne : μ (Z ⁻¹' {ω}) ≠ 0 := fun h ↦ hμ (measure_mono_null Set.inter_subset_left h)
  rw [← h_right hZ_ne, ← h_left hμ, h hμ]
  simp

end Cond

end ProbabilityTheory
