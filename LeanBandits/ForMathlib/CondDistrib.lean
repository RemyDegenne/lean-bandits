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

namespace ProbabilityTheory

section CondDistrib

variable [IsFiniteMeasure μ]

/-- An ae-equality of kernels wrt the joint law `μ.map (X, Y)` is equivalent to an ae-equality
fiberwise via the conditional distribution of `Y` given `X`. -/
lemma Kernel.ae_eq_map_prod_iff_ae_condDistrib
    [MeasurableSpace.CountableOrCountablyGenerated (β × Ω) δ]
    (hY : AEMeasurable Y μ) {f g : Kernel (β × Ω) δ} [IsFiniteKernel f] [IsFiniteKernel g] :
    f =ᵐ[μ.map (fun ω ↦ (X ω, Y ω))] g ↔
    ∀ᵐ x ∂(μ.map X), ∀ᵐ y ∂(condDistrib Y X μ x), f (x, y) = g (x, y) := by
  rw [← compProd_map_condDistrib hY]
  exact Measure.ae_compProd_iff (Kernel.measurableSet_eq _ _)

lemma condDistrib_prod_left [StandardBorelSpace β] [Nonempty β]
    (hX : AEMeasurable X μ) (hY : AEMeasurable Y μ) (hT : AEMeasurable T μ) :
    condDistrib (fun ω ↦ (X ω, Y ω)) T μ
      =ᵐ[μ.map T] condDistrib X T μ ⊗ₖ condDistrib Y (fun ω ↦ (T ω, X ω)) μ := by
  refine condDistrib_ae_eq_of_measure_eq_compProd (μ := μ) T (by fun_prop) ?_
  rw [← Measure.compProd_assoc', compProd_map_condDistrib hX, compProd_map_condDistrib hY,
    AEMeasurable.map_map_of_aemeasurable (by fun_prop) (by fun_prop)]
  rfl

lemma condDistrib_prod_self_left [StandardBorelSpace β] [Nonempty β] [StandardBorelSpace γ]
    [Nonempty γ]
    (hX : AEMeasurable X μ) (hT : AEMeasurable T μ) :
    condDistrib (fun ω ↦ (X ω, T ω)) T μ =ᵐ[μ.map T] condDistrib X T μ ×ₖ Kernel.id := by
  have h_prod := condDistrib_prod_left hX hT hT (μ := μ)
  have h_fst := condDistrib_comp_self (μ := μ) (fun ω ↦ (T ω, X ω)) (f := Prod.fst) (by fun_prop)
  have h_fst' := (Kernel.ae_eq_map_prod_iff_ae_condDistrib hX).mp h_fst
  filter_upwards [h_prod, h_fst'] with z hz1 hz2
  rw [hz1]
  simp only [Kernel.deterministic_apply] at hz2
  change ∀ᵐ y ∂(condDistrib X T μ z), condDistrib T (fun ω ↦ (T ω, X ω)) μ (z, y) = Measure.dirac z
    at hz2
  ext t ht
  rw [Kernel.compProd_apply ht]
  calc ∫⁻ y, condDistrib T (fun ω ↦ (T ω, X ω)) μ (z, y) (Prod.mk y ⁻¹' t) ∂condDistrib X T μ z
  _ = ∫⁻ y, (Measure.dirac z) (Prod.mk y ⁻¹' t) ∂condDistrib X T μ z :=
    lintegral_congr_ae (hz2.mono fun y hy ↦ by simp only [hy])
  _ = ∫⁻ y, (Prod.mk y ⁻¹' t).indicator 1 z ∂condDistrib X T μ z :=
    lintegral_congr fun y ↦ Measure.dirac_apply' _ (ht.preimage (by fun_prop))
  _ = (condDistrib X T μ z) ((fun y ↦ (y, z)) ⁻¹' t) := by
    rw [← lintegral_indicator_one (ht.preimage (by fun_prop : Measurable fun y ↦ (y, z)))]
    exact lintegral_congr fun _ ↦ rfl
  _ = ((condDistrib X T μ ×ₖ Kernel.id) z) t := by
    rw [Kernel.prod_apply, Kernel.id_apply, Measure.prod_apply_symm ht, lintegral_dirac]

-- proved by Claude, then modified
lemma CondIndepFun.prod_right [StandardBorelSpace α] [StandardBorelSpace β] [Nonempty β]
    [StandardBorelSpace γ] [Nonempty γ] [StandardBorelSpace δ] [Nonempty δ]
    {X : α → β} {Y : α → γ} {Z : α → δ}
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (h : X ⟂ᵢ[Z, hZ; μ] Y) :
    X ⟂ᵢ[Z, hZ; μ] (fun ω ↦ (Y ω, Z ω)) := by
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight hY hX hZ,
    condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)] at h
  rw [condIndepFun_iff_condDistrib_prod_ae_eq_prodMkRight (by fun_prop) hX hZ,
    condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)]
  -- Key: condDistrib (Y, Z) Z μ z = (condDistrib Y Z μ z).map (y ↦ (y, z))
  have h_cond : condDistrib (fun ω ↦ (Y ω, Z ω)) Z μ =ᵐ[μ.map Z]
      fun z ↦ (condDistrib Y Z μ z).map (fun y ↦ (y, z)) := by
    suffices condDistrib (fun ω ↦ (Y ω, Z ω)) Z μ =ᵐ[μ.map Z]
        (condDistrib Y Z μ) ×ₖ Kernel.id by
      refine this.trans (ae_of_all _ fun x ↦ ?_)
      simp only
      rw [Kernel.prod_apply, Kernel.id_apply]
      ext s hs
      rw [Measure.map_apply (by fun_prop) hs, Measure.prod_apply_symm hs, lintegral_dirac]
    exact condDistrib_prod_self_left hY.aemeasurable hZ.aemeasurable
  -- Main calculation
  calc μ.map (fun x ↦ ((Z x, X x), (Y x, Z x)))
  _ = (μ.map (fun x ↦ ((Z x, X x), Y x))).map (fun p ↦ (p.1, (p.2, p.1.1))) := by
      rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
  _ = (μ.map (fun ω ↦ (Z ω, X ω)) ⊗ₘ (condDistrib Y Z μ).prodMkRight β).map
        (fun p ↦ (p.1, (p.2, p.1.1))) := by rw [h]
  _ = μ.map (fun ω ↦ (Z ω, X ω)) ⊗ₘ (condDistrib (fun ω ↦ (Y ω, Z ω)) Z μ).prodMkRight β := by
    ext s hs
    rw [Measure.map_apply (by fun_prop) hs,
      Measure.compProd_apply (hs.preimage (by fun_prop)), Measure.compProd_apply hs]
    have h_cond' : ∀ᵐ p ∂(μ.map (fun ω ↦ (Z ω, X ω))),
        condDistrib (fun ω ↦ (Y ω, Z ω)) Z μ p.1 =
          (condDistrib Y Z μ p.1).map (fun y ↦ (y, p.1)) := by
      have h_fst : (μ.map (fun ω ↦ (Z ω, X ω))).map Prod.fst = μ.map Z := by
        rw [Measure.map_map (by fun_prop) (by fun_prop)]; rfl
      rw [← h_fst] at h_cond
      exact mem_ae_of_mem_ae_map (by fun_prop) h_cond
    refine lintegral_congr_ae (h_cond'.mono fun ⟨z, x⟩ hzx ↦ ?_)
    simp only [Kernel.prodMkRight_apply, hzx,
      Measure.map_apply (by fun_prop : Measurable fun y ↦ (y, z))
        (hs.preimage (by fun_prop : Measurable (Prod.mk (z, x))))]
    congr 1

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
  le_add_self μ ν := fun s ↦ by simp
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
  rw [← Kernel.compProd_eq_iff, compProd_map_condDistrib (by fun_prop)] at h ⊢
  have : μ.map (fun a ↦ ((Z a, X a), Y a))
      = (μ.map (fun a ↦ ((X a, Z a), Y a))).map (fun p ↦ ((p.1.2, p.1.1), p.2)) := by
    rw [Measure.map_map (by fun_prop) (by fun_prop)]
    rfl
  rw [this, h]
  ext s hs
  rw [Measure.map_apply, Measure.compProd_apply, Measure.compProd_apply, lintegral_map,
    lintegral_map]
  · simp only [Kernel.prodMkLeft_apply, Kernel.prodMkRight_apply]
    congr
  · exact Kernel.measurable_kernel_prodMk_left hs
  · fun_prop
  · refine Kernel.measurable_kernel_prodMk_left ?_
    exact hs.preimage (by fun_prop)
  · fun_prop
  · exact hs
  · exact hs.preimage (by fun_prop)
  · fun_prop
  · exact hs

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

-- cf. measurableSet_graph (Mathlib/MeasureTheory/Measure/Lebesgue/Basic.lean)
lemma measurableSet_graph' {β Ω : Type*} [MeasurableSpace β] [MeasurableSpace Ω]
    [StandardBorelSpace Ω] {f : β → Ω} (hf : Measurable f) :
    MeasurableSet {p : β × Ω | p.2 = f p.1} := by
  letI := upgradeStandardBorel Ω
  exact (measurable_snd.prodMk (by fun_prop)) isClosed_diagonal.measurableSet

omit [Nonempty Ω] [IsFiniteMeasure μ] in
lemma ae_eq_of_map_prodMk_eq {f : β → Ω} (hf : Measurable f) (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (h : μ.map (fun ω ↦ (X ω, Y ω)) = μ.map (fun ω ↦ (X ω, f (X ω)))) :
    Y =ᵐ[μ] f ∘ X := by
  have hp : ∀ᵐ p ∂μ.map (fun ω ↦ (X ω, f (X ω))), p.2 = f p.1 :=
    (ae_map_iff (by fun_prop) (measurableSet_graph' hf)).2 (by simp)
  exact ae_of_ae_map (by fun_prop) (h ▸ hp)

lemma ae_eq_of_condDistrib_eq_deterministic {f : β → Ω} (hf : Measurable f) (hX : AEMeasurable X μ)
    (hY : AEMeasurable Y μ) (h : condDistrib Y X μ =ᵐ[μ.map X] Kernel.deterministic f hf) :
    Y =ᵐ[μ] f ∘ X := by
  have hfX := condDistrib_comp_self (μ := μ) X hf
  rw [condDistrib_ae_eq_iff_measure_eq_compProd _ (by fun_prop)] at h hfX
  exact ae_eq_of_map_prodMk_eq hf hX hY (hfX ▸ h)

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

lemma lintegral_cond {μ : Measure α} (s : Set α) (f : α → ℝ≥0∞) :
    ∫⁻ x, f x ∂μ[|s] = (μ s)⁻¹ * ∫⁻ (a : α) in s, f a ∂μ := by
  unfold cond
  simp [lintegral_smul_measure]

omit [Nonempty Ω'] in
lemma condDistrib_prod_of_forall_condDistrib_cond [Countable Ω'] [IsFiniteMeasure μ]
    (hX : Measurable X) (hY : Measurable Y) (hZ : Measurable Z)
    (κ : Kernel (β × Ω') Ω) [IsFiniteKernel κ]
    (h_cond : ∀ b, μ (Z ⁻¹' {b}) ≠ 0 → condDistrib Y X μ[|Z ⁻¹' {b}] =ᵐ[μ[|Z ⁻¹' {b}].map X]
      (κ.comap (fun ω ↦ (ω, b)) (by fun_prop))) :
    condDistrib Y (fun ω ↦ (X ω, Z ω)) μ =ᵐ[μ.map (fun ω ↦ (X ω, Z ω))] κ := by
  refine condDistrib_ae_eq_of_measure_eq_compProd _ (by fun_prop) ?_
  ext s hs
  suffices ∀ b, (Measure.map (fun x ↦ ((X x, Z x), Y x)) μ) (s ∩ {p | p.1.2 = b}) =
      (Measure.map (fun ω ↦ (X ω, Z ω)) μ ⊗ₘ κ) (s ∩ {p | p.1.2 = b}) by
    have hs_iUnion : s = ⋃ b, s ∩ {p | p.1.2 = b} := by
      ext p
      simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_setOf_eq]
      grind
    have h_disj : Pairwise (Function.onFun Disjoint fun b ↦ s ∩ {p | p.1.2 = b}) := by
      intro i j hij
      simp only [Set.disjoint_iff_inter_eq_empty]
      ext
      grind
    have h_meas (b : Ω') : MeasurableSet (s ∩ {p | p.1.2 = b}) :=
      hs.inter ((measurableSet_singleton _).preimage (by fun_prop))
    rw [hs_iUnion, measure_iUnion h_disj h_meas, measure_iUnion h_disj h_meas]
    congr with b
    exact this b
  intro b
  by_cases hb : μ (Z ⁻¹' {b}) = 0
  · have h_left : (Measure.map (fun x ↦ ((X x, Z x), Y x)) μ) (s ∩ {p | p.1.2 = b}) = 0 := by
      suffices (Measure.map (fun x ↦ ((X x, Z x), Y x)) μ) {p | p.1.2 = b} = 0 from
        measure_mono_null Set.inter_subset_right this
      rw [Measure.map_apply (by fun_prop)]
      · simpa
      · exact (measurableSet_singleton _).preimage (by fun_prop)
    have h_right : (Measure.map (fun ω ↦ (X ω, Z ω)) μ ⊗ₘ κ) (s ∩ {p | p.1.2 = b}) = 0 := by
      suffices (Measure.map (fun ω ↦ (X ω, Z ω)) μ ⊗ₘ κ) {p | p.1.2 = b} = 0 from
        measure_mono_null Set.inter_subset_right this
      rw [Measure.compProd_apply, lintegral_map]
      rotate_left
      · exact Kernel.measurable_kernel_prodMk_left
          ((measurableSet_singleton _).preimage (by fun_prop))
      · fun_prop
      · exact (measurableSet_singleton _).preimage (by fun_prop)
      simp only [Set.preimage_setOf_eq]
      classical
      have h_le : ∫⁻ a, (κ (X a, Z a)) {a_1 | Z a = b} ∂μ ≤
          ∫⁻ a, {a' | Z a' = b}.indicator (fun _ ↦ κ.bound) a ∂μ := by
        gcongr with a
        by_cases hZ : Z a = b
        · simp only [hZ, Set.setOf_true, Set.mem_setOf_eq, Set.indicator_of_mem]
          exact κ.measure_le_bound _ _
        · simp [hZ]
      refine le_antisymm (h_le.trans ?_) (zero_le _)
      rw [lintegral_indicator]
      swap; · exact (measurableSet_singleton _).preimage (by fun_prop)
      simp only [lintegral_const, MeasurableSet.univ, Measure.restrict_apply, Set.univ_inter,
        nonpos_iff_eq_zero, mul_eq_zero]
      exact .inr hb
    rw [h_left, h_right]
  specialize h_cond b hb
  rw [condDistrib_ae_eq_iff_measure_eq_compProd] at h_cond
  swap; · fun_prop
  rw [Measure.ext_iff] at h_cond
  have hs' : MeasurableSet {p : β × Ω | ((p.1, b), p.2) ∈ s} := hs.preimage (by fun_prop)
  have h1 := h_cond {p | ((p.1, b), p.2) ∈ s} hs'
  have h_indicator : Measurable ({ω' | Z ω' = b}.indicator (fun x ↦ 1)) :=
    Measurable.indicator (by fun_prop) ((measurableSet_singleton _).preimage (by fun_prop))
  rw [Measure.map_apply] at h1 ⊢
  rotate_left
  · fun_prop
  · exact hs.inter ((measurableSet_singleton _).preimage (by fun_prop))
  · fun_prop
  · exact hs'
  rw [cond_apply] at h1
  swap; · exact (measurableSet_singleton _).preimage (by fun_prop)
  have h1' : μ (Z ⁻¹' {b} ∩ (fun x ↦ (X x, Y x)) ⁻¹' {p | ((p.1, b), p.2) ∈ s}) =
      (μ (Z ⁻¹' {b})) *
        (Measure.map X μ[|Z ⁻¹' {b}] ⊗ₘ κ.comap (fun ω ↦ (ω, b)) (by fun_prop))
        {p | ((p.1, b), p.2) ∈ s} := by
    rw [← h1, ← mul_assoc, ENNReal.mul_inv_cancel hb (by simp), one_mul]
  convert h1'
  · ext x
    simp only [Set.preimage_inter, Set.preimage_setOf_eq, Set.mem_inter_iff, Set.mem_preimage,
      Set.mem_setOf_eq]
    grind
  · rw [Measure.compProd_apply, Measure.compProd_apply, lintegral_map, lintegral_map]
    rotate_left
    · exact Kernel.measurable_kernel_prodMk_left hs'
    · fun_prop
    · apply Kernel.measurable_kernel_prodMk_left
      exact hs.inter ((measurableSet_singleton _).preimage (by fun_prop))
    · fun_prop
    · exact hs'
    · exact hs.inter ((measurableSet_singleton _).preimage (by fun_prop))
    rw [lintegral_cond, ← mul_assoc, ENNReal.mul_inv_cancel hb (by simp), one_mul]
    simp only [Set.preimage_inter, Set.preimage_setOf_eq, Kernel.coe_comap, Function.comp_apply]
    classical
    have h_eq : (fun a ↦ κ (X a, Z a) (Prod.mk (X a, Z a) ⁻¹' s ∩ {a_1 | Z a = b})) =
        {a | Z a = b}.indicator
          (fun a ↦ κ (X a, b) (Prod.mk (X a, b) ⁻¹' s ∩ {a_1 | Z a = b})) := by
      ext a
      by_cases hZ : Z a = b <;> simp [hZ]
    simp_rw [h_eq]
    rw [lintegral_indicator]
    swap; · exact (measurableSet_singleton _).preimage (by fun_prop)
    refine setLIntegral_congr_fun ((measurableSet_singleton _).preimage (by fun_prop)) fun a ha ↦ ?_
    congr 1 with ω
    simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_setOf_eq, and_iff_left_iff_imp]
    grind

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
