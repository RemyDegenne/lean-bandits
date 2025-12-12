import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory Measure ProbabilityTheory Set

namespace MeasurableSpace

variable {δ : Type*} {X : δ → Type*} [m : ∀ a, MeasurableSpace (X a)] {α : Type*}

-- Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean after MeasurableSpace.pi
theorem comap_pi {g : α → ∀ a, X a} :
    MeasurableSpace.comap g MeasurableSpace.pi =
      ⨆ a, MeasurableSpace.comap (fun x ↦ g x a) (m a) := by
  simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

end MeasurableSpace

namespace ProbabilityTheory

variable {ι κ : Type*} {𝓧 : Type*} [MeasurableSpace 𝓧]
    {μ : ι → κ → Measure 𝓧} [∀ i j, IsProbabilityMeasure (μ i j)]

-- Mathlib/Probability/Independence/InfinitePi.lean after iIndepFun_uncurry_infinitePi'
lemma indepFun_proj_infinitePi_infinitePi {a b : κ} (hab : a ≠ b) :
    IndepFun (fun (ω : ι → κ → 𝓧) i ↦ ω i a)
             (fun (ω : ι → κ → 𝓧) i ↦ ω i b)
             (infinitePi (fun i ↦ infinitePi (μ i))) := by
  have hi : iIndepFun (fun (p : ι × κ) (ω : ι → κ → 𝓧) ↦ ω p.1 p.2)
      (infinitePi (fun i ↦ infinitePi (μ i))) :=
    iIndepFun_uncurry_infinitePi' (X := fun _ _ ↦ id) μ (by fun_prop)
  have hd : Disjoint (range fun i : ι ↦ (i, a)) (range fun i : ι ↦ (i, b)) := by
    simp [disjoint_iff_inter_eq_empty, eq_empty_iff_forall_notMem, hab.symm]
  simp_rw [IndepFun_iff_Indep, MeasurableSpace.comap_pi]
  convert indep_iSup_of_disjoint (fun _ ↦ Measurable.comap_le (by fun_prop)) hi hd
  all_goals rw [iSup_range]

end ProbabilityTheory
