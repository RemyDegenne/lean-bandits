import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory Measure ProbabilityTheory Set

namespace MeasurableSpace

variable {δ : Type*} {X : δ → Type*} [m : ∀ a, MeasurableSpace (X a)] {α : Type*}

-- Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean
theorem comap_pi {g : α → ∀ a, X a} :
    MeasurableSpace.comap g MeasurableSpace.pi =
      ⨆ a, MeasurableSpace.comap (fun x ↦ g x a) (m a) := by
  simp_rw [MeasurableSpace.pi, MeasurableSpace.comap_iSup, MeasurableSpace.comap_comp]
  rfl

end MeasurableSpace

namespace ProbabilityTheory

variable {ι κ : Type*} {𝓧 : ι → κ → Type*} [m𝓧 : ∀ i j, MeasurableSpace (𝓧 i j)]
    {μ : (i : ι) → (j : κ) → Measure (𝓧 i j)} [∀ i j, IsProbabilityMeasure (μ i j)]

-- Mathlib/Probability/Independence/InfinitePi.lean
lemma indep_iSup_infinitePi_infinitePi {S T : Set (ι × κ)} (hd : Disjoint S T) :
    Indep (⨆ p ∈ S, MeasurableSpace.comap (fun ω ↦ ω p.1 p.2) (m𝓧 p.1 p.2))
          (⨆ p ∈ T, MeasurableSpace.comap (fun ω ↦ ω p.1 p.2) (m𝓧 p.1 p.2))
          (infinitePi (fun i ↦ infinitePi (μ i))) :=
  indep_iSup_of_disjoint (fun _ ↦ Measurable.comap_le (by fun_prop))
    (iIndepFun_uncurry_infinitePi' (X := fun _ _ ↦ id) μ (by fun_prop)) hd

-- Mathlib/Probability/Independence/InfinitePi.lean
lemma indepFun_proj_infinitePi_infinitePi {a b : κ} (h : a ≠ b) :
    IndepFun (fun ω i ↦ ω i a) (fun ω i ↦ ω i b)
        (infinitePi (fun i ↦ infinitePi (μ i))) := by
  have hd : Disjoint (Set.range fun i : ι ↦ (i, a)) (Set.range fun i ↦ (i, b)) := by
    simp [Set.disjoint_iff_inter_eq_empty, Set.eq_empty_iff_forall_notMem, h.symm]
  simp_rw [IndepFun_iff_Indep, MeasurableSpace.comap_pi]
  convert indep_iSup_infinitePi_infinitePi (μ := μ) hd
  all_goals rw [iSup_range]

end ProbabilityTheory
