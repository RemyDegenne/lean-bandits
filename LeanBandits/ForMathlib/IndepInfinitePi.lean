import Mathlib.Probability.Independence.InfinitePi

open MeasureTheory Measure ProbabilityTheory Set Function

namespace MeasurableSpace

variable {δ : Type*} {X : δ → Type*} [m : ∀ a, MeasurableSpace (X a)] {α : Type*}

-- Mathlib/MeasureTheory/MeasurableSpace/Constructions.lean
theorem comap_pi {g : α → ∀ a, X a} : pi.comap g = ⨆ a, (m a).comap (fun x ↦ g x a) := by
  simp_rw [pi, comap_iSup, comap_comp, comp_def]

end MeasurableSpace

namespace ProbabilityTheory

variable {ι κ : Type*} {𝓧 : ι → κ → Type*} [m𝓧 : ∀ i j, MeasurableSpace (𝓧 i j)]
    {μ : (i : ι) → (j : κ) → Measure (𝓧 i j)} [∀ i j, IsProbabilityMeasure (μ i j)]

-- Mathlib/Probability/Independence/InfinitePi.lean
lemma indepFun_proj_infinitePi_infinitePi {a b : κ} (h : a ≠ b) :
    IndepFun (fun ω i ↦ ω i a) (fun ω i ↦ ω i b) (infinitePi (fun i ↦ infinitePi (μ i))) := by
  simp_rw [IndepFun_iff_Indep, MeasurableSpace.comap_pi]
  have hd : Disjoint (range fun i : ι ↦ (i, a)) (range fun i ↦ (i, b)) := by
    simp [disjoint_range_iff, h]
  convert indep_iSup_of_disjoint (fun _ ↦ Measurable.comap_le (by fun_prop))
    (iIndepFun_uncurry_infinitePi' (X := fun _ _ x ↦ x) μ (by fun_prop)) hd
  all_goals rw [iSup_range]

end ProbabilityTheory
