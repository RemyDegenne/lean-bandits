import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.CondDistrib
import LeanBandits.ForMathlib.CondDistrib
import LeanBandits.ForMathlib.KernelCompositionLemmas

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory

variable {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
variable {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]
variable {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]

section MeasurableEquiv

instance : Unique (Iic 0) := by simp only [mem_Iic, nonpos_iff_eq_zero]; exact Unique.subtypeEq 0

lemma coe_default_Iic_zero : ((default : Iic 0) : ℕ) = 0 := by
  calc _ = ((⟨0, by simp⟩ : Iic 0) : ℕ) := by congr; exact (Unique.eq_default _).symm
    _ = _ := by simp

/-- Measurable equivalence between `Iic 0 → X i` and `X 0`. -/
def MeasurableEquiv.piIicZero (X : ℕ → Type*) [∀ n, MeasurableSpace (X n)] :
    ((i : Iic 0) → X i) ≃ᵐ X 0 :=
  (MeasurableEquiv.piUnique _).trans (coe_default_Iic_zero.symm ▸ MeasurableEquiv.refl _)

end MeasurableEquiv

namespace ProbabilityTheory.Kernel

-- Probability/Kernel/IonescuTulcea/Traj.lean
/-- Distribution of the infinite trajectory given the distribution of `X 0`. -/
noncomputable
def trajMeasure (μ₀ : Measure (X 0)) (κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1)))
    [∀ n, IsMarkovKernel (κ n)] :
    Measure (Π n, X n) :=
  (traj κ 0) ∘ₘ (μ₀.map (MeasurableEquiv.piIicZero _).symm)

-- Probability/Kernel/IonescuTulcea/Traj.lean
instance : IsProbabilityMeasure (trajMeasure μ₀ κ) := by
  rw [trajMeasure]
  have : IsProbabilityMeasure (μ₀.map (MeasurableEquiv.piIicZero _).symm) :=
    isProbabilityMeasure_map <| by fun_prop
  infer_instance

-- Probability/Kernel/IonescuTulcea/Traj.lean
lemma traj_map_eq_kernel {a : ℕ} : (traj κ a).map (fun x ↦ x (a + 1)) = κ a := by
  set f : (Π n, X n) → X (a + 1) := fun x ↦ x (a + 1)
  set g : (Π n : Iic (a + 1), X n) → X (a + 1) := fun x ↦ x ⟨a + 1, by simp⟩
  have hf : f = g ∘ (frestrictLe (a + 1)) := by rfl
  have hp : g ∘ IicProdIoc a (a + 1) = (piSingleton a).symm ∘ Prod.snd := by
    ext
    simp [g, _root_.IicProdIoc, piSingleton]
  rw [hf, map_comp_right, traj_map_frestrictLe, partialTraj_succ_self, ← map_comp_right, hp,
   map_comp_right, ← snd_eq, snd_prod, ← map_comp_right]
  all_goals measurability

-- Probability/Kernel/IonescuTulcea/Traj.lean
lemma partialTraj_compProd_kernel_eq_traj_map {a : ℕ} {x₀ : Π n : Iic 0, X n} :
    (partialTraj κ 0 a x₀) ⊗ₘ (κ a) = (traj κ 0 x₀).map (fun x ↦ (frestrictLe a x, x (a + 1))) := by
  set f := fun x ↦ (frestrictLe a x, x (a + 1))
  set g := fun x ↦ (frestrictLe a x, x)
  have hf : f = (Prod.map id (fun x ↦ x (a + 1))) ∘ g := rfl
  rw [hf, ← Measure.map_map, ← partialTraj_compProd_traj, ← MeasureTheory.Measure.compProd_map,
    traj_map_eq_kernel]
  all_goals measurability

-- (Extract kernel lemmas from rewrites?) Probability/Kernel/IonescuTulcea/Traj.lean
lemma trajMeasure_map_frestrictLe_compProd_kernel_eq_trajMeasure_map {a : ℕ} :
    (trajMeasure μ₀ κ).map (frestrictLe a) ⊗ₘ κ a =
      (trajMeasure μ₀ κ).map (fun x ↦ (frestrictLe a x, x (a + 1))) := by
  rw [Measure.compProd_eq_comp_prod, trajMeasure, Measure.map_comp, traj_map_frestrictLe,
    Measure.comp_assoc, Measure.map_comp]
  any_goals fun_prop
  congr
  ext1 x₀
  rw [comp_apply, ← Measure.compProd_eq_comp_prod, map_apply,
    partialTraj_compProd_kernel_eq_traj_map]
  fun_prop

-- Probability/Kernel/IonescuTulcea/Traj.lean
lemma condDistrib_trajMeasure_ae_eq_kernel {a : ℕ}
    [StandardBorelSpace (X (a + 1))] [Nonempty (X (a + 1))] :
    condDistrib (fun x ↦ x (a + 1)) (frestrictLe a) (trajMeasure μ₀ κ)
      =ᵐ[(trajMeasure μ₀ κ).map (frestrictLe a)] κ a := by
  apply condDistrib_ae_eq_of_measure_eq_compProd₀ (by measurability) (by measurability)
  exact trajMeasure_map_frestrictLe_compProd_kernel_eq_trajMeasure_map.symm

end ProbabilityTheory.Kernel
