import Mathlib.Probability.Kernel.IonescuTulcea.Traj
import Mathlib.Probability.Kernel.CondDistrib
import LeanBandits.ForMathlib.CondDistrib

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsFiniteMeasure P]
  {X : ℕ → Type*} [∀ n, MeasurableSpace (X n)]
  {κ : (n : ℕ) → Kernel (Π i : Iic n, X i) (X (n + 1))} [∀ n, IsMarkovKernel (κ n)]
  {μ₀ : Measure (X 0)} [IsProbabilityMeasure μ₀]

section MeasurableEquiv

lemma coe_default_Iic_zero : ((default : Iic 0) : ℕ) = 0 := rfl

end MeasurableEquiv

namespace ProbabilityTheory.Kernel

lemma traj_zero_map_eval_zero :
    (Kernel.traj κ 0).map (fun h ↦ h (default : Iic 0))
      = Kernel.deterministic (MeasurableEquiv.piUnique (fun i : Iic 0 ↦ X i))
        (MeasurableEquiv.piUnique _).measurable := by
  suffices (Kernel.traj κ 0).map (fun h ↦ h (default : Iic 0))
      = (Kernel.partialTraj κ 0 0).map (MeasurableEquiv.piUnique (fun i : Iic 0 ↦ X i)) by
    rwa [Kernel.partialTraj_zero, Kernel.deterministic_map] at this
    fun_prop
  rw [← Kernel.traj_map_frestrictLe, ← Kernel.map_comp_right _ (by fun_prop) (by fun_prop)]
  rfl

/-- Uniqueness of `trajMeasure`. -/
theorem eq_trajMeasure [∀ n, StandardBorelSpace (X n)] [∀ n, Nonempty (X n)]
    {Y : (n : ℕ) → Ω → X n} (hY_meas : ∀ n, Measurable (Y n))
    (h0 : P.map (Y 0) = μ₀)
    (h_condDistrib : ∀ n,
      condDistrib (Y (n + 1)) (fun ω ↦ fun i : Iic n ↦ Y i ω) P
        =ᵐ[P.map (fun ω ↦ fun i : Iic n ↦ Y i ω)] κ n) :
    P.map (fun ω n ↦ Y n ω) = trajMeasure μ₀ κ := by
  sorry

end ProbabilityTheory.Kernel
