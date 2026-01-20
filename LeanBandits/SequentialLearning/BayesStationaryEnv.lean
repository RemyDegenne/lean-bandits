/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.SequentialLearning.IonescuTulceaSpace

open MeasureTheory ProbabilityTheory Finset

namespace Learning.Bayes

variable {α R E : Type*} [mα : MeasurableSpace α] [mR : MeasurableSpace R] [mE : MeasurableSpace E]
variable (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R) [IsMarkovKernel κ]

noncomputable
def StationaryEnv : Environment α (E × R) where
  feedback n :=
    let g : (Iic n → α × E × R) × α → α × E := fun (h, a) => (a, (h ⟨0, by simp⟩).2.1)
    (Kernel.deterministic (Prod.snd ∘ g) (by fun_prop)) ×ₖ (κ.comap g (by fun_prop))
  h_feedback := inferInstance
  ν0 := (Kernel.const α Q) ⊗ₖ κ
  hp0 := Kernel.IsMarkovKernel.compProd _ _

noncomputable
def trajMeasure (alg : Algorithm α R) :=
  Learning.trajMeasure (alg.prod_left E) (StationaryEnv Q κ)

instance (alg : Algorithm α R) : IsProbabilityMeasure (trajMeasure Q κ alg) := by
  unfold trajMeasure
  infer_instance

def action (n : ℕ) (ω : ℕ → α × E × R) : α := (ω n).1

def reward (n : ℕ) (ω : ℕ → α × E × R) : R := (ω n).2.2

def hist (n : ℕ) (ω : ℕ → α × E × R) : Iic n → α × R :=  fun i ↦ (action i ω, reward i ω)

def env (ω : ℕ → α × E × R) : E := (ω 0).2.1

noncomputable
def posterior [StandardBorelSpace E] [Nonempty E] (n : ℕ) (alg : Algorithm α R) :
    Kernel (Iic n → α × R) E :=
  condDistrib env (hist n) (trajMeasure Q κ alg)

instance [StandardBorelSpace E] [Nonempty E] (n : ℕ) (alg : Algorithm α R) :
    IsMarkovKernel (posterior Q κ n alg) := by
  unfold posterior
  infer_instance

lemma isAlgEnvSeq_trajMeasure
    [StandardBorelSpace α] [Nonempty α] [StandardBorelSpace R] [Nonempty R] [StandardBorelSpace E]
    [Nonempty E] (alg : Algorithm α R) :
    IsAlgEnvSeq action IT.reward (alg.prod_left E) (StationaryEnv Q κ) (trajMeasure Q κ alg) :=
  IT.isAlgEnvSeq_trajMeasure _ _

end Learning.Bayes
