/-
Copyright (c) 2025 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.SequentialLearning.IonescuTulceaSpace

open MeasureTheory ProbabilityTheory Finset
open Learning

variable {α R E : Type*} [mα : MeasurableSpace α] [mR : MeasurableSpace R] [mE : MeasurableSpace E]

noncomputable
def bayesStationaryEnv (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R)
    [IsMarkovKernel κ] : Environment α (E × R) where
  feedback n :=
    let g : (Iic n → α × (E × R)) × α → (α × E) := fun (h, a) => (a, (h ⟨0, by simp⟩).2.1)
    (Kernel.deterministic (Prod.snd ∘ g) (by fun_prop)) ×ₖ (κ.comap g (by fun_prop))
  h_feedback := inferInstance
  ν0 := (Kernel.const α Q) ⊗ₖ κ
  hp0 := Kernel.IsMarkovKernel.compProd _ _

noncomputable
def bayesTrajMeasure (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R)
    [IsMarkovKernel κ] (alg : Algorithm α R) :=
  trajMeasure (alg.prod_left E) (bayesStationaryEnv Q κ)

instance isProbabilityMeasure_bayesTrajMeasure (Q : Measure E) [IsProbabilityMeasure Q]
    (κ : Kernel (α × E) R) [IsMarkovKernel κ] (alg : Algorithm α R) :
    IsProbabilityMeasure (bayesTrajMeasure Q κ alg) := by
  unfold bayesTrajMeasure
  infer_instance

lemma isAlgEnvSeq_bayesTrajMeasure (Q : Measure E) [IsProbabilityMeasure Q] (κ : Kernel (α × E) R)
    [IsMarkovKernel κ] [StandardBorelSpace α] [Nonempty α]
    [StandardBorelSpace R] [StandardBorelSpace E] [Nonempty E] [Nonempty R] (alg : Algorithm α R) :
    IsAlgEnvSeq IT.action IT.reward (alg.prod_left E) (bayesStationaryEnv Q κ)
    (bayesTrajMeasure Q κ alg) :=
  IT.isAlgEnvSeq_trajMeasure (alg.prod_left E) (bayesStationaryEnv Q κ)

namespace POTraj

variable {α R E : Type*}

def action (n : ℕ) (ω : ℕ → α × (E × R)) : α := (ω n).1

def reward (n : ℕ) (ω : ℕ → α × (E × R)) : R := (ω n).2.2

def hist (n : ℕ) (ω : ℕ → α × (E × R)) : Iic n → α × R :=
  fun i ↦ (action i ω, reward i ω)

def latent (n : ℕ) (ω : ℕ → α × (E × R)) : E := (ω n).2.1

end POTraj
