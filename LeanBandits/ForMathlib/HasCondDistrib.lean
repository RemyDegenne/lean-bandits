/-
Copyright (c) 2026 Rémy Degenne. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rémy Degenne, Paulo Rauber
-/
import LeanBandits.ForMathlib.CondDistrib

/-!
# A predicate for having a specified conditional distribution
-/

open MeasureTheory

namespace ProbabilityTheory

variable {α β Ω : Type*} {mα : MeasurableSpace α} {mβ : MeasurableSpace β}
  {mΩ : MeasurableSpace Ω} [StandardBorelSpace Ω] [Nonempty Ω]
  {μ : Measure α} {X : α → β} {Y : α → Ω} {κ : Kernel β Ω}

structure HasCondDistrib (Y : α → Ω) (X : α → β) (κ : Kernel β Ω)
  (μ : Measure α) [IsFiniteMeasure μ] : Prop where
  aemeasurable_fst : AEMeasurable Y μ
  aemeasurable_snd : AEMeasurable X μ
  condDistrib_eq : condDistrib Y X μ =ᵐ[μ.map X] κ

end ProbabilityTheory
