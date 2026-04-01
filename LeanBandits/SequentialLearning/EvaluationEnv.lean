/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanBandits.SequentialLearning.Algorithm

/-!
# Function evaluation environments
-/

open MeasureTheory ProbabilityTheory

namespace Learning

variable {α R : Type*} [MeasurableSpace α] [MeasurableSpace R]

@[simps]
noncomputable def evalEnv {f : α → R} (hf : Measurable f) : Environment α R where
  ν0 := Kernel.deterministic f hf
  feedback _ := Kernel.deterministic (f ∘ Prod.snd) <| hf.comp measurable_snd

end Learning
