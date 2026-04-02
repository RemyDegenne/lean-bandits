/-
Copyright (c) 2026 Gaëtan Serré. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gaëtan Serré
-/

import LeanBandits.SequentialLearning.StationaryEnv

/-!
# Function evaluation environments
-/

open MeasureTheory ProbabilityTheory

namespace Learning

variable {α R : Type*} [MeasurableSpace α] [MeasurableSpace R]

noncomputable def evalEnv {f : α → R} (hf : Measurable f) :=
  stationaryEnv <| Kernel.deterministic f hf

end Learning
