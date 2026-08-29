/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedRouteJoinTapes

/-! # Shared execution support for delimited-route joining -/

namespace LeanTrominoes.DelimitedRouteJoin

open StateTransition Turing

def oneStep {before after : machine.Cfg}
    (step : machine.step before = some after) :
    EvalsToInTime machine.step before (some after) 1 where
  steps := 1
  evals_in_steps := by
    simp only [Function.iterate_one]
    exact step
  steps_le_m := Nat.le_refl 1

end LeanTrominoes.DelimitedRouteJoin
