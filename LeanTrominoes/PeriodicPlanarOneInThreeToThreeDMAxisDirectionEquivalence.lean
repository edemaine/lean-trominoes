/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineRibbon
import Mathlib.Tactic.FinCases

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

def axisDirectionEquivFin : AxisDirection ≃ Fin 5 where
  toFun
    | .east => 0
    | .north => 1
    | .west => 2
    | .south => 3
    | .invalid => 4
  invFun value :=
    match value.1 with
    | 0 => .east
    | 1 => .north
    | 2 => .west
    | 3 => .south
    | _ => .invalid
  left_inv value := by cases value <;> rfl
  right_inv value := by fin_cases value <;> rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
