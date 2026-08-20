/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PlanarThreeDMVariableConnectorBoundary
import Mathlib.Tactic.FinCases

noncomputable section

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open PlanarThreeDM

def variableConnectorKindEquivFin : VariableConnectorKind ≃ Fin 3 where
  toFun
    | .fixedRed => 0
    | .fixedGreen => 1
    | .fixedBlue => 2
  invFun value :=
    match value.1 with
    | 0 => .fixedRed
    | 1 => .fixedGreen
    | _ => .fixedBlue
  left_inv value := by cases value <;> rfl
  right_inv value := by fin_cases value <;> rfl

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
