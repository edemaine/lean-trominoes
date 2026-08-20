/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableCoordinatedRouteInputComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMVariableRibbonRouteComputability

/-! # Computability of variable-side coordinated occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableCoordinatedRouteComputed_primrec :
    Primrec horizontalOccurrenceVariableCoordinatedRouteComputed := by
  exact variableRibbonCoordinatedRoute_primrec.comp
    horizontalOccurrenceVariableCoordinatedRouteInputComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
