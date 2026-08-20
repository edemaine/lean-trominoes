/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteInputComputability
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMClauseRibbonRouteComputability

/-! # Computability of clause-side coordinated occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceClauseCoordinatedRouteComputed_primrec :
    Primrec horizontalOccurrenceClauseCoordinatedRouteComputed := by
  exact clauseRibbonCoordinatedRoute_primrec.comp
    horizontalOccurrenceClauseCoordinatedRouteInputComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
