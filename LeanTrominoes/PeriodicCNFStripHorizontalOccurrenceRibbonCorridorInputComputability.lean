/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRibbonCorridorData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteLaneComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteComputability

/-! # Computability of central occurrence corridor inputs -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceRibbonCorridorInputComputed_primrec :
    Primrec horizontalOccurrenceRibbonCorridorInputComputed := by
  exact Primrec.pair
    horizontalOccurrenceRibbonLaneComputed_primrec
    (horizontalOccurrenceUnitSourceRouteComputed_primrec.comp Primrec.fst)

end PeriodicCNFStripReduction
end LeanTrominoes
