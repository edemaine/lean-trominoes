/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableStubComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRibbonCorridorComputability
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseStubComputability
import LeanTrominoes.PeriodicThreeDMNormalizationGeometryComputability

/-! # Computability of complete coordinated occurrence routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableCorridorComputed_primrec :
    Primrec fun input : HorizontalOccurrenceColoredRouteInput =>
      joinAtEndpoint
        (horizontalOccurrenceVariableStubComputed input)
        (horizontalOccurrenceRibbonCorridorCoreComputed input) := by
  exact PeriodicThreeDM.NormalizationCompiler.joinAtEndpoint_primrec.comp
    horizontalOccurrenceVariableStubComputed_primrec
    horizontalOccurrenceRibbonCorridorCoreComputed_primrec

theorem horizontalOccurrenceCoordinatedRouteComputed_primrec :
    Primrec horizontalOccurrenceCoordinatedRouteComputed := by
  exact PeriodicThreeDM.NormalizationCompiler.joinAtEndpoint_primrec.comp
    horizontalOccurrenceVariableCorridorComputed_primrec
    horizontalOccurrenceClauseStubComputed_primrec

end PeriodicCNFStripReduction
end LeanTrominoes
