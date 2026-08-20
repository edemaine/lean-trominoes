/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceRibbonCorridorData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceClauseCoordinatedRouteLaneSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteSemanticBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonUnitRoutes

/-! # Semantic correctness of central occurrence ribbon corridors -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceRibbonCorridorCoreComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    horizontalOccurrenceRibbonCorridorCoreComputed
        (((source, entry.1.1), entry.1.2), color) =
      occurrenceRibbonCorridorCore
        (horizontalSemanticNormalizedPlanarPresentation source)
        entry color := by
  unfold horizontalOccurrenceRibbonCorridorCoreComputed
    horizontalOccurrenceRibbonCorridorInputComputed
    occurrenceRibbonCorridorCore
  rw [horizontalOccurrenceRibbonLaneComputed_eq_semantic,
    horizontalOccurrenceUnitSourceRouteComputed_eq_semantic]

end PeriodicCNFStripReduction
end LeanTrominoes
