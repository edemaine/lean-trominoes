/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceSourceRouteSemanticBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceUnitRouteData
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonEndpointDirections

/-! # Semantic correctness of horizontal occurrence-route preprocessing -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Executable unit subdivision is exactly the semantic unit source route. -/
theorem horizontalOccurrenceUnitSourceRouteComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase) :
    horizontalOccurrenceUnitSourceRouteComputed
        ((source, entry.1.1), entry.1.2) =
      occurrenceUnitSourceRoute
        (horizontalSemanticNormalizedPlanarPresentation source)
        entry := by
  unfold horizontalOccurrenceUnitSourceRouteComputed
    occurrenceUnitSourceRoute
  rw [horizontalOccurrenceSourceRouteComputed_eq_semantic]

/-- The executable first direction is the semantic variable direction. -/
theorem horizontalOccurrenceSourceVariableDirectionComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase) :
    horizontalOccurrenceSourceVariableDirectionComputed
        ((source, entry.1.1), entry.1.2) =
      occurrenceSourceVariableDirection
        (horizontalSemanticNormalizedPlanarPresentation source)
        entry := by
  unfold horizontalOccurrenceSourceVariableDirectionComputed
    occurrenceSourceVariableDirection
  rw [horizontalOccurrenceUnitSourceRouteComputed_eq_semantic]

/-- The executable final direction is the semantic clause direction. -/
theorem horizontalOccurrenceSourceClauseDirectionComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase) :
    horizontalOccurrenceSourceClauseDirectionComputed
        ((source, entry.1.1), entry.1.2) =
      occurrenceSourceClauseDirection
        (horizontalSemanticNormalizedPlanarPresentation source)
        entry := by
  unfold horizontalOccurrenceSourceClauseDirectionComputed
    occurrenceSourceClauseDirection
  rw [horizontalOccurrenceUnitSourceRouteComputed_eq_semantic]

end PeriodicCNFStripReduction
end LeanTrominoes
