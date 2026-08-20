/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticOccurrenceRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticPlanarPresentationRoutes
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMOccurrenceSourceRouteCorrectness

/-! # Correctness of semantic horizontal occurrence-route data -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- On an active entry, the proof-free semantic data route is the
choice-backed route used by the ribbon construction. -/
theorem horizontalSemanticOccurrenceSourceRouteData_eq
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase) :
    horizontalSemanticOccurrenceSourceRouteData
        ((source, entry.1.1), entry.1.2) =
      occurrenceSourceRoute
        (horizontalSemanticNormalizedPlanarPresentation source)
        entry := by
  unfold horizontalSemanticOccurrenceSourceRouteData
  rw [← horizontalSemanticNormalizedPlanarPresentation_routes]
  exact occurrenceSourceRouteFromData_eq
    (horizontalSemanticNormalizedPlanarPresentation source)
    entry

end PeriodicCNFStripReduction
end LeanTrominoes
