/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticOccurrenceRouteDataBridge
import LeanTrominoes.PeriodicCNFStripHorizontalSemanticOccurrenceRouteCorrectness

/-! # Semantic correctness of horizontal occurrence source routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

/-- Every active horizontal occurrence gets exactly the choice-backed source
route used by the final coordinated ribbon presentation. -/
theorem horizontalOccurrenceSourceRouteComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase) :
    horizontalOccurrenceSourceRouteComputed
        ((source, entry.1.1), entry.1.2) =
      occurrenceSourceRoute
        (horizontalSemanticNormalizedPlanarPresentation source)
        entry := by
  exact (horizontalOccurrenceSourceRouteComputed_eq_semanticData
      ((source, entry.1.1), entry.1.2)).trans
    (horizontalSemanticOccurrenceSourceRouteData_eq source entry)

end PeriodicCNFStripReduction
end LeanTrominoes
