/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableCoordinatedRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceVariableFanSemanticBridge

/-! # Semantic correctness of variable-side coordinated routes -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceVariableCoordinatedRouteComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    horizontalOccurrenceVariableCoordinatedRouteComputed
        (((source, entry.1.1), entry.1.2), color) =
      (sourceVariableRibbonFanData
        (horizontalSemanticNormalizedPlanarPresentation source)
        entry).coordinatedRoute
          (occurrenceVariableSiteSlot entry.1.2) color := by
  unfold horizontalOccurrenceVariableCoordinatedRouteComputed
    horizontalOccurrenceVariableCoordinatedRouteInputComputed
  rw [horizontalOccurrenceVariableRibbonFanDataComputed_eq_semantic]

end PeriodicCNFStripReduction
end LeanTrominoes
