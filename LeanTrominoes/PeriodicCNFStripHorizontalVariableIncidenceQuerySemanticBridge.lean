/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalAssembledRouteData
import LeanTrominoes.PeriodicCNFStripHorizontalNormalizedRibbonEraseBridge
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRoutingSemanticBridge

/-! # Semantic bridge for horizontal variable-incidence queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalRoutedOccurrenceTripleQueryComputed_eq_semantic
    (source : PeriodicCNF Nat)
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (triple : Triple RoutedVariable)
    (color : WireColor) :
    horizontalRoutedOccurrenceTripleQueryComputed
        ((((source, entry.1.1), entry.1.2), triple), color) =
      routedOccurrenceTriple
        (horizontalSemanticNormalizedRibbonSource source).erase
        entry.1.1 entry.1.2 color := by
  unfold horizontalRoutedOccurrenceTripleQueryComputed
    horizontalRoutedOccurrenceTripleInputComputed
    horizontalVariableTypedIncidenceNormalizedSourceComputed
    horizontalVariableTypedIncidenceSourceAtomComputed
    horizontalVariableTypedIncidenceMetadataComputed
  rw [horizontalNormalizedRoutedEraseComputed_eq_semanticData]

theorem horizontalVariableOccurrenceRouteComputed_eq_routing
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation))
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (triple : Triple RoutedVariable)
    (color : WireColor) :
    horizontalOccurrenceCoordinatedRouteComputed
        (horizontalVariableOccurrenceRouteQueryComputed
          ((((source, entry.1.1), entry.1.2), triple), color)) =
      (coordinatedSourceRibbonThreeStrandRouting
        (horizontalSemanticNormalizedRibbonReadyPresentation source)
        width compatible).route entry color := by
  unfold horizontalVariableOccurrenceRouteQueryComputed
    horizontalVariableTypedIncidenceMetadataComputed
  exact horizontalOccurrenceCoordinatedRouteComputed_eq_routing
    source width compatible entry color

end PeriodicCNFStripReduction
end LeanTrominoes
