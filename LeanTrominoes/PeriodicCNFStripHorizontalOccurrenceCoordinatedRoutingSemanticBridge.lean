/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFStripHorizontalOccurrenceCoordinatedRouteSemanticBridge
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonSourceRoutingProjection

/-! # Agreement with the certified coordinated source routing -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicCNFStripReduction

open PeriodicPlanarOneInThreeToThreeDM
open Gadget

attribute [local instance]
  horizontalRoutedRoutesSourceVariableDecidableEq
  horizontalRibbonRoutedVariableDecidableEq

theorem horizontalOccurrenceCoordinatedRouteComputed_eq_routing
    (source : PeriodicCNF Nat)
    (width :
      (horizontalSemanticNormalizedRibbonSource source).erase.WidthAtMost 3)
    (compatible : SourceRibbonFansClockwiseCompatible
      ((horizontalSemanticNormalizedRibbonReadyPresentation source)
        |>.toPlanarIncidencePresentation))
    (entry : ActiveOccurrenceEntry
      (horizontalSemanticNormalizedRibbonSource source).erase)
    (color : WireColor) :
    horizontalOccurrenceCoordinatedRouteComputed
        (((source, entry.1.1), entry.1.2), color) =
      (coordinatedSourceRibbonThreeStrandRouting
        (horizontalSemanticNormalizedRibbonReadyPresentation source)
        width compatible).route entry color := by
  rw [coordinatedSourceRibbonThreeStrandRouting_route_explicit]
  change horizontalOccurrenceCoordinatedRouteComputed
      (((source, entry.1.1), entry.1.2), color) =
    joinAtEndpoint
      (joinAtEndpoint
        (occurrenceCoordinatedRibbonVariableStub
          (horizontalSemanticNormalizedPlanarPresentation source)
          entry color)
        (occurrenceRibbonCorridorCore
          (horizontalSemanticNormalizedPlanarPresentation source)
          entry color))
      (occurrenceCoordinatedRibbonClauseStub
        (horizontalSemanticNormalizedPlanarPresentation source)
        entry color)
  exact horizontalOccurrenceCoordinatedRouteComputed_eq_semantic
    source entry color

end PeriodicCNFStripReduction
end LeanTrominoes
