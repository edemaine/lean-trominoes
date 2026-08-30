/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRouteDirections
import LeanTrominoes.RetainedAngularFanCarrierLensTemplateFallbackKind

/-! # Fallback policies of retained carrier-lens routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicEightOccurrenceSplit

/-- The two straight routes in a retained carrier lens have singleton
deleted-final-point prefixes, while its two routed incidences do not. -/
theorem carrier_route_singletonPrefix_iff
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (localClauseIndex literalIndex : Nat) :
    ((((DrawingPlanarSATClauseSource.carrier
            link localClauseIndex).incidenceDrawing source).routes
          localClauseIndex literalIndex).dropLast.length = 1) ↔
      (localClauseIndex = 0 ∧ literalIndex = 0) ∨
      (localClauseIndex = 1 ∧ literalIndex = 1) := by
  let span := AxisDirection.axisSpan
    (CarrierNode.position source.incidenceGraph link.first)
    (CarrierNode.position source.incidenceGraph link.second)
  have routeLength :
      (((DrawingPlanarSATClauseSource.carrier
            link localClauseIndex).incidenceDrawing source).routes
          localClauseIndex literalIndex).length =
        (horizontalEqualityLensRoutes span
          localClauseIndex literalIndex).length := by
    unfold DrawingPlanarSATClauseSource.incidenceDrawing
      drawingPlanarSATCarrierLensIncidenceDrawing
      EqualityLink.lensDrawing
    change
      ((placedEqualityLensDrawing link.first link.second
        (CarrierNode.position source.incidenceGraph link.first)
        (AxisDirection.between
          (CarrierNode.position source.incidenceGraph link.first)
          (CarrierNode.position source.incidenceGraph link.second))
        span).routes localClauseIndex literalIndex).length = _
    simp [placedEqualityLensDrawing,
      EmbeddedCNFIncidenceDrawing.renameToImage,
      EmbeddedCNFIncidenceDrawing.rename,
      axisEqualityLensDrawing,
      EmbeddedCNFIncidenceDrawing.placeOnAxis,
      EmbeddedCNFIncidenceDrawing.orient,
      EmbeddedCNFIncidenceDrawing.mapPoints,
      EmbeddedCNFIncidenceDrawing.translate,
      horizontalEqualityLensDrawing]
  have dropLastLength :
      (((DrawingPlanarSATClauseSource.carrier
            link localClauseIndex).incidenceDrawing source).routes
          localClauseIndex literalIndex).dropLast.length =
        (horizontalEqualityLensRoutes span
          localClauseIndex literalIndex).dropLast.length := by
    simpa only [List.length_dropLast] using
      congrArg (fun length => length - 1) routeLength
  rw [dropLastLength]
  exact horizontalEqualityLensRoute_singletonPrefix_iff
    span localClauseIndex literalIndex

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
