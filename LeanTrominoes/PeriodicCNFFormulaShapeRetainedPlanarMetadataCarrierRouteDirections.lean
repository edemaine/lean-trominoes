/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierDescriptorBlocks
import LeanTrominoes.PeriodicOrthocrossingRetainedCarrierBoundingBox
import LeanTrominoes.OrthogonalPolylineEndpointDirections

/-! # First directions of retained carrier-lens routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The first compass direction of a route in an east- or north-facing
equality lens.  Every selected retained carrier link has one of these two
orientations. -/
def carrierLensRouteFirstDirection
    (horizontal : Bool) : Nat → Nat → AxisDirection
  | 0, 0 => if horizontal then .west else .south
  | 0, 1 => if horizontal then .south else .east
  | 1, 0 => if horizontal then .north else .west
  | 1, 1 => if horizontal then .east else .north
  | _, _ => .invalid

/-- The local retained carrier drawing has the fixed equality-lens first
directions determined solely by whether its physical carrier is horizontal. -/
theorem carrier_routeFirstDirection_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (link : EqualityLink CarrierNode)
    (linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks source.incidenceGraph)
    (localClauseIndex literalIndex : Nat) :
    AxisDirection.polylineFirstDirection
        (((DrawingPlanarSATClauseSource.carrier
            link localClauseIndex).incidenceDrawing source).routes
          localClauseIndex literalIndex) =
      carrierLensRouteFirstDirection link.first.isHorizontal
        localClauseIndex literalIndex := by
  have direction :=
    retainedDrawingCompleteCarrierLink_carrierDirection_eq_axis
      wellFormed degree isLocal linkMember
  have spanSix :
      6 < AxisDirection.axisSpan
        (CarrierNode.position source.incidenceGraph link.first)
        (CarrierNode.position source.incidenceGraph link.second) := by
    have spanLarge :=
      (retainedDrawingCompleteCarrierLink_lensGeometry
        wellFormed degree isLocal linkMember).spanLarge
    omega
  unfold DrawingPlanarSATClauseSource.incidenceDrawing
    drawingPlanarSATCarrierLensIncidenceDrawing
    EqualityLink.lensDrawing at ⊢
  change AxisDirection.polylineFirstDirection
      ((placedEqualityLensDrawing link.first link.second
        (CarrierNode.position source.incidenceGraph link.first)
        (AxisDirection.between
          (CarrierNode.position source.incidenceGraph link.first)
          (CarrierNode.position source.incidenceGraph link.second))
        (AxisDirection.axisSpan
          (CarrierNode.position source.incidenceGraph link.first)
          (CarrierNode.position source.incidenceGraph link.second))).routes
        localClauseIndex literalIndex) = _
  change AxisDirection.between
      (CarrierNode.position source.incidenceGraph link.first)
      (CarrierNode.position source.incidenceGraph link.second) = _ at direction
  rw [direction]
  by_cases horizontal : link.first.isHorizontal = true
  all_goals
    rcases localClauseIndex with (_ | _ | localClauseIndex) <;>
      rcases literalIndex with (_ | _ | literalIndex) <;>
      simp [horizontal, spanSix, carrierLensRouteFirstDirection,
        placedEqualityLensDrawing,
        EmbeddedCNFIncidenceDrawing.renameToImage,
        EmbeddedCNFIncidenceDrawing.rename,
        axisEqualityLensDrawing,
        EmbeddedCNFIncidenceDrawing.placeOnAxis,
        EmbeddedCNFIncidenceDrawing.orient,
        EmbeddedCNFIncidenceDrawing.mapPoints,
        EmbeddedCNFIncidenceDrawing.translate,
        horizontalEqualityLensDrawing,
        horizontalEqualityLensRoutes,
        horizontalEqualityLensUpperLeftRoute,
        horizontalEqualityLensUpperRightRoute,
        horizontalEqualityLensLowerLeftRoute,
        horizontalEqualityLensLowerRightRoute,
        AxisDirection.polylineFirstDirection,
        AxisDirection.orientPoint, AxisDirection.between, Cell.add] <;>
      omega

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
