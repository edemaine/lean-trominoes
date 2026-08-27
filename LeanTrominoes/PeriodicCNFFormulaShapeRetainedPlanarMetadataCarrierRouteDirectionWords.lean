/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRouteDirections
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionTranslation

/-! # Complete direction words of retained carrier-lens routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The complete unit-step direction word of one route in an east- or
north-facing equality lens.  The only unbounded datum is the unary carrier
span. -/
def carrierLensRouteDirections
    (horizontal : Bool) (span : Int) : Nat → Nat → List AxisDirection
  | 0, 0 =>
      List.replicate 3 (if horizontal then .west else .south)
  | 0, 1 =>
      List.replicate 2 (if horizontal then .south else .east) ++
        List.replicate (span - 3).natAbs
          (if horizontal then .east else .north) ++
        List.replicate 2 (if horizontal then .north else .west)
  | 1, 0 =>
      [if horizontal then .north else .west] ++
        List.replicate 6 (if horizontal then .west else .south) ++
        [if horizontal then .south else .east]
  | 1, 1 =>
      List.replicate (span - 6).natAbs
        (if horizontal then .east else .north)
  | _, _ => []

/-- The local retained carrier drawing has exactly the explicit complete
direction words above.  Translation disappears, and the carrier-axis bit
selects either the east-facing template or its north-facing quarter turn. -/
theorem carrier_routeDirections_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (link : EqualityLink CarrierNode)
    (linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks source.incidenceGraph)
    (localClauseIndex literalIndex : Nat) :
    Gadget.unitSubdivisionDirections
        (((DrawingPlanarSATClauseSource.carrier
            link localClauseIndex).incidenceDrawing source).routes
          localClauseIndex literalIndex) =
      carrierLensRouteDirections link.first.isHorizontal
        (AxisDirection.axisSpan
          (CarrierNode.position source.incidenceGraph link.first)
          (CarrierNode.position source.incidenceGraph link.second))
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
  have spanThree :
      3 < AxisDirection.axisSpan
        (CarrierNode.position source.incidenceGraph link.first)
        (CarrierNode.position source.incidenceGraph link.second) := by
    omega
  unfold DrawingPlanarSATClauseSource.incidenceDrawing
    drawingPlanarSATCarrierLensIncidenceDrawing
    EqualityLink.lensDrawing at ⊢
  change Gadget.unitSubdivisionDirections
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
      simp [horizontal, spanSix, carrierLensRouteDirections,
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
        Gadget.unitSubdivisionDirections,
        AxisDirection.segmentLength,
        Int.natAbs_neg,
        AxisDirection.orientPoint, AxisDirection.between, Cell.add,
        spanThree] <;>
      omega

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
