/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendRouteDirectionWords
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataCarrierRouteDirectionWords

/-! # Source-prefix direction words of retained fallback routes -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Direction word of one carrier route after deleting its old variable
endpoint and therefore its complete final segment. -/
def carrierLensRoutePrefixDirections
    (horizontal : Bool) (span : Int) : Nat → Nat → List AxisDirection
  | 0, 0 => []
  | 0, 1 =>
      List.replicate 2 (if horizontal then .south else .east) ++
        List.replicate (span - 3).natAbs
          (if horizontal then .east else .north)
  | 1, 0 =>
      [if horizontal then .north else .west] ++
        List.replicate 6 (if horizontal then .west else .south)
  | 1, 1 => []
  | _, _ => []

/-- The local retained carrier drawing has exactly the explicit source-prefix
words above.  In particular, the two straight two-point routes contribute
empty prefixes. -/
theorem carrier_routePrefixDirections_eq
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
        ((((DrawingPlanarSATClauseSource.carrier
            link localClauseIndex).incidenceDrawing source).routes
          localClauseIndex literalIndex).dropLast) =
      carrierLensRoutePrefixDirections link.first.isHorizontal
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
      (((placedEqualityLensDrawing link.first link.second
        (CarrierNode.position source.incidenceGraph link.first)
        (AxisDirection.between
          (CarrierNode.position source.incidenceGraph link.first)
          (CarrierNode.position source.incidenceGraph link.second))
        (AxisDirection.axisSpan
          (CarrierNode.position source.incidenceGraph link.first)
          (CarrierNode.position source.incidenceGraph link.second))).routes
        localClauseIndex literalIndex).dropLast) = _
  change AxisDirection.between
      (CarrierNode.position source.incidenceGraph link.first)
      (CarrierNode.position source.incidenceGraph link.second) = _ at direction
  rw [direction]
  by_cases horizontal : link.first.isHorizontal = true
  all_goals
    rcases localClauseIndex with (_ | _ | localClauseIndex) <;>
      rcases literalIndex with (_ | _ | literalIndex) <;>
      simp [horizontal, carrierLensRoutePrefixDirections,
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

/-- Direction word of one fixed bend route after deleting its old variable
endpoint and complete final segment. -/
def bendRoutePrefixDirections
    (firstPort secondPort : CornerPort)
    (localClauseIndex literalIndex : Nat) : List AxisDirection :=
  Gadget.unitSubdivisionDirections
    (cornerEqualityRoutes firstPort secondPort
      localClauseIndex literalIndex).dropLast

/-- Placing a bend translates its source prefix, so the finite corner-table
prefix word is unchanged. -/
theorem bend_routePrefixDirections_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (localClauseIndex literalIndex : Nat) :
    Gadget.unitSubdivisionDirections
        ((((DrawingPlanarSATClauseSource.bend
            routeBend localClauseIndex).incidenceDrawing source).routes
          localClauseIndex literalIndex).dropLast) =
      bendRoutePrefixDirections
        routeBend.incomingPort routeBend.outgoingPort
        localClauseIndex literalIndex := by
  change Gadget.unitSubdivisionDirections
      (((cornerEqualityRoutes
          routeBend.incomingPort routeBend.outgoingPort
          localClauseIndex literalIndex).map
        (Cell.add (Cell.scale planarMacroScale
          (routeBend.drawingPoint source.incidenceGraph)))).dropLast) = _
  rw [← List.map_dropLast]
  change Gadget.unitSubdivisionDirections
      (PeriodicOrthocrossing.translatePolyline
        (Cell.scale planarMacroScale
          (routeBend.drawingPoint source.incidenceGraph))
        (cornerEqualityRoutes
          routeBend.incomingPort routeBend.outgoingPort
          localClauseIndex literalIndex).dropLast) = _
  exact Gadget.unitSubdivisionDirections_translatePolyline _ _

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
