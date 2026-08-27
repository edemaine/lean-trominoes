/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTerminalData
import LeanTrominoes.RetainedRayRasterizationTranslation

/-! # Semantics of retained carrier and bend terminal data -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicEightOccurrenceSplit
open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicThreeSATThree

/-- The explicit carrier-lens terminal datum is the exact terminal datum of
the corresponding retained local incidence route. -/
theorem carrier_routeTerminalData_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (degree : source.incidenceGraph.DegreeAtMost 3)
    (isLocal : source.incidenceGraph.IsLocal)
    (link : EqualityLink CarrierNode)
    (linkMember :
      link ∈ retainedDrawingCompleteCarrierLinks source.incidenceGraph)
    (localClauseIndex literalIndex : Nat) :
    classifiedRetainedTerminalData
        (routeTerminalVector
          (((DrawingPlanarSATClauseSource.carrier
              link localClauseIndex).incidenceDrawing source).routes
            localClauseIndex literalIndex)) =
      carrierLensRouteTerminalData link.first.isHorizontal
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
  have spanNotLtSix :
      ¬AxisDirection.axisSpan
          (CarrierNode.position source.incidenceGraph link.first)
          (CarrierNode.position source.incidenceGraph link.second) < 6 := by
    omega
  have spanDiffNeZero :
      AxisDirection.axisSpan
          (CarrierNode.position source.incidenceGraph link.first)
          (CarrierNode.position source.incidenceGraph link.second) - 6 ≠ 0 := by
    omega
  unfold DrawingPlanarSATClauseSource.incidenceDrawing
    drawingPlanarSATCarrierLensIncidenceDrawing
    EqualityLink.lensDrawing at ⊢
  change classifiedRetainedTerminalData
      (routeTerminalVector
        ((placedEqualityLensDrawing link.first link.second
          (CarrierNode.position source.incidenceGraph link.first)
          (AxisDirection.between
            (CarrierNode.position source.incidenceGraph link.first)
            (CarrierNode.position source.incidenceGraph link.second))
          (AxisDirection.axisSpan
            (CarrierNode.position source.incidenceGraph link.first)
            (CarrierNode.position source.incidenceGraph link.second))).routes
          localClauseIndex literalIndex)) = _
  change AxisDirection.between
      (CarrierNode.position source.incidenceGraph link.first)
      (CarrierNode.position source.incidenceGraph link.second) = _ at direction
  rw [direction]
  by_cases horizontal : link.first.isHorizontal = true
  all_goals
    rcases localClauseIndex with (_ | _ | localClauseIndex) <;>
      rcases literalIndex with (_ | _ | literalIndex) <;>
      simp [horizontal, spanSix, spanNotLtSix, spanDiffNeZero,
        carrierLensRouteTerminalData,
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
        routeTerminalVector, gridPolylineSegments,
        classifiedRetainedTerminalData,
        retainedTerminalDirectionClassify,
        retainedRayClassify, terminalPort, compassLength,
        routedClauseRayClassify, routedClauseRayMatches,
        routedClauseRayLengthCandidate, routedClauseRayPrimitive,
        RetainedRay.terminalDirection, oppositePort,
        RetainedRay.length,
        AxisDirection.orientPoint, Cell.add, Cell.sub, Cell.scale]

/-- Translation of a bend's finite corner table leaves its exact terminal
datum unchanged. -/
theorem bend_routeTerminalData_eq
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (localClauseIndex literalIndex : Nat) :
    classifiedRetainedTerminalData
        (routeTerminalVector
          (((DrawingPlanarSATClauseSource.bend
              routeBend localClauseIndex).incidenceDrawing source).routes
            localClauseIndex literalIndex)) =
      bendRouteTerminalData routeBend.incomingPort routeBend.outgoingPort
        localClauseIndex literalIndex := by
  change classifiedRetainedTerminalData
      (routeTerminalVector
        ((cornerEqualityRoutes routeBend.incomingPort routeBend.outgoingPort
          localClauseIndex literalIndex).map
            (Cell.add (Cell.scale planarMacroScale
              (routeBend.drawingPoint source.incidenceGraph))))) = _
  change classifiedRetainedTerminalData
      (routeTerminalVector
        (PeriodicOrthocrossing.translatePolyline
          (Cell.scale planarMacroScale
            (routeBend.drawingPoint source.incidenceGraph))
          (cornerEqualityRoutes routeBend.incomingPort routeBend.outgoingPort
            localClauseIndex literalIndex))) = _
  rw [routeTerminalVector_translatePolyline]
  rfl

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
