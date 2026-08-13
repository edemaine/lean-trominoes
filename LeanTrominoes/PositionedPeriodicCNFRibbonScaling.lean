/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PositionedPeriodicCNFScaling
import LeanTrominoes.PeriodicGridDrawingEndpointContacts

/-!
# Padding positioned incidence drawings for ribbon refinement

A closed ribbon macrocell can reach the next refined lattice line.  The
expanded finite checker, however, asks for an open one-cell halo.  Uniformly
doubling a halo-bounded source leaves at least one integer unit below each
upper halo boundary, which is exactly the margin needed before the later
`128`-fold ribbon refinement.

This file also proves that positive scaling preserves endpoint-only listed
route contacts, so the doubled presentation remains ribbon-ready.
-/

namespace LeanTrominoes

namespace PeriodicGridDrawing

/-- Positive uniform scaling preserves the open one-period halo. -/
theorem positionInExpandedSquare_scale
    {factor : Nat} (positive : 0 < factor)
    {drawing : PeriodicGridDrawing} {point : Cell}
    (inside : drawing.PositionInExpandedSquare point) :
    (drawing.scale factor).PositionInExpandedSquare
      (Cell.scale factor point) := by
  simp only [PositionInExpandedSquare] at inside ⊢
  rw [gridSize_scale positive]
  rcases point with ⟨pointX, pointY⟩
  simp only [Cell.scale, Nat.cast_mul]
  have factorPositive : (0 : Int) < factor := by exact_mod_cast positive
  constructor
  · nlinarith [inside.1]
  constructor
  · nlinarith [inside.2.1]
  constructor
  · nlinarith [inside.2.2.1]
  · nlinarith [inside.2.2.2]

/-- Doubling a point in the open source halo gives one unit of upper margin
in the doubled halo. -/
theorem positionInExpandedSquareWithUpperMargin_scale_two
    {drawing : PeriodicGridDrawing} {point : Cell}
    (inside : drawing.PositionInExpandedSquare point) :
    (drawing.scale 2).PositionInExpandedSquareWithUpperMargin
      (Cell.scale 2 point) := by
  simp only [PositionInExpandedSquare] at inside
  simp only [PositionInExpandedSquareWithUpperMargin]
  rw [gridSize_scale (by decide)]
  rcases point with ⟨pointX, pointY⟩
  simp only [Cell.scale]
  omega

end PeriodicGridDrawing

namespace PositionedPeriodicCNF

/-- Reversal and periodic rebasing commute with positive uniform scaling. -/
theorem ContinuousPlanarIncidencePresentation.variableToClauseRoute_scale
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {factor : Nat} (factorPositive : 0 < factor)
    (presentation :
      source.ContinuousPlanarIncidencePresentation placement)
    (incidence : CNFIncidence Variable) :
    ((presentation.scale factorPositive).toPlanarIncidencePresentation
      |>.variableToClauseRoute incidence) =
      scalePolyline factor
        (presentation.toPlanarIncidencePresentation
          |>.variableToClauseRoute incidence) := by
  simp [PlanarIncidencePresentation.variableToClauseRoute,
    ContinuousPlanarIncidencePresentation.scale,
    scaleIncidenceRoutes,
    PeriodicOrthocrossing.translatePolyline,
    scalePolyline, List.map_reverse, List.map_map,
    Function.comp_def, Cell.scale_add]

/-- Any positive uniform scale preserves ordinary rebased-route halo
bounds. -/
theorem HaloBoundedContinuousPlanarIncidencePresentation.rebasedRoutePointsInExpandedSquare_scale
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    {factor : Nat} (factorPositive : 0 < factor)
    (presentation :
      source.HaloBoundedContinuousPlanarIncidencePresentation placement) :
    ((presentation.toContinuousPlanarIncidencePresentation.scale
        factorPositive).toPlanarIncidencePresentation)
      |>.RebasedRoutePointsInExpandedSquare := by
  intro tagged taggedMember point pointMember
  have taggedMember' :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    simpa using taggedMember
  rw [ContinuousPlanarIncidencePresentation.variableToClauseRoute_scale]
    at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨originalPoint, originalMember, rfl⟩
  change
    (incidenceDrawing
      (source.scale factor) (placement.scale factor)
      (scaleIncidenceRoutes factor presentation.routes))
      |>.PositionInExpandedSquare
        (Cell.scale factor originalPoint)
  rw [incidenceDrawing_scale
    factor source placement presentation.routes presentation.periodPositive]
  exact PeriodicGridDrawing.positionInExpandedSquare_scale factorPositive
    (presentation.rebasedRoutePointsInside
      tagged taggedMember' originalPoint originalMember)

/-- Doubling an ordinary rebased-route halo certificate produces the upper
margin needed by closed ribbon macrocells. -/
theorem HaloBoundedContinuousPlanarIncidencePresentation.rebasedRoutePointsInExpandedSquareWithUpperMargin_scale_two
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedContinuousPlanarIncidencePresentation placement) :
    ((presentation.toContinuousPlanarIncidencePresentation.scale
        (by decide : 0 < 2)).toPlanarIncidencePresentation)
      |>.RebasedRoutePointsInExpandedSquareWithUpperMargin := by
  intro tagged taggedMember point pointMember
  have taggedMember' :
      tagged ∈
        (PeriodicCNF.incidencesWithMetadata source.erase).zipIdx := by
    simpa using taggedMember
  rw [ContinuousPlanarIncidencePresentation.variableToClauseRoute_scale]
    at pointMember
  rcases List.mem_map.mp pointMember with
    ⟨originalPoint, originalMember, rfl⟩
  change
    (incidenceDrawing
      (source.scale 2) (placement.scale 2)
      (scaleIncidenceRoutes 2 presentation.routes))
      |>.PositionInExpandedSquareWithUpperMargin
        (Cell.scale 2 originalPoint)
  rw [incidenceDrawing_scale
    2 source placement presentation.routes presentation.periodPositive]
  exact
    PeriodicGridDrawing.positionInExpandedSquareWithUpperMargin_scale_two
      (presentation.rebasedRoutePointsInside
        tagged taggedMember' originalPoint originalMember)

end PositionedPeriodicCNF

namespace IndexedRoutePoint

/-- Scaling a listed route point changes only its physical coordinate. -/
def scale (factor : Int) (indexed : IndexedRoutePoint) :
    IndexedRoutePoint where
  routeIndex := indexed.routeIndex
  pointIndex := indexed.pointIndex
  routeLength := indexed.routeLength
  point := Cell.scale factor indexed.point

@[simp]
theorem scale_routeIndex (factor : Int) (indexed : IndexedRoutePoint) :
    (indexed.scale factor).routeIndex = indexed.routeIndex :=
  rfl

@[simp]
theorem scale_pointIndex (factor : Int) (indexed : IndexedRoutePoint) :
    (indexed.scale factor).pointIndex = indexed.pointIndex :=
  rfl

@[simp]
theorem scale_routeLength (factor : Int) (indexed : IndexedRoutePoint) :
    (indexed.scale factor).routeLength = indexed.routeLength :=
  rfl

@[simp]
theorem scale_point (factor : Int) (indexed : IndexedRoutePoint) :
    (indexed.scale factor).point = Cell.scale factor indexed.point :=
  rfl

end IndexedRoutePoint

namespace PeriodicGridDrawing

/-- The indexed listed points of a scaled drawing have the same syntactic
keys and scaled physical coordinates. -/
theorem indexedRoutePoints_scale
    (factor : Nat) (drawing : PeriodicGridDrawing) :
    (drawing.scale factor).indexedRoutePoints =
      drawing.indexedRoutePoints.map
        (IndexedRoutePoint.scale factor) := by
  unfold indexedRoutePoints PeriodicGridDrawing.scale
  rw [List.zipIdx_map, List.flatMap_map, List.map_flatMap]
  apply List.flatMap_congr
  rintro ⟨route, routeIndex⟩ taggedRouteMember
  simp [scalePolyline, List.zipIdx_map, List.map_map,
    IndexedRoutePoint.scale, Function.comp_def]

/-- Positive uniform scaling preserves endpoint-only contacts between
listed periodic route-point occurrences. -/
theorem routePointsMeetOnlyAtEndpoints_scale
    {factor : Nat} (positive : 0 < factor)
    (drawing : PeriodicGridDrawing)
    (contacts : drawing.RoutePointsMeetOnlyAtEndpoints) :
    (drawing.scale factor).RoutePointsMeetOnlyAtEndpoints := by
  intro first firstMember second secondMember
    firstTranslate secondTranslate different equal
  rw [indexedRoutePoints_scale] at firstMember secondMember
  rcases List.mem_map.mp firstMember with
    ⟨originalFirst, originalFirstMember, rfl⟩
  rcases List.mem_map.mp secondMember with
    ⟨originalSecond, originalSecondMember, rfl⟩
  have factorNonzero : (factor : Int) ≠ 0 := by
    exact_mod_cast Nat.ne_of_gt positive
  have originalEqual :
      Cell.add originalFirst.point
          (drawing.periodTranslation firstTranslate) =
        Cell.add originalSecond.point
          (drawing.periodTranslation secondTranslate) := by
    apply Cell.scale_injective factorNonzero
    simpa [Cell.scale_add, periodTranslation_scale positive] using equal
  have originalDifferent :
      RoutePointOccurrenceKey originalFirst firstTranslate ≠
        RoutePointOccurrenceKey originalSecond secondTranslate := by
    simpa [RoutePointOccurrenceKey] using different
  have result :=
    contacts originalFirst originalFirstMember
      originalSecond originalSecondMember
      firstTranslate secondTranslate
      originalDifferent originalEqual
  simpa [IndexedRoutePoint.IsEndpoint] using result

end PeriodicGridDrawing

namespace PositionedPeriodicCNF

/-- Doubling a halo-bounded ribbon-ready presentation preserves all of its
geometry and upgrades its rebased-route bounds to the required upper
margin. -/
noncomputable def HaloBoundedRibbonReadyIncidencePresentation.scaleTwo
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement) :
    (source.scale 2).HaloBoundedRibbonReadyIncidencePresentation
      (placement.scale 2) where
  toHaloBoundedContinuousPlanarIncidencePresentation := {
    toContinuousPlanarIncidencePresentation :=
      presentation.toContinuousPlanarIncidencePresentation.scale
        (by decide)
    rebasedRoutePointsInside :=
      (presentation.toContinuousPlanarIncidencePresentation.scale
          (by decide : 0 < 2)).toPlanarIncidencePresentation
        |>.rebasedRoutePointsInExpandedSquare_of_upperMargin
          (presentation.toHaloBoundedContinuousPlanarIncidencePresentation
            |>.rebasedRoutePointsInExpandedSquareWithUpperMargin_scale_two)
  }
  endpointContacts := by
    change
      (incidenceDrawing
        (source.scale 2) (placement.scale 2)
        (scaleIncidenceRoutes 2 presentation.routes))
        |>.RoutePointsMeetOnlyAtEndpoints
    rw [incidenceDrawing_scale
      2 source placement presentation.routes presentation.periodPositive]
    exact
      PeriodicGridDrawing.routePointsMeetOnlyAtEndpoints_scale
        (by decide) _ presentation.endpointContacts

/-- The doubled presentation carries the promised one-unit upper route
margin. -/
theorem HaloBoundedRibbonReadyIncidencePresentation.scaleTwo_rebasedRoutePointsInExpandedSquareWithUpperMargin
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    {placement : PeriodicVariablePlacement Variable}
    (presentation :
      source.HaloBoundedRibbonReadyIncidencePresentation placement) :
    (presentation.scaleTwo.toPlanarIncidencePresentation)
      |>.RebasedRoutePointsInExpandedSquareWithUpperMargin :=
  presentation.toHaloBoundedContinuousPlanarIncidencePresentation
    |>.rebasedRoutePointsInExpandedSquareWithUpperMargin_scale_two

end PositionedPeriodicCNF

end LeanTrominoes
