/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.EmbeddedCNFIncidenceDrawing
import LeanTrominoes.PlanarThreeSATWires
import Mathlib.Tactic

/-!
# A planar rectilinear equality lens

The two implication clauses of a positioned equality link can lie on the
same carrier axis as their endpoint variables.  Direct incidence segments
then overlap, even though the abstract four-cycle is planar.  This file gives
that four-cycle a uniformly narrow rectilinear drawing.

The canonical horizontal template has endpoint variables at `(0, 0)` and
`(span, 0)`, with the two existing clause vertices at `(3, 0)` and `(6, 0)`.
Its four routes occupy only the lanes `-2 ≤ y ≤ 1`; the only hypothesis is
`8 ≤ span`.  At the left endpoint they use the east and north rays, while
at the right endpoint they use the west and south rays.  Thus consecutive
lenses use all four rays exactly once at their shared carrier variable.
Later carrier geometry can translate, reflect, or rotate this one
parametric certificate.
-/

namespace LeanTrominoes
namespace PlanarThreeSAT

set_option maxHeartbeats 800000

/-- The two existing collinear clause positions of the canonical equality
link. -/
def horizontalEqualityLensPositions : EqualityPositions :=
  ⟨(3, 0), (6, 0)⟩

/-- Endpoint positions of a horizontal equality link of the given span. -/
def horizontalEqualityLensVariablePosition (span : Int) : Bool → Cell
  | false => (0, 0)
  | true => (span, 0)

/-- Forward incidence to the left endpoint, directly along the carrier. -/
def horizontalEqualityLensUpperLeftRoute : List Cell :=
  [(3, 0), (0, 0)]

/-- Forward incidence to the right endpoint, routed below the carrier. -/
def horizontalEqualityLensUpperRightRoute (span : Int) : List Cell :=
  [(3, 0), (3, -2), (span, -2), (span, 0)]

/-- Backward incidence to the left endpoint, routed above the carrier. -/
def horizontalEqualityLensLowerLeftRoute : List Cell :=
  [(6, 0), (6, 1), (0, 1), (0, 0)]

/-- Backward incidence to the right endpoint, directly along the carrier. -/
def horizontalEqualityLensLowerRightRoute (span : Int) : List Cell :=
  [(6, 0), (span, 0)]

/-- Total presentation-indexed route lookup for the equality lens. -/
def horizontalEqualityLensRoutes (span : Int) :
    Nat → Nat → List Cell
  | 0, 0 => horizontalEqualityLensUpperLeftRoute
  | 0, 1 => horizontalEqualityLensUpperRightRoute span
  | 1, 0 => horizontalEqualityLensLowerLeftRoute
  | 1, 1 => horizontalEqualityLensLowerRightRoute span
  | _, _ => []

/-- The canonical equality formula equipped with its narrow rectilinear
incidence routes. -/
def horizontalEqualityLensDrawing (span : Int) :
    EmbeddedCNFIncidenceDrawing Bool where
  formula :=
    equalityInstance false true horizontalEqualityLensPositions
  variablePosition := horizontalEqualityLensVariablePosition span
  routes := horizontalEqualityLensRoutes span

/-- Every equality-lens route starts and ends at its advertised graph
vertices. -/
theorem horizontalEqualityLensDrawing_routesMatch (span : Int) :
    (horizontalEqualityLensDrawing span).RoutesMatch := by
  intro index
  fin_cases index <;>
    simp [EmbeddedCNFIncidenceDrawing.incidenceAt,
      EmbeddedCNFIncidenceDrawing.incidences,
      embeddedCNFIncidences,
      EmbeddedCNFIncidenceDrawing.routeAt,
      horizontalEqualityLensDrawing,
      horizontalEqualityLensPositions,
      horizontalEqualityLensVariablePosition,
      horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute,
      equalityInstance]

/-- All four equality-lens routes are orthogonal once the long horizontal
segments are nondegenerate. -/
theorem horizontalEqualityLensDrawing_isOrthogonal
    (span : Int) (spanLarge : 8 ≤ span) :
    (horizontalEqualityLensDrawing span).IsOrthogonal := by
  intro incidenceIndex
  fin_cases incidenceIndex
  all_goals
    simp only [EmbeddedCNFIncidenceDrawing.incidenceAt,
      EmbeddedCNFIncidenceDrawing.incidences,
      embeddedCNFIncidences,
      EmbeddedCNFIncidenceDrawing.routeAt,
      horizontalEqualityLensDrawing,
      horizontalEqualityLensPositions,
      horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute,
      equalityInstance, List.zipIdx_cons, List.zipIdx_nil,
      List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
      List.get_cons_zero, List.get_cons_succ]
    intro segmentIndex
    fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.IsAxisAligned,
        GridSegment.IsHorizontal, GridSegment.IsVertical] <;>
      omega

private theorem horizontalEqualityLensUpperLeftRoute_isSimple :
    LocalIncidenceDrawing.RouteIsSimple
      horizontalEqualityLensUpperLeftRoute := by
  native_decide

private theorem horizontalEqualityLensUpperRightRoute_isSimple
    (span : Int) (spanLarge : 8 ≤ span) :
    LocalIncidenceDrawing.RouteIsSimple
      (horizontalEqualityLensUpperRightRoute span) := by
  simp [horizontalEqualityLensUpperRightRoute,
    LocalIncidenceDrawing.RouteIsSimple,
    gridPolylineSegments, GridSegment.InteriorsMeet,
    GridSegment.InteriorContains, GridSegment.OpenIntervalsOverlap,
    GridSegment.StrictlyBetween,
    GridSegment.IsHorizontal, GridSegment.IsVertical]
  omega

private theorem horizontalEqualityLensLowerLeftRoute_isSimple :
    LocalIncidenceDrawing.RouteIsSimple
      horizontalEqualityLensLowerLeftRoute := by
  native_decide

private theorem horizontalEqualityLensLowerRightRoute_isSimple
    (span : Int) (spanLarge : 8 ≤ span) :
    LocalIncidenceDrawing.RouteIsSimple
      (horizontalEqualityLensLowerRightRoute span) := by
  simp [horizontalEqualityLensLowerRightRoute,
    LocalIncidenceDrawing.RouteIsSimple,
    gridPolylineSegments, GridSegment.InteriorsMeet,
    GridSegment.InteriorContains, GridSegment.OpenIntervalsOverlap,
    GridSegment.StrictlyBetween,
    GridSegment.IsHorizontal, GridSegment.IsVertical]
  omega

private theorem horizontalEqualityLensUpper_routesAvoidEachOther
    (span : Int) (spanLarge : 8 ≤ span) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      horizontalEqualityLensUpperLeftRoute
      (horizontalEqualityLensUpperRightRoute span) := by
  unfold horizontalEqualityLensUpperLeftRoute
    horizontalEqualityLensUpperRightRoute
  constructor
  · intro firstIndex secondIndex
    fin_cases firstIndex <;> fin_cases secondIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorsMeet,
        GridSegment.OpenIntervalsOverlap, GridSegment.StrictlyBetween,
        GridSegment.IsHorizontal, GridSegment.IsVertical] <;>
      omega
  constructor
  · intro pointIndex segmentIndex
    fin_cases pointIndex <;> fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween, GridSegment.IsHorizontal,
        GridSegment.IsVertical] <;>
      omega
  constructor
  · intro pointIndex segmentIndex
    fin_cases pointIndex <;> fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween, GridSegment.IsHorizontal,
        GridSegment.IsVertical] <;>
      omega
  · intro firstIndex secondIndex pointsEqual
    fin_cases firstIndex <;> fin_cases secondIndex <;>
      simp_all [EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint] <;>
      omega

private theorem horizontalEqualityLensLeft_routesAvoidEachOther
    (span : Int) (spanLarge : 8 ≤ span) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      horizontalEqualityLensUpperLeftRoute
      horizontalEqualityLensLowerLeftRoute := by
  unfold horizontalEqualityLensUpperLeftRoute
    horizontalEqualityLensLowerLeftRoute
  constructor
  · intro firstIndex secondIndex
    fin_cases firstIndex <;> fin_cases secondIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorsMeet,
        GridSegment.OpenIntervalsOverlap, GridSegment.StrictlyBetween,
        GridSegment.IsHorizontal, GridSegment.IsVertical] <;>
      omega
  constructor
  · intro pointIndex segmentIndex
    fin_cases pointIndex <;> fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween, GridSegment.IsHorizontal,
        GridSegment.IsVertical] <;>
      omega
  constructor
  · intro pointIndex segmentIndex
    fin_cases pointIndex <;> fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween, GridSegment.IsHorizontal,
        GridSegment.IsVertical] <;>
      omega
  · intro firstIndex secondIndex pointsEqual
    fin_cases firstIndex <;> fin_cases secondIndex <;>
      simp_all [EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint] <;>
      omega

private theorem horizontalEqualityLensOppositeFirst_routesAvoidEachOther
    (span : Int) (spanLarge : 8 ≤ span) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      horizontalEqualityLensUpperLeftRoute
      (horizontalEqualityLensLowerRightRoute span) := by
  unfold horizontalEqualityLensUpperLeftRoute
    horizontalEqualityLensLowerRightRoute
  constructor
  · intro firstIndex secondIndex
    fin_cases firstIndex <;> fin_cases secondIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorsMeet,
        GridSegment.OpenIntervalsOverlap, GridSegment.StrictlyBetween,
        GridSegment.IsHorizontal, GridSegment.IsVertical] <;>
      omega
  constructor
  · intro pointIndex segmentIndex
    fin_cases pointIndex <;> fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween, GridSegment.IsHorizontal,
        GridSegment.IsVertical] <;>
      omega
  constructor
  · intro pointIndex segmentIndex
    fin_cases pointIndex <;> fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween, GridSegment.IsHorizontal,
        GridSegment.IsVertical] <;>
      omega
  · intro firstIndex secondIndex pointsEqual
    fin_cases firstIndex <;> fin_cases secondIndex <;>
      simp_all [EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint] <;>
      omega

private theorem horizontalEqualityLensOppositeSecond_routesAvoidEachOther
    (span : Int) (spanLarge : 8 ≤ span) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (horizontalEqualityLensUpperRightRoute span)
      horizontalEqualityLensLowerLeftRoute := by
  unfold horizontalEqualityLensUpperRightRoute
    horizontalEqualityLensLowerLeftRoute
  constructor
  · intro firstIndex secondIndex
    fin_cases firstIndex <;> fin_cases secondIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorsMeet,
        GridSegment.OpenIntervalsOverlap, GridSegment.StrictlyBetween,
        GridSegment.IsHorizontal, GridSegment.IsVertical] <;>
      omega
  constructor
  · intro pointIndex segmentIndex
    fin_cases pointIndex <;> fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween, GridSegment.IsHorizontal,
        GridSegment.IsVertical] <;>
      omega
  constructor
  · intro pointIndex segmentIndex
    fin_cases pointIndex <;> fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween, GridSegment.IsHorizontal,
        GridSegment.IsVertical] <;>
      omega
  · intro firstIndex secondIndex pointsEqual
    fin_cases firstIndex <;> fin_cases secondIndex <;>
      simp_all [EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint] <;>
      omega

private theorem horizontalEqualityLensRight_routesAvoidEachOther
    (span : Int) (spanLarge : 8 ≤ span) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (horizontalEqualityLensUpperRightRoute span)
      (horizontalEqualityLensLowerRightRoute span) := by
  unfold horizontalEqualityLensUpperRightRoute
    horizontalEqualityLensLowerRightRoute
  constructor
  · intro firstIndex secondIndex
    fin_cases firstIndex <;> fin_cases secondIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorsMeet,
        GridSegment.OpenIntervalsOverlap, GridSegment.StrictlyBetween,
        GridSegment.IsHorizontal, GridSegment.IsVertical] <;>
      omega
  constructor
  · intro pointIndex segmentIndex
    fin_cases pointIndex <;> fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween, GridSegment.IsHorizontal,
        GridSegment.IsVertical] <;>
      omega
  constructor
  · intro pointIndex segmentIndex
    fin_cases pointIndex <;> fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween, GridSegment.IsHorizontal,
        GridSegment.IsVertical] <;>
      omega
  · intro firstIndex secondIndex pointsEqual
    fin_cases firstIndex <;> fin_cases secondIndex <;>
      simp_all [EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint] <;>
      omega

private theorem horizontalEqualityLensLower_routesAvoidEachOther
    (span : Int) (spanLarge : 8 ≤ span) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      horizontalEqualityLensLowerLeftRoute
      (horizontalEqualityLensLowerRightRoute span) := by
  unfold horizontalEqualityLensLowerLeftRoute
    horizontalEqualityLensLowerRightRoute
  constructor
  · intro firstIndex secondIndex
    fin_cases firstIndex <;> fin_cases secondIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorsMeet,
        GridSegment.OpenIntervalsOverlap, GridSegment.StrictlyBetween,
        GridSegment.IsHorizontal, GridSegment.IsVertical] <;>
      omega
  constructor
  · intro pointIndex segmentIndex
    fin_cases pointIndex <;> fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween, GridSegment.IsHorizontal,
        GridSegment.IsVertical] <;>
      omega
  constructor
  · intro pointIndex segmentIndex
    fin_cases pointIndex <;> fin_cases segmentIndex <;>
      simp [gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween, GridSegment.IsHorizontal,
        GridSegment.IsVertical] <;>
      omega
  · intro firstIndex secondIndex pointsEqual
    fin_cases firstIndex <;> fin_cases secondIndex <;>
      simp_all [EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint] <;>
      omega

private theorem horizontalEqualityLensDrawing_verticesAvoidRouteInteriors
    (span : Int) (spanLarge : 8 ≤ span) :
    (horizontalEqualityLensDrawing
      span).VerticesAvoidRouteInteriors := by
  intro vertexIndex incidenceIndex
  fin_cases vertexIndex <;> fin_cases incidenceIndex
  all_goals
    simp only [EmbeddedCNFIncidenceDrawing.vertexPositions,
      EmbeddedCNFIncidenceDrawing.variableVertices,
      EmbeddedCNFIncidenceDrawing.incidenceAt,
      EmbeddedCNFIncidenceDrawing.incidences,
      embeddedCNFIncidences,
      EmbeddedCNFIncidenceDrawing.routeAt,
      horizontalEqualityLensDrawing,
      horizontalEqualityLensPositions,
      horizontalEqualityLensVariablePosition,
      horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute,
      equalityInstance, List.zipIdx_cons, List.zipIdx_nil,
      List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
      List.get_cons_zero, List.get_cons_succ]
    intro segmentIndex
    fin_cases segmentIndex <;>
      simp [horizontalEqualityLensVariablePosition,
        gridPolylineSegments, GridSegment.InteriorContains,
        GridSegment.StrictlyBetween,
        GridSegment.IsHorizontal, GridSegment.IsVertical] <;>
      omega

private theorem horizontalEqualityLensDrawing_vertexPositions_nodup
    (span : Int) (spanLarge : 8 ≤ span) :
    (horizontalEqualityLensDrawing span).vertexPositions.Nodup := by
  simp [EmbeddedCNFIncidenceDrawing.vertexPositions,
    EmbeddedCNFIncidenceDrawing.variableVertices,
    horizontalEqualityLensDrawing,
    horizontalEqualityLensPositions,
    horizontalEqualityLensVariablePosition,
    equalityInstance]
  omega

/-- The canonical rectilinear equality lens is continuously planar for every
admissible wire span. -/
theorem horizontalEqualityLensDrawing_isPlanar
    (span : Int) (spanLarge : 8 ≤ span) :
    (horizontalEqualityLensDrawing span).IsPlanar := by
  constructor
  · intro incidenceIndex
    fin_cases incidenceIndex
    · simpa [horizontalEqualityLensDrawing,
        horizontalEqualityLensPositions,
        horizontalEqualityLensRoutes,
        equalityInstance,
        EmbeddedCNFIncidenceDrawing.incidenceAt,
        EmbeddedCNFIncidenceDrawing.incidences,
        embeddedCNFIncidences,
        EmbeddedCNFIncidenceDrawing.routeAt] using
        horizontalEqualityLensUpperLeftRoute_isSimple
    · simpa [horizontalEqualityLensDrawing,
        horizontalEqualityLensPositions,
        horizontalEqualityLensRoutes,
        equalityInstance,
        EmbeddedCNFIncidenceDrawing.incidenceAt,
        EmbeddedCNFIncidenceDrawing.incidences,
        embeddedCNFIncidences,
        EmbeddedCNFIncidenceDrawing.routeAt] using
        horizontalEqualityLensUpperRightRoute_isSimple
          span spanLarge
    · simpa [horizontalEqualityLensDrawing,
        horizontalEqualityLensPositions,
        horizontalEqualityLensRoutes,
        equalityInstance,
        EmbeddedCNFIncidenceDrawing.incidenceAt,
        EmbeddedCNFIncidenceDrawing.incidences,
        embeddedCNFIncidences,
        EmbeddedCNFIncidenceDrawing.routeAt] using
        horizontalEqualityLensLowerLeftRoute_isSimple
    · simpa [horizontalEqualityLensDrawing,
        horizontalEqualityLensPositions,
        horizontalEqualityLensRoutes,
        equalityInstance,
        EmbeddedCNFIncidenceDrawing.incidenceAt,
        EmbeddedCNFIncidenceDrawing.incidences,
        embeddedCNFIncidences,
        EmbeddedCNFIncidenceDrawing.routeAt] using
        horizontalEqualityLensLowerRightRoute_isSimple
          span spanLarge
  constructor
  · intro firstIndex secondIndex different
    fin_cases firstIndex <;> fin_cases secondIndex
    all_goals
      simp only [horizontalEqualityLensDrawing,
        horizontalEqualityLensPositions,
        horizontalEqualityLensRoutes,
        equalityInstance,
        EmbeddedCNFIncidenceDrawing.incidenceAt,
        EmbeddedCNFIncidenceDrawing.incidences,
        embeddedCNFIncidences,
        EmbeddedCNFIncidenceDrawing.routeAt,
        List.zipIdx_cons, List.zipIdx_nil,
        List.flatMap_cons, List.flatMap_nil,
        List.map_cons, List.map_nil,
        List.get_cons_zero, List.get_cons_succ]
    · exact (different rfl).elim
    · exact horizontalEqualityLensUpper_routesAvoidEachOther
        span spanLarge
    · exact horizontalEqualityLensLeft_routesAvoidEachOther
        span spanLarge
    · exact horizontalEqualityLensOppositeFirst_routesAvoidEachOther
        span spanLarge
    · exact EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_comm
        (horizontalEqualityLensUpper_routesAvoidEachOther
          span spanLarge)
    · exact (different rfl).elim
    · exact
        horizontalEqualityLensOppositeSecond_routesAvoidEachOther
          span spanLarge
    · exact horizontalEqualityLensRight_routesAvoidEachOther
        span spanLarge
    · exact EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_comm
        (horizontalEqualityLensLeft_routesAvoidEachOther
          span spanLarge)
    · exact EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_comm
        (horizontalEqualityLensOppositeSecond_routesAvoidEachOther
          span spanLarge)
    · exact (different rfl).elim
    · exact horizontalEqualityLensLower_routesAvoidEachOther
        span spanLarge
    · exact EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_comm
        (horizontalEqualityLensOppositeFirst_routesAvoidEachOther
          span spanLarge)
    · exact EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_comm
        (horizontalEqualityLensRight_routesAvoidEachOther
          span spanLarge)
    · exact EmbeddedCNFIncidenceDrawing.routesAvoidEachOther_comm
        (horizontalEqualityLensLower_routesAvoidEachOther
          span spanLarge)
    · exact (different rfl).elim
  exact
    ⟨horizontalEqualityLensDrawing_verticesAvoidRouteInteriors
        span spanLarge,
      horizontalEqualityLensDrawing_vertexPositions_nodup
        span spanLarge⟩

/-- Complete endpoint, orthogonality, and continuous-planarity certificate
for the canonical equality lens. -/
theorem horizontalEqualityLensDrawing_isValid
    (span : Int) (spanLarge : 8 ≤ span) :
    (horizontalEqualityLensDrawing span).IsValid :=
  ⟨horizontalEqualityLensDrawing_routesMatch span,
    horizontalEqualityLensDrawing_isOrthogonal span spanLarge,
    horizontalEqualityLensDrawing_isPlanar span spanLarge⟩

set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

/-- Any selected route of one horizontal lens avoids any selected route of
the next lens on the same carrier.  The two drawings may meet only at their
shared endpoint `(span, 0)`. -/
theorem horizontalEqualityLensRoutes_adjacent_avoidEachOther
    (span nextSpan : Int)
    (spanLarge : 8 ≤ span)
    (nextSpanLarge : 8 ≤ nextSpan)
    (firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat)
    (firstClauseLt : firstClauseIndex < 2)
    (firstLiteralLt : firstLiteralIndex < 2)
    (secondClauseLt : secondClauseIndex < 2)
    (secondLiteralLt : secondLiteralIndex < 2) :
    EmbeddedCNFIncidenceDrawing.RoutesAvoidEachOther
      (horizontalEqualityLensRoutes span
        firstClauseIndex firstLiteralIndex)
      ((horizontalEqualityLensRoutes nextSpan
        secondClauseIndex secondLiteralIndex).map
          (Cell.add (span, 0))) := by
  interval_cases firstClauseIndex <;>
    interval_cases firstLiteralIndex <;>
    interval_cases secondClauseIndex <;>
    interval_cases secondLiteralIndex
  all_goals
    unfold horizontalEqualityLensRoutes
      horizontalEqualityLensUpperLeftRoute
      horizontalEqualityLensUpperRightRoute
      horizontalEqualityLensLowerLeftRoute
      horizontalEqualityLensLowerRightRoute
    constructor
    · intro firstIndex secondIndex
      fin_cases firstIndex <;> fin_cases secondIndex <;>
        simp [gridPolylineSegments, GridSegment.InteriorsMeet,
          GridSegment.OpenIntervalsOverlap,
          GridSegment.StrictlyBetween,
          GridSegment.IsHorizontal, GridSegment.IsVertical,
          Cell.add] <;>
        omega
    constructor
    · intro pointIndex segmentIndex
      fin_cases pointIndex <;> fin_cases segmentIndex <;>
        simp [gridPolylineSegments, GridSegment.InteriorContains,
          GridSegment.StrictlyBetween,
          GridSegment.IsHorizontal, GridSegment.IsVertical,
          Cell.add] <;>
        omega
    constructor
    · intro pointIndex segmentIndex
      fin_cases pointIndex <;> fin_cases segmentIndex <;>
        simp [gridPolylineSegments, GridSegment.InteriorContains,
          GridSegment.StrictlyBetween,
          GridSegment.IsHorizontal, GridSegment.IsVertical,
          Cell.add] <;>
        omega
    · intro firstIndex secondIndex pointsEqual
      fin_cases firstIndex <;> fin_cases secondIndex
      all_goals
        norm_num [Cell.add] at pointsEqual <;>
        norm_num [EmbeddedCNFIncidenceDrawing.RoutePointIsEndpoint,
          Cell.add] <;>
        omega

end PlanarThreeSAT
end LeanTrominoes
