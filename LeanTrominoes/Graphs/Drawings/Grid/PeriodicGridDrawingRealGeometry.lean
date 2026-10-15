/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridSegmentRealGeometry

/-! # Geometric periodic drawings, including diagonal segments and loops

The general drawing theorems concern closed curves in the real plane.
These predicates retain the executable integer-grid representation while
checking all real contacts. Simple closed routes are allowed for loops.
-/
namespace LeanTrominoes

def realCell (point : Cell) : ℝ × ℝ := (point.1,point.2)

namespace GridPolyline

def RealContains (route : List Cell) (point : ℝ × ℝ) : Prop :=
  ∃ segment ∈ gridPolylineSegments route, segment.RealContains point

def RealIsEndpoint (route : List Cell) (point : ℝ × ℝ) : Prop :=
  (∃ endpoint, route.head? = some endpoint ∧ point = realCell endpoint) ∨
    ∃ endpoint, route.getLast? = some endpoint ∧ point = realCell endpoint

/-- A route has no contacts between nonconsecutive pieces, except that the
first and last pieces may close a loop. Consecutive pieces meet only at their
common boundary. Nondegeneracy prevents constant pieces from hiding contacts. -/
def IsRealSimple (route : List Cell) : Prop :=
  2 ≤ route.length ∧
    (∀ segment ∈ gridPolylineSegments route, segment.start ≠ segment.finish) ∧
    ∀ first ∈ (gridPolylineSegments route).zipIdx,
      ∀ second ∈ (gridPolylineSegments route).zipIdx,
        first.2 < second.2 → ∀ point : ℝ × ℝ,
          first.1.RealContains point → second.1.RealContains point →
            (first.2+1 = second.2 ∧ point = realCell first.1.finish) ∨
              (first.2 = 0 ∧ second.2+1 = (gridPolylineSegments route).length ∧
                point = realCell first.1.start ∧ point = realCell second.1.finish)

end GridPolyline

namespace PeriodicGridDrawing

def realEdgeRoute (drawing : PeriodicGridDrawing) (index : Nat) (cell : Cell) : List Cell :=
  (drawing.edgeRoute index).map (Cell.add (drawing.periodTranslation cell))

def RealVerticesAvoidRoutes (drawing : PeriodicGridDrawing) : Prop :=
  ∀ vertex ∈ drawing.vertexPositions, ∀ vertexCell edgeCell edgeIndex,
    edgeIndex < drawing.edgeRoutes.length →
      GridPolyline.RealContains (drawing.realEdgeRoute edgeIndex edgeCell)
        (realCell (Cell.add vertex (drawing.periodTranslation vertexCell))) →
      GridPolyline.RealIsEndpoint (drawing.realEdgeRoute edgeIndex edgeCell)
        (realCell (Cell.add vertex (drawing.periodTranslation vertexCell)))

def RealRoutesAreSimple (drawing : PeriodicGridDrawing) : Prop :=
  ∀ route ∈ drawing.edgeRoutes, GridPolyline.IsRealSimple route

def RealRoutesMeetOnlyAtEndpoints (drawing : PeriodicGridDrawing) : Prop :=
  ∀ firstIndex secondIndex firstCell secondCell,
    firstIndex < drawing.edgeRoutes.length → secondIndex < drawing.edgeRoutes.length →
      (firstIndex,firstCell) ≠ (secondIndex,secondCell) →
        ∀ point : ℝ × ℝ,
          GridPolyline.RealContains (drawing.realEdgeRoute firstIndex firstCell) point →
          GridPolyline.RealContains (drawing.realEdgeRoute secondIndex secondCell) point →
            GridPolyline.RealIsEndpoint (drawing.realEdgeRoute firstIndex firstCell) point ∧
              GridPolyline.RealIsEndpoint (drawing.realEdgeRoute secondIndex secondCell) point

def RealProperlyCrossesAt (first second : GridSegment) (point : ℝ × ℝ) : Prop :=
  first.RealInteriorContains point ∧ second.RealInteriorContains point ∧
    ((first.IsHorizontal ∧ second.IsVertical) ∨ (first.IsVertical ∧ second.IsHorizontal))

def IsRealOrthocrossing (drawing : PeriodicGridDrawing) : Prop :=
  ∀ firstIndex secondIndex firstCell secondCell,
    firstIndex < drawing.edgeRoutes.length → secondIndex < drawing.edgeRoutes.length →
      (firstIndex,firstCell) ≠ (secondIndex,secondCell) →
        ∀ point : ℝ × ℝ,
          GridPolyline.RealContains (drawing.realEdgeRoute firstIndex firstCell) point →
          GridPolyline.RealContains (drawing.realEdgeRoute secondIndex secondCell) point →
            (GridPolyline.RealIsEndpoint (drawing.realEdgeRoute firstIndex firstCell) point ∧
              GridPolyline.RealIsEndpoint (drawing.realEdgeRoute secondIndex secondCell) point) ∨
            ∃ first ∈ gridPolylineSegments (drawing.realEdgeRoute firstIndex firstCell),
              ∃ second ∈ gridPolylineSegments (drawing.realEdgeRoute secondIndex secondCell),
                RealProperlyCrossesAt first second point

def RealPointInCell (drawing : PeriodicGridDrawing) (cell : Cell) (point : ℝ × ℝ) : Prop :=
  (drawing.gridSize : ℝ)*cell.1 ≤ point.1 ∧
    point.1 ≤ (drawing.gridSize : ℝ)*(cell.1+1) ∧
    (drawing.gridSize : ℝ)*cell.2 ≤ point.2 ∧
    point.2 ≤ (drawing.gridSize : ℝ)*(cell.2+1)

def IsRealLocal {Vertex : Type*} (drawing : PeriodicGridDrawing) (graph : PeriodicGraph Vertex) : Prop :=
  ∀ edge ∈ graph.edges.zipIdx, ∀ point : ℝ × ℝ,
    GridPolyline.RealContains (drawing.edgeRoute edge.2) point →
      drawing.RealPointInCell (0,0) point ∨ drawing.RealPointInCell edge.1.offset point

def IsRealDrawing {Vertex : Type*} [DecidableEq Vertex]
    (drawing : PeriodicGridDrawing) (graph : PeriodicGraph Vertex) : Prop :=
  drawing.IsCompatible graph ∧ drawing.RealRoutesAreSimple ∧ drawing.RealVerticesAvoidRoutes

def IsRealPlanarDrawing {Vertex : Type*} [DecidableEq Vertex]
    (drawing : PeriodicGridDrawing) (graph : PeriodicGraph Vertex) : Prop :=
  drawing.IsRealDrawing graph ∧ drawing.RealRoutesMeetOnlyAtEndpoints

end PeriodicGridDrawing
end LeanTrominoes
