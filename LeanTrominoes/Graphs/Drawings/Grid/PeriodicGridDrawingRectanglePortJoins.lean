/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleRoutePlacement

/-! # Rectangle boundary ports agree with crossing bars, vertex fans, and row joins -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting GeneralVertexNormalization

def rectangleIntegralPortPoint {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (key : RectanglePortKey Vertex) : Cell :=
  Cell.add (drawing.paddedSlabOrigin column 0) ((key.integralPort graph drawing column).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize))

theorem rectangle_crossing_port_point {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (key : Nat × Cell) (right : Bool) :
    rectangleIntegralPortPoint graph drawing column (.vertical right (.crossing key)) =
      ((paddedRefinementFactor drawing.gridSize : Int)*((column+if right then 1 else 0 : Nat) : Int)+
        (if right then -5 else 5)*crossingBound drawing.gridSize,
        paddedPeriodicColumnHeight graph drawing ((column+if right then 1 else 0 : Nat) : Int)
          ((drawing.liftedStraightSegment key.1 key.2).rationalLineHeight ((column+if right then 1 else 0 : Nat) : Int))) := by
  cases right <;> apply Prod.ext <;>
    simp [rectangleIntegralPortPoint,RectanglePortKey.integralPort,ColumnPortKey.periodicIntegralPort,paddedSlabOrigin,paddedVerticalSlabPort,
      Port.point,paddedSlabWidth,Cell.add] <;> ring

theorem rectangle_integral_horizontal_port_point {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) {key : Nat × Cell} (sameSlab : seamAssignedSlab graph drawing key = column) (top : Bool) :
    rectangleIntegralPortPoint graph drawing column (.horizontal top key) =
      (seamCrossingCoordinate graph drawing 0 ((drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0),
        (paddedGridSize drawing.gridSize : Int)*(if top then 1 else 0)) := by
  cases top <;> apply Prod.ext <;>
    simp [rectangleIntegralPortPoint,RectanglePortKey.integralPort,finiteHorizontalSlabPort,paddedSlabOrigin,Port.point,Cell.add,sameSlab] <;> ring

theorem rectangle_incidence_port_point {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (right : Bool) {tagged : PeriodicEdge Vertex × Nat} {target : Bool}
    (valid : (RectanglePortKey.vertical right (.incidence tagged target)).Valid graph drawing column) :
    rectangleIntegralPortPoint graph drawing column (.vertical right (.incidence tagged target)) =
      Cell.add (Cell.scale (paddedRefinementFactor drawing.gridSize) (drawing.vertexPosition graph (endpointPort tagged target).vertex))
        (Cell.scale (crossingBound drawing.gridSize) (portBoundaryAnchor graph drawing (endpointPort tagged target))) := by
  have distinct := distinctPortRayKeys_of_planar_straight planar straight
  have anchorX := portBoundaryAnchor_x distinct degree (endpointPort_mem graph valid.1 target)
  have actualAnchorX : (portBoundaryAnchor graph drawing (endpointPort tagged target)).1 = if right then -5 else 5 := by
    rw [valid.2.2] at anchorX
    cases right <;> simpa [StraightRayKey.group,groupBoundaryX] using anchorX
  have sameColumn : (drawing.outwardStraightSegment tagged target).start.1-(if right then 1 else 0) = column := by
    rw [valid.2.1]
    cases right <;> simp
  have point := paddedFanSlabPort_point (drawing := drawing) (position := (drawing.outwardStraightSegment tagged target).start) right actualAnchorX
  rw [sameColumn,outwardStraightSegment_start planar.1.1 valid.1 target] at point
  simpa only [rectangleIntegralPortPoint,RectanglePortKey.integralPort,ColumnPortKey.periodicIntegralPort,assignedFanSlabPort,
    outwardStraightSegment_start planar.1.1 valid.1 target] using point

theorem rectangle_horizontal_ports_join {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (key : Nat × Cell) (cell : Cell) :
    Cell.add (drawing.rectangleRouteOffset column cell)
      (((RectanglePortKey.horizontal (Vertex := Vertex) true key).integralPort graph drawing column).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)) =
    Cell.add (drawing.rectangleRouteOffset column (Cell.add cell (0,1)))
      (((RectanglePortKey.horizontal (Vertex := Vertex) false key).integralPort graph drawing column).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize)) := by
  apply Prod.ext <;> simp [rectangleRouteOffset,rectangleRouteIndex,paddedSlabOrigin,RectanglePortKey.integralPort,finiteHorizontalSlabPort,Port.point,Cell.add] <;> ring

def RectanglePortKey.liftedParentKey {Vertex : Type*} (key : RectanglePortKey Vertex) (cell : Cell) : Nat × Cell :=
  (key.parentKey.1,Cell.add key.parentKey.2 cell)

theorem rectangle_horizontal_parent_keys_join {Vertex : Type*} (key : Nat × Cell) (cell : Cell) :
    (RectanglePortKey.horizontal (Vertex := Vertex) true key).liftedParentKey cell =
      (RectanglePortKey.horizontal (Vertex := Vertex) false key).liftedParentKey (Cell.add cell (0,1)) := by
  apply Prod.ext
  · rfl
  · apply Prod.ext <;> simp [RectanglePortKey.liftedParentKey,RectanglePortKey.parentKey,Cell.add] <;> ring

end LeanTrominoes.PeriodicGridDrawing
