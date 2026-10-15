/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingFanPortOrder

/-! # One boundary-port map handles both crossings and vertex incidences -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement GeneralVertexNormalization PeriodicOrthocrossing

inductive ColumnPortKey (Vertex : Type*) where
  | crossing (key : Nat × Cell)
  | incidence (tagged : PeriodicEdge Vertex × Nat) (target : Bool)

def ColumnPortKey.Valid {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Int) (right : Bool) : ColumnPortKey Vertex → Prop
  | .crossing key => key ∈ verticalCrossingCopies graph drawing column
  | .incidence tagged target => tagged ∈ graph.edges.zipIdx ∧
      (drawing.outwardStraightSegment tagged target).start.1 = column ∧
      drawing.portRayKey (endpointPort tagged target) =
        if right then .left (drawing.outwardStraightSegment tagged target).rationalSlope else
          .right (drawing.outwardStraightSegment tagged target).rationalSlope

def ColumnPortKey.virtualPort {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Int) (right : Bool) : ColumnPortKey Vertex → RealRectangleBoundary.Port
  | .crossing key => virtualVerticalPort graph drawing column key right
  | .incidence tagged target => virtualIncidencePort graph drawing tagged target right

def ColumnPortKey.integralPort {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Int) (right : Bool) : ColumnPortKey Vertex → OrthogonalBoundaryRouting.Port
  | .crossing key => finiteVerticalSlabPort graph drawing column key right
  | .incidence tagged target => assignedFanSlabPort graph drawing tagged target right

theorem columnPort_coordinate_order {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} (columnBound : column < drawing.gridSize) (right : Bool)
    {first second : ColumnPortKey Vertex} (firstValid : first.Valid graph drawing column right)
    (secondValid : second.Valid graph drawing column right)
    (ordered : (first.virtualPort graph drawing column right).coordinate < (second.virtualPort graph drawing column right).coordinate) :
    (first.integralPort graph drawing column right).coordinate < (second.integralPort graph drawing column right).coordinate := by
  have distinct := distinctPortRayKeys_of_planar_straight planar straight
  cases first with
  | crossing first =>
    cases second with
    | crossing second => exact virtualVerticalPort_coordinate_order planar degree straight columnBound firstValid secondValid right ordered
    | incidence tagged target =>
      have bounds := portBoundaryAnchor_bounds distinct degree (endpointPort_mem graph secondValid.1 target)
      exact crossing_fan_coordinate_order planar degree straight columnBound firstValid secondValid.1 target right secondValid.2.1
        ⟨bounds.2.2.1,bounds.2.2.2⟩ ordered
  | incidence first firstTarget =>
    cases second with
    | crossing key =>
      have bounds := portBoundaryAnchor_bounds distinct degree (endpointPort_mem graph firstValid.1 firstTarget)
      exact fan_crossing_coordinate_order planar degree straight columnBound secondValid firstValid.1 firstTarget right firstValid.2.1
        ⟨bounds.2.2.1,bounds.2.2.2⟩ ordered
    | incidence second secondTarget =>
      exact virtualIncidencePort_coordinate_order planar degree straight firstValid.1 secondValid.1 firstTarget secondTarget right
        (firstValid.2.1.trans secondValid.2.1.symm) firstValid.2.2 secondValid.2.2 ordered

theorem columnPort_virtual_inside {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {column : Nat} (columnBound : column < drawing.gridSize) (right : Bool)
    {key : ColumnPortKey Vertex} (valid : key.Valid graph drawing column right) :
    (key.virtualPort graph drawing column right).Inside
      ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ) := by
  cases key with
  | crossing key => exact virtualVerticalPort_inside planar straight columnBound valid right
  | incidence tagged target => exact virtualIncidencePort_inside planar straight valid.1 target right

theorem columnPort_integral_inside {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Int) (right : Bool) {key : ColumnPortKey Vertex} (valid : key.Valid graph drawing column right) :
    (key.integralPort graph drawing column right).Inside drawing.paddedSlabWidth
      (paddedGridSize drawing.gridSize) (2*crossingBound drawing.gridSize) := by
  cases key with
  | crossing key =>
    have member : (drawing.liftedStraightSegment key.1 key.2).rationalLineHeight column ∈ verticalCrossingHeights graph drawing column :=
      List.mem_toFinset.mpr (List.mem_map.mpr ⟨key,valid,rfl⟩)
    have bounds := paddedCrossingHeight_in_cell planar.1.1 degree member
    have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
    cases right <;> simp [ColumnPortKey.integralPort,finiteVerticalSlabPort,OrthogonalBoundaryRouting.Port.Inside]
    all_goals constructor <;> omega
  | incidence tagged target =>
    have bounds := outwardStraightSegment_start_bounds planar.1.1 valid.1 target
    have distinct := distinctPortRayKeys_of_planar_straight planar straight
    have anchorBounds := portBoundaryAnchor_bounds distinct degree (endpointPort_mem graph valid.1 target)
    exact paddedFanSlabPort_inside ⟨bounds.2.2.1,bounds.2.2.2⟩ ⟨anchorBounds.2.2.1,anchorBounds.2.2.2⟩ right

theorem columnPort_sides {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Int) (right : Bool) (key : ColumnPortKey Vertex) :
    (key.virtualPort graph drawing column right).side = (if right then 2 else 0) ∧
      (key.integralPort graph drawing column right).side = (if right then 2 else 0) := by
  cases key <;> exact ⟨rfl,rfl⟩

end LeanTrominoes.PeriodicGridDrawing
