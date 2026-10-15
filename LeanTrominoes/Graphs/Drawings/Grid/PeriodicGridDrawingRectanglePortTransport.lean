/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingPeriodicColumnPortTransport
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingVirtualHorizontalPortOrder
import LeanTrominoes.Graphs.Drawings.Orthogonal.RectangleBoundaryKeyTransport

/-! # The four rectangle sides share a verified boundary-port assignment -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement

inductive RectanglePortKey (Vertex : Type*) where
  | vertical (right : Bool) (key : ColumnPortKey Vertex)
  | horizontal (top : Bool) (key : Nat × Cell)

def RectanglePortKey.Valid {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) : RectanglePortKey Vertex → Prop
  | .vertical right key => key.Valid graph drawing ((column+if right then 1 else 0 : Nat) : Int) right
  | .horizontal _ key => key ∈ seamCrossingCopies graph drawing 0 ∧ seamAssignedSlab graph drawing key = column

def RectanglePortKey.virtualPort {Vertex : Type*} (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) : RectanglePortKey Vertex → RealRectangleBoundary.Port
  | .vertical right key => key.virtualPort graph drawing ((column+if right then 1 else 0 : Nat) : Int) right
  | .horizontal top key => virtualHorizontalPort graph drawing (columnPerturbation graph drawing) key top

def RectanglePortKey.integralPort {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) : RectanglePortKey Vertex → OrthogonalBoundaryRouting.Port
  | .vertical right key => key.periodicIntegralPort graph drawing ((column+if right then 1 else 0 : Nat) : Int) right
  | .horizontal top key => finiteHorizontalSlabPort graph drawing key top

def RectanglePortKey.side {Vertex : Type*} : RectanglePortKey Vertex → Fin 4
  | .vertical right _ => if right then 2 else 0
  | .horizontal top _ => if top then 1 else 3

theorem rectanglePort_virtual_side {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (key : RectanglePortKey Vertex) : (key.virtualPort graph drawing column).side = key.side := by
  cases key with
  | vertical right key => exact (columnPort_sides graph drawing _ right key).1
  | horizontal top key => rfl

theorem rectanglePort_integral_side {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (column : Nat) (key : RectanglePortKey Vertex) : (key.integralPort graph drawing column).side = key.side := by
  cases key with
  | vertical right key => cases key <;> rfl
  | horizontal top key => rfl

theorem rectanglePort_coordinate_order {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {first second : RectanglePortKey Vertex} (firstValid : first.Valid graph drawing column)
    (secondValid : second.Valid graph drawing column)
    (sameSide : (first.virtualPort graph drawing column).side = (second.virtualPort graph drawing column).side)
    (ordered : (first.virtualPort graph drawing column).coordinate < (second.virtualPort graph drawing column).coordinate) :
    (first.integralPort graph drawing column).coordinate < (second.integralPort graph drawing column).coordinate := by
  rw [rectanglePort_virtual_side,rectanglePort_virtual_side] at sameSide
  cases first with
  | vertical firstRight first =>
    cases second with
    | vertical secondRight second =>
      have faces : firstRight = secondRight := by
        cases firstRight <;> cases secondRight <;> simp_all [RectanglePortKey.side,Fin.ext_iff]
      subst secondRight
      exact periodic_columnPort_coordinate_order planar degree graphLocal straight (column+if firstRight then 1 else 0)
        firstRight firstValid secondValid ordered
    | horizontal top key => cases firstRight <;> cases top <;> norm_num [RectanglePortKey.side,Fin.ext_iff] at sameSide
  | horizontal firstTop first =>
    cases second with
    | vertical right key => cases firstTop <;> cases right <;> norm_num [RectanglePortKey.side,Fin.ext_iff] at sameSide
    | horizontal secondTop second =>
      have faces : firstTop = secondTop := by
        cases firstTop <;> cases secondTop <;> simp_all [RectanglePortKey.side,Fin.ext_iff]
      subst secondTop
      exact virtualHorizontalPort_coordinate_order planar degree straight firstValid.1 secondValid.1
        (firstValid.2.trans secondValid.2.symm) (columnPerturbation graph drawing) firstTop ordered

theorem rectanglePort_preserves_before {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {first second : RectanglePortKey Vertex} (firstValid : first.Valid graph drawing column)
    (secondValid : second.Valid graph drawing column)
    (ordered : (first.virtualPort graph drawing column).Before (second.virtualPort graph drawing column)) :
    (first.integralPort graph drawing column).Before (second.integralPort graph drawing column) := by
  exact RectangleBoundaryMatchingTransport.keys_preserve_before
    (fun key _ => (rectanglePort_integral_side graph drawing column key).trans (rectanglePort_virtual_side graph drawing column key).symm)
    (fun _ firstValid _ secondValid => rectanglePort_coordinate_order planar degree graphLocal straight column firstValid secondValid)
    firstValid secondValid ordered

theorem rectanglePort_virtual_inside {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    (key.virtualPort graph drawing column).Inside ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ) := by
  cases key with
  | vertical right key => exact periodic_columnPort_virtual_inside planar graphLocal straight _ right valid
  | horizontal top key =>
    exact virtualHorizontalPort_inside planar straight (columnPerturbation_positive planar straight)
      (columnPerturbation_le_cutMargin planar straight) valid.1 top

theorem finiteHorizontalSlabPort_inside {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (compatible : drawing.IsCompatible graph) (degree : graph.DegreeAtMost 4)
    {key : Nat × Cell} (member : key ∈ seamCrossingCopies graph drawing 0) (top : Bool) :
    (finiteHorizontalSlabPort graph drawing key top).Inside drawing.paddedSlabWidth
      (paddedGridSize drawing.gridSize) (2*crossingBound drawing.gridSize) := by
  have coordMember : (drawing.liftedStraightSegment key.1 key.2).rationalLineAbscissa 0 ∈ seamCrossingAbscissae graph drawing 0 :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨key,member,rfl⟩)
  have bounds := seamCrossingCoordinate_bounds compatible degree coordMember
  dsimp only at bounds
  have nonnegative : (0 : Int) ≤ crossingBound drawing.gridSize := by positivity
  cases top <;> simp [finiteHorizontalSlabPort,OrthogonalBoundaryRouting.Port.Inside,paddedSlabWidth,seamAssignedSlab]
  all_goals constructor <;> nlinarith [bounds.1,bounds.2]

theorem rectanglePort_integral_inside {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) {key : RectanglePortKey Vertex} (valid : key.Valid graph drawing column) :
    (key.integralPort graph drawing column).Inside drawing.paddedSlabWidth
      (paddedGridSize drawing.gridSize) (2*crossingBound drawing.gridSize) := by
  cases key with
  | vertical right key => exact periodic_columnPort_integral_inside planar degree graphLocal straight _ right valid
  | horizontal top key => exact finiteHorizontalSlabPort_inside planar.1.1 degree valid.1 top

end LeanTrominoes.PeriodicGridDrawing
