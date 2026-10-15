/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRationalRectangleContacts
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalAffineRectangleClips

/-! # Every proper affine rectangle contact occurs in the computed port list -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalAffineBoundary

theorem rational_rectangle_vertical_contact_retained {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) (column : Nat) (columnBound : column < drawing.gridSize) (right : Bool) (point : ℚ × ℚ)
    (spans : (drawing.liftedStraightSegment tagged.2 cell).SpansUnitColumn column)
    (sameX : point.1 = if right then 1-2*columnPerturbation graph drawing else 0)
    (heightBounds : 0 < point.2 ∧ point.2 < (drawing.gridSize : ℚ))
    (lineEquation : point.2 = rectangleAffineBase graph drawing column (tagged.2,cell)+
      (drawing.liftedStraightSegment tagged.2 cell).rationalSlope*point.1) :
    ∃ key : RectanglePortKey Vertex, key.Valid graph drawing column ∧ key.parentKey = (tagged.2,cell) ∧
      key.rationalPoint graph drawing column = point := by
  rw [rectangle_affine_height,sameX] at lineEquation
  have coordinateEqual : (column : ℚ)+columnPerturbation graph drawing+(if right then 1-2*columnPerturbation graph drawing else 0) =
      (column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing) := by
    cases right <;> simp <;> ring
  rw [coordinateEqual] at lineEquation
  have inside : -seamPerturbation graph drawing < (drawing.liftedStraightSegment tagged.2 cell).rationalHeightAt
      ((column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing)) ∧
      (drawing.liftedStraightSegment tagged.2 cell).rationalHeightAt
        ((column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing)) <
        (drawing.gridSize : ℚ)-seamPerturbation graph drawing := by constructor <;> linarith [heightBounds.1,heightBounds.2]
  obtain ⟨key,valid,parent,coordinate⟩ := vertical_cut_retained planar straight member edgeLocal cell column columnBound right spans inside
  have newCoordinate : (RectanglePortKey.vertical right key).rationalCoordinate graph drawing column = point.2 := by
    change key.rationalCoordinate graph drawing ((column+if right then 1 else 0 : Nat) : Int) right = point.2
    rw [coordinate]
    exact lineEquation.symm
  refine ⟨.vertical right key,valid,parent,?_⟩
  apply Prod.ext
  · cases right <;> simpa [RectanglePortKey.rationalPoint,RectanglePortKey.side,boundaryPoint] using sameX.symm
  · cases right <;> simpa [RectanglePortKey.rationalPoint,RectanglePortKey.side,boundaryPoint] using newCoordinate

theorem rational_rectangle_horizontal_contact_retained {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) (column : Nat) (columnBound : column < drawing.gridSize) (top : Bool) (point : ℚ × ℚ)
    (spans : (drawing.liftedStraightSegment tagged.2 cell).SpansUnitColumn column)
    (sameY : point.2 = if top then (drawing.gridSize : ℚ) else 0)
    (coordinateBounds : 0 < point.1 ∧ point.1 < 1-2*columnPerturbation graph drawing)
    (lineEquation : point.2 = rectangleAffineBase graph drawing column (tagged.2,cell)+
      (drawing.liftedStraightSegment tagged.2 cell).rationalSlope*point.1) :
    ∃ key : RectanglePortKey Vertex, key.Valid graph drawing column ∧ key.parentKey = (tagged.2,cell) ∧
      key.rationalPoint graph drawing column = point := by
  have epsilonPositive := columnPerturbation_positive planar straight
  have between := GridSegment.unit_column_inner_coordinate_between spans epsilonPositive ⟨coordinateBounds.1.le,coordinateBounds.2.le⟩
  have actual := GridSegment.realInteriorContains_implies_realContains (GridSegment.rationalHeightAt_realInteriorContains between)
  have nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠ (drawing.liftedStraightSegment tagged.2 cell).finish.1 := by
    rcases spans with forward | backward <;> omega
  rw [rectangle_affine_height] at lineEquation
  have heightEqual : (drawing.liftedStraightSegment tagged.2 cell).rationalHeightAt
      ((column : ℚ)+columnPerturbation graph drawing+point.1) = point.2-seamPerturbation graph drawing := by linarith
  simp only [Int.cast_natCast] at actual
  rw [heightEqual] at actual
  have contains : (drawing.liftedStraightSegment tagged.2 cell).RealContains
      ((((column : ℚ)+columnPerturbation graph drawing+point.1 : ℚ) : ℝ),
        ((drawing.gridSize : ℚ)*(if top then 1 else 0)-seamPerturbation graph drawing : ℝ)) := by
    cases top <;> simpa only [Bool.false_eq_true,if_false,if_true,mul_zero,mul_one,sameY,Rat.cast_sub,Rat.cast_zero,Rat.cast_natCast] using actual
  have inColumn : (column : ℚ) < (column : ℚ)+columnPerturbation graph drawing+point.1 ∧
      (column : ℚ)+columnPerturbation graph drawing+point.1 < (column : ℚ)+1 := by
    constructor <;> linarith [coordinateBounds.1,coordinateBounds.2]
  obtain ⟨key,valid,parent,coordinate,_,_⟩ := horizontal_cut_retained planar straight member edgeLocal cell column columnBound top nonvertical inColumn contains
  have newCoordinate : (RectanglePortKey.horizontal top key).rationalCoordinate graph drawing column = point.1 := by
    dsimp only [RectanglePortKey.rationalCoordinate]
    rw [coordinate,valid.2]
    push_cast
    ring
  refine ⟨.horizontal top key,valid,parent,?_⟩
  apply Prod.ext
  · cases top <;> simpa [RectanglePortKey.rationalPoint,RectanglePortKey.side,boundaryPoint] using newCoordinate
  · cases top <;> simpa [RectanglePortKey.rationalPoint,RectanglePortKey.side,boundaryPoint] using sameY.symm

theorem rational_rectangle_contact_retained {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) (column : Nat) (columnBound : column < drawing.gridSize) (point : ℚ × ℚ)
    (spans : (drawing.liftedStraightSegment tagged.2 cell).SpansUnitColumn column)
    (contact : Contact (1-2*columnPerturbation graph drawing) drawing.gridSize (rectangleAffineBase graph drawing column (tagged.2,cell))
      (drawing.liftedStraightSegment tagged.2 cell).rationalSlope point) :
    ∃ key : RectanglePortKey Vertex, key.Valid graph drawing column ∧ key.parentKey = (tagged.2,cell) ∧
      key.rationalPoint graph drawing column = point := by
  rcases contact.2 with vertical | horizontal
  · rcases vertical.1 with left | right
    · exact rational_rectangle_vertical_contact_retained planar straight member edgeLocal cell column columnBound false point spans left vertical.2 contact.1
    · exact rational_rectangle_vertical_contact_retained planar straight member edgeLocal cell column columnBound true point spans right vertical.2 contact.1
  · rcases horizontal.1 with bottom | top
    · exact rational_rectangle_horizontal_contact_retained planar straight member edgeLocal cell column columnBound false point spans bottom horizontal.2 contact.1
    · exact rational_rectangle_horizontal_contact_retained planar straight member edgeLocal cell column columnBound true point spans top horizontal.2 contact.1

end LeanTrominoes.PeriodicGridDrawing
