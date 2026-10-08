/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingTranslatedEndpointCuts
import LeanTrominoes.PeriodicGridDrawingRectanglePortSpan
import LeanTrominoes.PeriodicGridDrawingRationalPortOrder

/-! # Both kinds of proper virtual vertical contact occur in the finite port table -/
namespace LeanTrominoes.PeriodicGridDrawing
open GeneralVertexNormalization

theorem endpoint_occurrence_cut_retained {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) (target right : Bool)
    {line : Int} (lineBounds : 0 ≤ line ∧ line ≤ drawing.gridSize)
    (sameX : (if target then (drawing.liftedStraightSegment tagged.2 cell).reverse else
      drawing.liftedStraightSegment tagged.2 cell).start.1 = line)
    (direction : if right then
      (if target then (drawing.liftedStraightSegment tagged.2 cell).reverse else drawing.liftedStraightSegment tagged.2 cell).finish.1 < line else
      line < (if target then (drawing.liftedStraightSegment tagged.2 cell).reverse else drawing.liftedStraightSegment tagged.2 cell).finish.1)
    (inside : -seamPerturbation graph drawing < (drawing.liftedStraightSegment tagged.2 cell).rationalHeightAt
        ((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing)) ∧
      (drawing.liftedStraightSegment tagged.2 cell).rationalHeightAt
        ((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing)) <
        (drawing.gridSize : ℚ)-seamPerturbation graph drawing) :
    (ColumnPortKey.incidence tagged target).Valid graph drawing line right ∧
      (ColumnPortKey.incidence tagged target).parentKey = (tagged.2,cell) ∧
      (ColumnPortKey.incidence tagged target).rationalCoordinate graph drawing line right =
        (drawing.liftedStraightSegment tagged.2 cell).rationalHeightAt
          ((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing))+seamPerturbation graph drawing := by
  let shift : Cell := (cell.1-(endpointCell tagged target).1,cell.2-(endpointCell tagged target).2)
  have sumCell : Cell.add (endpointCell tagged target) shift = cell := by apply Prod.ext <;> simp [shift,Cell.add]
  have translatedEq := outwardStraightSegment_translate drawing tagged target shift
  rw [sumCell] at translatedEq
  have nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠
      (drawing.liftedStraightSegment tagged.2 cell).finish.1 := by
    cases target <;> cases right <;> simp [GridSegment.reverse] at sameX direction <;> omega
  have heightEqual : ((drawing.outwardStraightSegment tagged target).translate (drawing.periodTranslation shift)).rationalHeightAt
      ((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing)) =
      (drawing.liftedStraightSegment tagged.2 cell).rationalHeightAt
        ((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing)) := by
    rw [translatedEq]
    cases target
    · rfl
    · exact GridSegment.rationalHeightAt_reverse nonvertical _
  have shiftedX : (drawing.outwardStraightSegment tagged target).start.1+(drawing.gridSize : Int)*shift.1 = line := by
    rw [← translatedEq] at sameX
    simpa only [GridSegment.translate,Cell.add,periodTranslation,Cell.scale,add_comm] using sameX
  have shiftedDirection : if right then (drawing.outwardStraightSegment tagged target).finish.1 <
      (drawing.outwardStraightSegment tagged target).start.1 else
      (drawing.outwardStraightSegment tagged target).start.1 < (drawing.outwardStraightSegment tagged target).finish.1 := by
    have translatedDirection : if right then
        ((drawing.outwardStraightSegment tagged target).translate (drawing.periodTranslation shift)).finish.1 <
          ((drawing.outwardStraightSegment tagged target).translate (drawing.periodTranslation shift)).start.1 else
        ((drawing.outwardStraightSegment tagged target).translate (drawing.periodTranslation shift)).start.1 <
          ((drawing.outwardStraightSegment tagged target).translate (drawing.periodTranslation shift)).finish.1 := by
      simpa only [translatedEq,sameX] using direction
    cases right <;> simp [GridSegment.translate,Cell.add] at translatedDirection ⊢ <;> omega
  have retained := endpoint_cut_retained_of_virtual_row planar straight member target right shift lineBounds shiftedX shiftedDirection
    (by simpa only [heightEqual] using inside)
  have cellEqual : endpointCell tagged target = cell := by simpa only [retained.1,Cell.add,Prod.fst,Prod.snd,add_zero,Prod.eta] using sumCell
  refine ⟨retained.2,Prod.ext rfl cellEqual,?_⟩
  dsimp only [ColumnPortKey.rationalCoordinate]
  have unshifted : ((drawing.outwardStraightSegment tagged target).translate (drawing.periodTranslation shift)).rationalHeightAt
      ((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing)) =
      perturbedIncidenceHeight graph drawing tagged target right := by
    simp only [retained.1,periodTranslation,Cell.scale,mul_zero,GridSegment.translate,Cell.add,zero_add]
    rw [← retained.2.2.1]
    rfl
  rw [← unshifted,heightEqual]

theorem vertical_cut_retained {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) (column : Nat) (columnBound : column < drawing.gridSize) (right : Bool)
    (spans : (drawing.liftedStraightSegment tagged.2 cell).SpansUnitColumn column)
    (inside : -seamPerturbation graph drawing < (drawing.liftedStraightSegment tagged.2 cell).rationalHeightAt
        ((column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing)) ∧
      (drawing.liftedStraightSegment tagged.2 cell).rationalHeightAt
        ((column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing)) <
        (drawing.gridSize : ℚ)-seamPerturbation graph drawing) :
    ∃ key : ColumnPortKey Vertex, key.Valid graph drawing ((column+if right then 1 else 0 : Nat) : Int) right ∧
      key.parentKey = (tagged.2,cell) ∧ key.rationalCoordinate graph drawing ((column+if right then 1 else 0 : Nat) : Int) right =
        (drawing.liftedStraightSegment tagged.2 cell).rationalHeightAt
          ((column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing))+seamPerturbation graph drawing := by
  let line : Int := column+if right then 1 else 0
  have lineEq : ((column+if right then 1 else 0 : Nat) : Int) = line := by cases right <;> simp [line]
  have lineBounds : 0 ≤ line ∧ line ≤ drawing.gridSize := by cases right <;> simp [line] <;> omega
  have coordinateEq : (column : ℚ)+(if right then 1-columnPerturbation graph drawing else columnPerturbation graph drawing) =
      (line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing) := by
    cases right <;> simp [line] <;> ring
  rw [coordinateEq] at inside ⊢
  rw [lineEq]
  rcases GridSegment.unit_column_cut_endpoint_or_crossing spans right with crossing | endpoint | endpoint
  · have perturbedEq : perturbedColumnHeight graph drawing line (tagged.2,cell) right =
        (drawing.liftedStraightSegment tagged.2 cell).rationalHeightAt
          ((line : ℚ)+(if right then -columnPerturbation graph drawing else columnPerturbation graph drawing)) := rfl
    exact ⟨.crossing (tagged.2,cell),column_crossing_retained_of_virtual_row planar straight member edgeLocal cell lineBounds crossing right
      (by simpa only [perturbedEq] using inside),rfl,by simp only [ColumnPortKey.rationalCoordinate,perturbedEq]⟩
  · exact ⟨.incidence tagged false,endpoint_occurrence_cut_retained planar straight member cell false right lineBounds endpoint.1 endpoint.2 inside⟩
  · exact ⟨.incidence tagged true,endpoint_occurrence_cut_retained planar straight member cell true right lineBounds endpoint.1 endpoint.2 inside⟩

end LeanTrominoes.PeriodicGridDrawing
