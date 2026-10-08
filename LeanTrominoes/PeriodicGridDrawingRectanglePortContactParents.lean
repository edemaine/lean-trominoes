/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectanglePortContactColumns
import LeanTrominoes.OrthogonalBoundaryPortPointInjection
import LeanTrominoes.PeriodicGridDrawingLiftedCrossingPortPoints

/-! # A shared new rectangle port identifies the original lifted edge -/
namespace LeanTrominoes.PeriodicGridDrawing
open OrthogonalDrawingRefinement OrthogonalBoundaryRouting

theorem rectangle_integral_ports_same_cell_parent_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (cell : Cell) {first last : RectanglePortKey Vertex}
    (firstValid : first.Valid graph drawing column) (lastValid : last.Valid graph drawing column)
    (pointEq : rectangleLiftedPortPoint graph drawing column cell first =
      rectangleLiftedPortPoint graph drawing column cell last) : first.parentKey = last.parentKey := by
  have points : (first.integralPort graph drawing column).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize) =
      (last.integralPort graph drawing column).point drawing.paddedSlabWidth (paddedGridSize drawing.gridSize) := by
    apply Prod.ext
    · have equal := congrArg Prod.fst pointEq
      change (drawing.rectangleRouteOffset column cell).1+_ = (drawing.rectangleRouteOffset column cell).1+_ at equal
      omega
    · have equal := congrArg Prod.snd pointEq
      change (drawing.rectangleRouteOffset column cell).2+_ = (drawing.rectangleRouteOffset column cell).2+_ at equal
      omega
  have room := paddedSlab_room drawing
  have portEq := Port.eq_of_point_eq (by omega : 0 < drawing.paddedSlabWidth)
    (by omega : (0 : Int) < paddedGridSize drawing.gridSize) (by positivity : (0 : Int) ≤ 2*crossingBound drawing.gridSize)
    (rectanglePort_integral_inside planar degree graphLocal straight column firstValid)
    (rectanglePort_integral_inside planar degree graphLocal straight column lastValid) points
  by_contra different
  have oldDifferent := rectanglePort_ne_of_parent_ne planar straight column
    (first := first) (last := last) firstValid lastValid different
  exact RectangleBoundaryMatchingTransport.new_ports_ne_of_old_ports_ne
    (Key := RectanglePortKey Vertex)
    (valid := fun key => key.Valid graph drawing column)
    (oldPort := fun key => key.virtualPort graph drawing column)
    (newPort := fun key => key.integralPort graph drawing column)
    (fun _ firstValid _ lastValid ordered => rectanglePort_preserves_before planar degree graphLocal straight column firstValid lastValid ordered)
    firstValid lastValid oldDifferent portEq

theorem rectangle_integral_ports_contact_parent_eq {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (degree : graph.DegreeAtMost 4) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (firstColumn lastColumn : Nat) (firstBound : firstColumn < drawing.gridSize) (lastBound : lastColumn < drawing.gridSize)
    (firstCell lastCell : Cell) {first last : RectanglePortKey Vertex}
    (firstValid : first.Valid graph drawing firstColumn) (lastValid : last.Valid graph drawing lastColumn)
    (pointEq : rectangleLiftedPortPoint graph drawing firstColumn firstCell first =
      rectangleLiftedPortPoint graph drawing lastColumn lastCell last) :
    first.liftedParentKey firstCell = last.liftedParentKey lastCell := by
  by_cases same : (firstColumn,firstCell) = (lastColumn,lastCell)
  · have columns := congrArg Prod.fst same
    have cells := congrArg Prod.snd same
    change firstColumn = lastColumn at columns
    change firstCell = lastCell at cells
    subst lastColumn
    subst lastCell
    have parents := rectangle_integral_ports_same_cell_parent_eq planar degree graphLocal straight firstColumn firstCell firstValid lastValid pointEq
    simp only [RectanglePortKey.liftedParentKey,parents]
  obtain ⟨columns,cellX⟩ := rectangle_integral_ports_contact_columns planar degree graphLocal straight
    firstColumn lastColumn firstBound lastBound firstCell lastCell firstValid lastValid pointEq
  obtain ⟨oldY,firstTop,firstRaw,firstEq⟩ := rectangle_distinct_integral_ports_old_y_eq planar degree graphLocal straight
    firstColumn lastColumn firstBound lastBound firstCell lastCell firstValid lastValid same pointEq
  obtain ⟨_,lastTop,lastRaw,lastEq⟩ := rectangle_distinct_integral_ports_old_y_eq planar degree graphLocal straight
    lastColumn firstColumn lastBound firstBound lastCell firstCell lastValid firstValid (Ne.symm same) pointEq.symm
  subst lastColumn
  subst first
  subst last
  have newX := congrArg Prod.fst pointEq
  rw [rectangleLiftedPortPoint_eq_translate,rectangleLiftedPortPoint_eq_translate,
    rectangle_integral_horizontal_port_point graph drawing firstColumn firstValid.2 firstTop,
    rectangle_integral_horizontal_port_point graph drawing firstColumn lastValid.2 lastTop] at newX
  simp only [Cell.add,Cell.scale] at newX
  rw [cellX] at newX
  have coordinateEq : seamCrossingCoordinate graph drawing 0 ((drawing.liftedStraightSegment firstRaw.1 firstRaw.2).rationalLineAbscissa 0) =
      seamCrossingCoordinate graph drawing 0 ((drawing.liftedStraightSegment lastRaw.1 lastRaw.2).rationalLineAbscissa 0) := by omega
  have firstMember : (drawing.liftedStraightSegment firstRaw.1 firstRaw.2).rationalLineAbscissa 0 ∈ seamCrossingAbscissae graph drawing 0 :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨firstRaw,firstValid.1,rfl⟩)
  have lastMember : (drawing.liftedStraightSegment lastRaw.1 lastRaw.2).rationalLineAbscissa 0 ∈ seamCrossingAbscissae graph drawing 0 :=
    List.mem_toFinset.mpr (List.mem_map.mpr ⟨lastRaw,lastValid.1,rfl⟩)
  have abscissaEq := (seamCrossingCoordinates_strictMonoOn planar.1.1 degree 0).injOn firstMember lastMember coordinateEq
  have rawEq := horizontalCrossingCopies_abscissa_injective planar straight 0
    (List.mem_filter.mp firstValid.1).1 (List.mem_filter.mp lastValid.1).1 abscissaEq
  subst lastRaw
  have gridPositive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have rows : firstCell.2+(if firstTop then 1 else 0 : Int) = lastCell.2+(if lastTop then 1 else 0 : Int) := by
    rw [rectangle_horizontal_original_point_y,rectangle_horizontal_original_point_y] at oldY
    have castEq : ((firstCell.2+(if firstTop then 1 else 0 : Int) : Int) : ℚ) =
        ((lastCell.2+(if lastTop then 1 else 0 : Int) : Int) : ℚ) := by
      push_cast
      cases firstTop <;> cases lastTop <;>
        norm_num only [Bool.false_eq_true,if_false,if_true] at oldY ⊢ <;>
        nlinarith only [oldY,gridPositive]
    exact_mod_cast castEq
  apply Prod.ext
  · rfl
  · apply Prod.ext
    · simp only [RectanglePortKey.liftedParentKey,RectanglePortKey.parentKey,Cell.add]
      omega
    · simp only [RectanglePortKey.liftedParentKey,RectanglePortKey.parentKey,Cell.add]
      omega

end LeanTrominoes.PeriodicGridDrawing
