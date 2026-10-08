/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleParameterCoverage
import LeanTrominoes.RationalAffineOpenClip

/-! # Interior clip parameters avoid every old rectangle boundary -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalAffineBoundary RationalIntervalPartition

theorem rectangleParentChord_base_avoids_horizontal_sides {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (columnBound : column < drawing.gridSize) (parent : Nat × Cell)
    {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some (first,last)) :
    rectangleAffineBase graph drawing column parent ≠ 0 ∧
      rectangleAffineBase graph drawing column parent ≠ (drawing.gridSize : ℚ) := by
  have data := rectangleParentChord_data graph drawing column parent lookup
  obtain ⟨tagged,member,index⟩ := rectanglePort_parent_tagged data.1
  have indexEqual := index.trans (congrArg Prod.fst data.2.2.1)
  have parentEqual : parent = (tagged.2,parent.2) := Prod.ext indexEqual.symm rfl
  have spans := rectanglePort_parent_spans_unit_column planar graphLocal straight column data.1
  rw [data.2.2.1,parentEqual] at spans
  have corners := rectangle_affine_corners_avoided planar straight member
    (graphLocal _ (List.fst_mem_of_mem_zipIdx member)) parent.2 column columnBound
  rw [parentEqual]
  exact ⟨by simpa using corners false false spans,by simpa using corners false true spans⟩

theorem rectangleParentChordInterval_open_bounds {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (columnBound : column < drawing.gridSize) (parent : Nat × Cell)
    {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some (first,last)) (parameter : ℚ)
    (after : (rectangleParentChordInterval planar graphLocal straight column parent lookup).start < parameter)
    (before : parameter < (rectangleParentChordInterval planar graphLocal straight column parent lookup).finish) :
    ((column : ℚ)+columnPerturbation graph drawing < ((drawing.liftedStraightSegment parent.1 parent.2).rationalPointAtParameter parameter).1 ∧
      ((drawing.liftedStraightSegment parent.1 parent.2).rationalPointAtParameter parameter).1 < (column : ℚ)+1-columnPerturbation graph drawing) ∧
      (-seamPerturbation graph drawing < ((drawing.liftedStraightSegment parent.1 parent.2).rationalPointAtParameter parameter).2 ∧
        ((drawing.liftedStraightSegment parent.1 parent.2).rationalPointAtParameter parameter).2 < (drawing.gridSize : ℚ)-seamPerturbation graph drawing) := by
  let original := (drawing.liftedStraightSegment parent.1 parent.2).rationalPointAtParameter parameter
  let point : ℚ × ℚ := (original.1-(column : ℚ)-columnPerturbation graph drawing,original.2+seamPerturbation graph drawing)
  have data := rectangleParentChord_data graph drawing column parent lookup
  have spans := rectanglePort_parent_spans_unit_column planar graphLocal straight column data.1
  rw [data.2.2.1] at spans
  have nonvertical : (drawing.liftedStraightSegment parent.1 parent.2).start.1 ≠
      (drawing.liftedStraightSegment parent.1 parent.2).finish.1 := by rcases spans with forward | backward <;> omega
  have coordinateEq : (column : ℚ)+columnPerturbation graph drawing+point.1 = original.1 := by dsimp [point]; ring
  have parameterEq : (drawing.liftedStraightSegment parent.1 parent.2).rationalXParameter
      ((column : ℚ)+columnPerturbation graph drawing+point.1) = parameter := by
    rw [coordinateEq]
    exact GridSegment.rationalXParameter_xAtParameter nonvertical parameter
  have openBetween := (GridSegment.rationalXParameter_between_open_iff nonvertical
    ((column : ℚ)+columnPerturbation graph drawing+(first.rationalPoint graph drawing column).1)
    ((column : ℚ)+columnPerturbation graph drawing+(last.rationalPoint graph drawing column).1)
    ((column : ℚ)+columnPerturbation graph drawing+point.1)).mp
      (by rw [parameterEq]; exact ⟨after,before⟩)
  have localBetween : min (first.rationalPoint graph drawing column).1 (last.rationalPoint graph drawing column).1 < point.1 ∧
      point.1 < max (first.rationalPoint graph drawing column).1 (last.rationalPoint graph drawing column).1 := by
    simpa only [min_lt_iff,lt_max_iff,add_lt_add_iff_left] using openBetween
  have onLine : point.2 = rectangleAffineBase graph drawing column parent+
      (drawing.liftedStraightSegment parent.1 parent.2).rationalSlope*point.1 := by
    have affine := rectangle_affine_height graph drawing column parent point.1
    rw [coordinateEq,GridSegment.rationalPointAtParameter_height nonvertical] at affine
    exact affine.symm
  have firstContact := rectanglePort_rational_contact planar graphLocal straight column data.1
  have lastContact := rectanglePort_rational_contact planar graphLocal straight column data.2.1
  rw [data.2.2.1] at firstContact
  rw [data.2.2.2.1] at lastContact
  have baseAvoids := rectangleParentChord_base_avoids_horizontal_sides planar graphLocal straight column columnBound parent lookup
  have widthPositive := virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  have heightPositive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have different := rectangleParentChord_x_distinct planar graphLocal straight column parent lookup
  have strictInside : (0 < point.1 ∧ point.1 < 1-2*columnPerturbation graph drawing) ∧
      (0 < point.2 ∧ point.2 < (drawing.gridSize : ℚ)) := by
    rcases lt_or_gt_of_ne different with increasing | decreasing
    · simp only [min_eq_left increasing.le,max_eq_right increasing.le] at localBetween
      exact open_clip_strict_inside widthPositive heightPositive baseAvoids.1 baseAvoids.2 firstContact lastContact localBetween.1 localBetween.2 onLine
    · simp only [min_eq_right decreasing.le,max_eq_left decreasing.le] at localBetween
      exact open_clip_strict_inside widthPositive heightPositive baseAvoids.1 baseAvoids.2 lastContact firstContact localBetween.1 localBetween.2 onLine
  change ((column : ℚ)+columnPerturbation graph drawing < original.1 ∧ original.1 < (column : ℚ)+1-columnPerturbation graph drawing) ∧
    (-seamPerturbation graph drawing < original.2 ∧ original.2 < (drawing.gridSize : ℚ)-seamPerturbation graph drawing)
  dsimp only [point] at strictInside
  exact ⟨⟨by linarith [strictInside.1.1],by linarith [strictInside.1.2]⟩,
    ⟨by linarith [strictInside.2.1],by linarith [strictInside.2.2]⟩⟩

end LeanTrominoes.PeriodicGridDrawing
