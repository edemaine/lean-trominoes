/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleClipCoverage
import LeanTrominoes.RationalAffineClipInterval
import LeanTrominoes.RealRectanglePortPointInjection

/-! # The computed two-port groups delimit the exact original edge clip -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalAffineBoundary

theorem rectanglePort_rationalPoint_cast {Vertex : Type*} [DecidableEq Vertex]
    (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing) (column : Nat) (key : RectanglePortKey Vertex) :
    (((key.rationalPoint graph drawing column).1 : ℝ),((key.rationalPoint graph drawing column).2 : ℝ)) =
      (key.virtualPort graph drawing column).point ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) (drawing.gridSize : ℝ) := by
  have portEqual : RealRectangleBoundary.Port.mk key.side (key.rationalCoordinate graph drawing column : ℝ) =
      key.virtualPort graph drawing column := by
    apply RealRectangleBoundary.Port.clockwiseCode_injective
    simp only [RealRectangleBoundary.Port.clockwiseCode]
    rw [rectanglePort_virtual_side,rectanglePort_virtual_coordinate]
  have pointEqual := boundaryPoint_cast (1-2*columnPerturbation graph drawing) drawing.gridSize
    (key.rationalCoordinate graph drawing column) key.side
  rw [portEqual] at pointEqual
  simpa only [RectanglePortKey.rationalPoint,Rat.cast_natCast] using pointEqual

theorem rectangleParentChord_x_distinct {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (parent : Nat × Cell) {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some (first,last)) :
    (first.rationalPoint graph drawing column).1 ≠ (last.rationalPoint graph drawing column).1 := by
  have data := rectangleParentChord_data graph drawing column parent lookup
  have firstContact := rectanglePort_rational_contact planar graphLocal straight column data.1
  have lastContact := rectanglePort_rational_contact planar graphLocal straight column data.2.1
  rw [data.2.2.1] at firstContact
  rw [data.2.2.2.1] at lastContact
  intro equalX
  have equal := contact_eq_of_x_eq firstContact lastContact equalX
  have castEqual := congrArg (fun point : ℚ × ℚ => ((point.1 : ℝ),(point.2 : ℝ))) equal
  rw [rectanglePort_rationalPoint_cast,rectanglePort_rationalPoint_cast] at castEqual
  have widthPositive : (0 : ℝ) < ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) := by
    exact_mod_cast virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  have heightPositive : (0 : ℝ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have portsEqual := RealRectangleBoundary.Port.eq_of_point_eq widthPositive heightPositive
    (rectanglePort_virtual_inside planar graphLocal straight column data.1)
    (rectanglePort_virtual_inside planar graphLocal straight column data.2.1) castEqual
  have order := data.2.2.2.2
  change (first.virtualPort graph drawing column).clockwiseCode < (last.virtualPort graph drawing column).clockwiseCode at order
  rw [portsEqual] at order
  exact lt_irrefl _ order

theorem rectangleParentChord_clip_interval {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (columnBound : column < drawing.gridSize) (parent : Nat × Cell) {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some (first,last)) {point : ℚ × ℚ}
    (onLine : point.2 = rectangleAffineBase graph drawing column parent+
      (drawing.liftedStraightSegment parent.1 parent.2).rationalSlope*point.1) :
    ClosedPoint (1-2*columnPerturbation graph drawing) drawing.gridSize (rectangleAffineBase graph drawing column parent)
      (drawing.liftedStraightSegment parent.1 parent.2).rationalSlope point ↔
      min (first.rationalPoint graph drawing column).1 (last.rationalPoint graph drawing column).1 ≤ point.1 ∧
        point.1 ≤ max (first.rationalPoint graph drawing column).1 (last.rationalPoint graph drawing column).1 := by
  have data := rectangleParentChord_data graph drawing column parent lookup
  have firstContact := rectanglePort_rational_contact planar graphLocal straight column data.1
  have lastContact := rectanglePort_rational_contact planar graphLocal straight column data.2.1
  rw [data.2.2.1] at firstContact
  rw [data.2.2.2.1] at lastContact
  obtain ⟨tagged,member,index⟩ := rectanglePort_parent_tagged data.1
  have indexEqual := index.trans (congrArg Prod.fst data.2.2.1)
  have parentEqual : parent = (tagged.2,parent.2) := Prod.ext indexEqual.symm rfl
  have spans := rectanglePort_parent_spans_unit_column planar graphLocal straight column data.1
  rw [data.2.2.1,parentEqual] at spans
  have corners := rectangle_affine_corners_avoided planar straight member (graphLocal _ (List.fst_mem_of_mem_zipIdx member))
    parent.2 column columnBound
  have baseNotBottom : rectangleAffineBase graph drawing column parent ≠ 0 := by
    rw [parentEqual]
    simpa using corners false false spans
  have baseNotTop : rectangleAffineBase graph drawing column parent ≠ (drawing.gridSize : ℚ) := by
    rw [parentEqual]
    simpa using corners false true spans
  have widthPositive := virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  have heightPositive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have different := rectangleParentChord_x_distinct planar graphLocal straight column parent lookup
  rcases lt_or_gt_of_ne different with before | after
  · simpa only [min_eq_left before.le,max_eq_right before.le] using
      closed_clip_x_interval widthPositive heightPositive baseNotBottom baseNotTop firstContact lastContact before onLine
  · simpa only [min_eq_right after.le,max_eq_left after.le] using
      closed_clip_x_interval widthPositive heightPositive baseNotBottom baseNotTop lastContact firstContact after onLine

theorem rectangleParentChord_clip_realInteriorContains {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    (column : Nat) (parent : Nat × Cell) {first last : RectanglePortKey Vertex}
    (lookup : rectangleParentChord graph drawing column parent = some (first,last)) {point : ℚ × ℚ}
    (inside : ClosedPoint (1-2*columnPerturbation graph drawing) drawing.gridSize (rectangleAffineBase graph drawing column parent)
      (drawing.liftedStraightSegment parent.1 parent.2).rationalSlope point) :
    (drawing.liftedStraightSegment parent.1 parent.2).RealInteriorContains
      ((((column : ℚ)+columnPerturbation graph drawing+point.1 : ℚ) : ℝ),((-seamPerturbation graph drawing+point.2 : ℚ) : ℝ)) := by
  have data := rectangleParentChord_data graph drawing column parent lookup
  have spans := rectanglePort_parent_spans_unit_column planar graphLocal straight column data.1
  rw [data.2.2.1] at spans
  have between := GridSegment.unit_column_inner_coordinate_between spans (columnPerturbation_positive planar straight) inside.2.1
  have contact := GridSegment.rationalHeightAt_realInteriorContains between
  have height : -seamPerturbation graph drawing+point.2 =
      (drawing.liftedStraightSegment parent.1 parent.2).rationalHeightAt ((column : ℚ)+columnPerturbation graph drawing+point.1) := by
    have affine := rectangle_affine_height graph drawing column parent point.1
    linarith [inside.1]
  simpa only [height,Int.cast_natCast] using contact

end LeanTrominoes.PeriodicGridDrawing
