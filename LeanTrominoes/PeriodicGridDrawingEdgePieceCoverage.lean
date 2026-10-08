/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingEdgePieceColumnCoverage
import LeanTrominoes.PeriodicGridDrawingRectanglePieceWindow
import LeanTrominoes.PeriodicGridDrawingRectangleClosedCoverage

/-! # Every parameter of a straight nonvertical edge has an enumerated replacement piece -/
namespace LeanTrominoes.PeriodicGridDrawing
open PeriodicOrthocrossing OrthogonalDrawingRefinement RationalAffineBoundary RationalIntegerStripCover

set_option maxRecDepth 2048 in
theorem nonverticalEdgePieces_cover {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (nonvertical : (drawing.liftedStraightSegment tagged.2 (0,0)).start.1 ≠ (drawing.liftedStraightSegment tagged.2 (0,0)).finish.1)
    (parameter : ℚ) (lower : 0 ≤ parameter) (upper : parameter ≤ 1) :
    ∃ piece ∈ nonverticalEdgePieces graph drawing tagged, piece.start ≤ parameter ∧ parameter ≤ piece.finish := by
  rcases nonverticalEdgePieces_cover_outside_slabs planar graphLocal straight member nonvertical parameter lower upper with covered | inSlab
  · exact covered
  obtain ⟨oldColumn,slab⟩ := inSlab
  let segment := drawing.liftedStraightSegment tagged.2 (0,0)
  let original := segment.rationalPointAtParameter parameter
  let column := (oldColumn % (drawing.gridSize : Int)).toNat
  let cell : Cell := (oldColumn/(drawing.gridSize : Int),rationalCell drawing.gridSize (original.2+seamPerturbation graph drawing))
  let shift := drawing.periodTranslation (Cell.scale (-1) cell)
  let point : ℚ × ℚ := (original.1-(oldColumn : ℚ)-columnPerturbation graph drawing,
    rationalResidue drawing.gridSize (original.2+seamPerturbation graph drawing))
  have periodPositive : (0 : Int) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  have remainderNonnegative := Int.emod_nonneg oldColumn periodPositive.ne'
  have remainderBound := Int.emod_lt_of_pos oldColumn periodPositive
  have columnCast : (column : Int) = oldColumn % (drawing.gridSize : Int) := Int.toNat_of_nonneg remainderNonnegative
  have columnBound : column < drawing.gridSize := by omega
  have columnDecomposition : (column : ℚ)+(drawing.gridSize : ℚ)*cell.1 = oldColumn := by
    have decomposition := Int.emod_add_ediv_mul oldColumn (drawing.gridSize : Int)
    have integerEq : (column : Int)+(drawing.gridSize : Int)*cell.1 = oldColumn := by
      dsimp only [cell]
      nlinarith
    exact_mod_cast integerEq
  have xStrict : 0 < point.1 ∧ point.1 < 1-2*columnPerturbation graph drawing := by
    change (oldColumn : ℚ)+columnPerturbation graph drawing < original.1 ∧
      original.1 < (oldColumn : ℚ)+1-columnPerturbation graph drawing at slab
    dsimp only [point]
    constructor <;> linarith [slab.1,slab.2]
  have yBounds : 0 ≤ point.2 ∧ point.2 < (drawing.gridSize : ℚ) :=
    rationalResidue_bounds periodPositive (original.2+seamPerturbation graph drawing)
  have xEqual : (column : ℚ)+columnPerturbation graph drawing+point.1 = original.1+(shift.1 : ℚ) := by
    dsimp only [point,shift,periodTranslation,Cell.scale]
    push_cast
    linarith [columnDecomposition]
  have yEqual : -seamPerturbation graph drawing+point.2 = original.2+(shift.2 : ℚ) := by
    dsimp only [point,shift,periodTranslation,Cell.scale,cell,rationalResidue]
    push_cast
    ring
  have segmentEqual : drawing.liftedStraightSegment tagged.2 (Cell.scale (-1) cell) = segment.translate shift := by
    simpa only [Cell.add,zero_add] using liftedStraightSegment_add_cell drawing tagged.2 (0,0) (Cell.scale (-1) cell)
  have shiftedHeight : (drawing.liftedStraightSegment tagged.2 (Cell.scale (-1) cell)).rationalHeightAt
      ((column : ℚ)+columnPerturbation graph drawing+point.1) = -seamPerturbation graph drawing+point.2 := by
    rw [segmentEqual,xEqual,GridSegment.rationalHeightAt_translate]
    rw [GridSegment.rationalPointAtParameter_height nonvertical]
    exact yEqual.symm
  have onLine : point.2 = rectangleAffineBase graph drawing column (tagged.2,Cell.scale (-1) cell)+
      (drawing.liftedStraightSegment tagged.2 (Cell.scale (-1) cell)).rationalSlope*point.1 := by
    have affine := rectangle_affine_height graph drawing column (tagged.2,Cell.scale (-1) cell) point.1
    rw [shiftedHeight] at affine
    linarith
  have inside : ClosedPoint (1-2*columnPerturbation graph drawing) drawing.gridSize
      (rectangleAffineBase graph drawing column (tagged.2,Cell.scale (-1) cell))
      (drawing.liftedStraightSegment tagged.2 (Cell.scale (-1) cell)).rationalSlope point :=
    ⟨onLine,⟨xStrict.1.le,xStrict.2.le⟩,yBounds.1,yBounds.2.le⟩
  have originalContains := GridSegment.rationalPointAtParameter_realContains segment lower upper
  have translatedContains := (GridSegment.realContains_translate segment shift
    ((original.1 : ℝ),(original.2 : ℝ))).mpr originalContains
  have realPointEqual :
      ((((column : ℚ)+columnPerturbation graph drawing+point.1 : ℚ) : ℝ),((-seamPerturbation graph drawing+point.2 : ℚ) : ℝ)) =
      ((shift.1 : ℝ)+(original.1 : ℝ),(shift.2 : ℝ)+(original.2 : ℝ)) := by
    apply Prod.ext
    · have castEqual := congrArg (fun value : ℚ => (value : ℝ)) xEqual
      push_cast at castEqual
      push_cast
      simpa only [add_comm] using castEqual
    · have castEqual := congrArg (fun value : ℚ => (value : ℝ)) yEqual
      push_cast at castEqual
      push_cast
      simpa only [add_comm] using castEqual
  have contains : (drawing.liftedStraightSegment tagged.2 (Cell.scale (-1) cell)).RealContains
      ((((column : ℚ)+columnPerturbation graph drawing+point.1 : ℚ) : ℝ),((-seamPerturbation graph drawing+point.2 : ℚ) : ℝ)) := by
    rw [segmentEqual,realPointEqual]
    exact translatedContains
  have spans : (drawing.liftedStraightSegment tagged.2 (Cell.scale (-1) cell)).SpansUnitColumn column := by
    apply GridSegment.realContains_spans_unit_column contains
    dsimp only [Prod.fst]
    push_cast
    have positive : (0 : ℚ) < columnPerturbation graph drawing := columnPerturbation_positive planar straight
    have xBounds : (column : ℚ) < (column : ℚ)+columnPerturbation graph drawing+point.1 ∧
        (column : ℚ)+columnPerturbation graph drawing+point.1 < (column : ℚ)+1 := by
      constructor <;> linarith [xStrict.1,xStrict.2]
    exact ⟨by exact_mod_cast xBounds.1,by exact_mod_cast xBounds.2⟩
  obtain ⟨first,last,lookup⟩ := rectangleParentChord_exists_of_closed_clip planar graphLocal straight member
    (Cell.scale (-1) cell) column columnBound spans inside xStrict
  obtain ⟨piece,pieceMember,bounds⟩ := rectangleEdgePieces_cover_clip planar graphLocal straight tagged.2 column columnBound cell lookup inside
  have parameterEqual : (drawing.liftedStraightSegment tagged.2 (Cell.scale (-1) cell)).rationalXParameter
      ((column : ℚ)+columnPerturbation graph drawing+point.1) = parameter := by
    rw [segmentEqual,xEqual,GridSegment.rationalXParameter_translate]
    exact GridSegment.rationalXParameter_xAtParameter nonvertical parameter
  rw [parameterEqual] at bounds
  refine ⟨piece,?_,bounds⟩
  simp only [nonverticalEdgePieces,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  exact Or.inl (Or.inl (Or.inr pieceMember))

end LeanTrominoes.PeriodicGridDrawing
