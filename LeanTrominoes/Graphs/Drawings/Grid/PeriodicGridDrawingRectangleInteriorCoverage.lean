/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRectangleMatchingCoverage
import LeanTrominoes.Graphs.Drawings.Orthogonal.RationalAffineRectangleInteriorContacts
import LeanTrominoes.Common.Geometry.GridSegmentRealHeightAt

/-! # Every original edge portion entering a virtual rectangle is routed -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalAffineBoundary

theorem rectanglePort_exists_of_interior_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    (cell : Cell) (column : Nat) (columnBound : column < drawing.gridSize) {point : ℝ × ℝ}
    (contains : (drawing.liftedStraightSegment tagged.2 cell).RealContains point)
    (xBounds : (column : ℝ)+(columnPerturbation graph drawing : ℝ) < point.1 ∧
      point.1 < (column : ℝ)+1-(columnPerturbation graph drawing : ℝ))
    (yBounds : -(seamPerturbation graph drawing : ℝ) < point.2 ∧
      point.2 < (drawing.gridSize : ℝ)-(seamPerturbation graph drawing : ℝ)) :
    ∃ key : RectanglePortKey Vertex, key.Valid graph drawing column ∧ key.parentKey = (tagged.2,cell) := by
  have epsilonPositive : (0 : ℝ) < columnPerturbation graph drawing := by exact_mod_cast columnPerturbation_positive planar straight
  have spans : (drawing.liftedStraightSegment tagged.2 cell).SpansUnitColumn column :=
    GridSegment.realContains_spans_unit_column contains ⟨by simp only [Int.cast_natCast]; linarith [xBounds.1],
      by simp only [Int.cast_natCast]; linarith [xBounds.2]⟩
  have nonvertical : (drawing.liftedStraightSegment tagged.2 cell).start.1 ≠ (drawing.liftedStraightSegment tagged.2 cell).finish.1 := by
    rcases spans with forward | backward <;> omega
  have height := GridSegment.realContains_affine_height nonvertical ((column : ℚ)+columnPerturbation graph drawing) contains
  let localX := point.1-(column : ℝ)-(columnPerturbation graph drawing : ℝ)
  let localY := point.2+(seamPerturbation graph drawing : ℝ)
  have coordinateBounds : (0 : ℝ) ≤ localX ∧ localX ≤ ((1-2*columnPerturbation graph drawing : ℚ) : ℝ) := by
    dsimp [localX]
    push_cast
    constructor <;> linarith [xBounds.1,xBounds.2]
  have heightBounds : (0 : ℝ) < localY ∧ localY < ((drawing.gridSize : ℚ) : ℝ) := by
    dsimp [localY]
    simp only [Rat.cast_natCast]
    constructor <;> linarith [yBounds.1,yBounds.2]
  have lineEquation : localY = (rectangleAffineBase graph drawing column (tagged.2,cell) : ℝ)+
      ((drawing.liftedStraightSegment tagged.2 cell).rationalSlope : ℝ)*localX := by
    dsimp only [localX,localY,rectangleAffineBase,Prod.fst,Prod.snd]
    push_cast at height ⊢
    nlinarith [height]
  have corner := rectangle_affine_corners_avoided planar straight member edgeLocal cell column columnBound
  have widthPositive := virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
  have gridPositive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
  obtain ⟨contactPoint,contact⟩ := contact_exists_of_real_interior widthPositive gridPositive
    (by simpa using corner false false spans) (by simpa using corner false true spans)
    (by simpa using corner true false spans) (by simpa using corner true true spans) coordinateBounds heightBounds lineEquation
  obtain ⟨key,valid,parent,_⟩ := rational_rectangle_contact_retained planar straight member edgeLocal cell column columnBound contactPoint spans contact
  exact ⟨key,valid,parent⟩

theorem rectangleChordFamily_covers_interior_contact {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (cell : Cell) (column : Nat) (columnBound : column < drawing.gridSize) {point : ℝ × ℝ}
    (contains : (drawing.liftedStraightSegment tagged.2 cell).RealContains point)
    (xBounds : (column : ℝ)+(columnPerturbation graph drawing : ℝ) < point.1 ∧
      point.1 < (column : ℝ)+1-(columnPerturbation graph drawing : ℝ))
    (yBounds : -(seamPerturbation graph drawing : ℝ) < point.2 ∧
      point.2 < (drawing.gridSize : ℝ)-(seamPerturbation graph drawing : ℝ)) :
    ∃ first last : RectanglePortKey Vertex,
      rectangleParentChord graph drawing column (tagged.2,cell) = some (first,last) ∧
      (first.integralPort graph drawing column,last.integralPort graph drawing column) ∈ rectangleChordFamily graph drawing column := by
  obtain ⟨key,valid,parent⟩ := rectanglePort_exists_of_interior_contact planar straight member
    (graphLocal _ (List.fst_mem_of_mem_zipIdx member)) cell column columnBound contains xBounds yBounds
  obtain ⟨first,last,lookup,chordAt,_⟩ := rectangleChordFamily_covers_port planar graphLocal straight column columnBound valid
  exact ⟨first,last,by simpa only [parent] using lookup,chordAt⟩

end LeanTrominoes.PeriodicGridDrawing
