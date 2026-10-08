/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRectangleInteriorCoverage
import LeanTrominoes.PeriodicGridDrawingRectangleParameterCoverage

/-! # Rectangle chord coverage also includes points on a horizontal period seam -/
namespace LeanTrominoes.PeriodicGridDrawing
open RationalAffineBoundary

theorem rectangleParentChord_exists_of_closed_clip {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}
    (planar : drawing.IsRealPlanarDrawing graph) (graphLocal : graph.IsLocal)
    (straight : ∀ tagged ∈ graph.edges.zipIdx, (drawing.edgeRoute tagged.2).length = 2)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (cell : Cell) (column : Nat) (columnBound : column < drawing.gridSize)
    (spans : (drawing.liftedStraightSegment tagged.2 cell).SpansUnitColumn column)
    {point : ℚ × ℚ}
    (inside : ClosedPoint (1-2*columnPerturbation graph drawing) drawing.gridSize
      (rectangleAffineBase graph drawing column (tagged.2,cell))
      (drawing.liftedStraightSegment tagged.2 cell).rationalSlope point)
    (xStrict : 0 < point.1 ∧ point.1 < 1-2*columnPerturbation graph drawing) :
    ∃ first last : RectanglePortKey Vertex,
      rectangleParentChord graph drawing column (tagged.2,cell) = some (first,last) := by
  have edgeLocal := graphLocal _ (List.fst_mem_of_mem_zipIdx member)
  have contactExists : ∃ contactPoint : ℚ × ℚ,
      Contact (1-2*columnPerturbation graph drawing) drawing.gridSize
        (rectangleAffineBase graph drawing column (tagged.2,cell))
        (drawing.liftedStraightSegment tagged.2 cell).rationalSlope contactPoint := by
    by_cases bottom : point.2 = 0
    · exact ⟨point,inside.1,Or.inr ⟨Or.inl bottom,xStrict⟩⟩
    by_cases top : point.2 = (drawing.gridSize : ℚ)
    · exact ⟨point,inside.1,Or.inr ⟨Or.inr top,xStrict⟩⟩
    have corners := rectangle_affine_corners_avoided planar straight member edgeLocal cell column columnBound
    have widthPositive := virtualSlabWidth_positive (columnPerturbation_le_cutMargin planar straight)
    have heightPositive : (0 : ℚ) < drawing.gridSize := by exact_mod_cast Nat.zero_lt_succ drawing.gridSizePred
    have strictHeight : (0 : ℚ) < point.2 ∧ point.2 < drawing.gridSize :=
      ⟨lt_of_le_of_ne inside.2.2.1 (Ne.symm bottom),lt_of_le_of_ne inside.2.2.2 top⟩
    apply contact_exists_of_real_interior widthPositive heightPositive
      (by simpa using corners false false spans) (by simpa using corners false true spans)
      (by simpa using corners true false spans) (by simpa using corners true true spans)
      (x := (point.1 : ℝ)) (y := (point.2 : ℝ))
    · exact ⟨by exact_mod_cast inside.2.1.1,by exact_mod_cast inside.2.1.2⟩
    · exact ⟨by exact_mod_cast strictHeight.1,by exact_mod_cast strictHeight.2⟩
    · exact_mod_cast inside.1
  obtain ⟨contactPoint,contact⟩ := contactExists
  obtain ⟨key,valid,parent,_⟩ := rational_rectangle_contact_retained planar straight member edgeLocal
    cell column columnBound contactPoint spans contact
  obtain ⟨first,last,lookup,_,_⟩ := rectangleChordFamily_covers_port planar graphLocal straight column columnBound valid
  exact ⟨first,last,by simpa only [parent] using lookup⟩

end LeanTrominoes.PeriodicGridDrawing
