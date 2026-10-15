/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineScaledEndpointTrim
import LeanTrominoes.Common.Geometry.GridPolylineRealAffineSimplicity

/-! # Trimming opens simple loops and preserves simplicity -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

theorem firstTrimCut_bounds (index : Nat) : 0 ≤ firstTrimCut index ∧ firstTrimCut index ≤ 8 := by
  unfold firstTrimCut
  split <;> norm_num

theorem lastTrimCut_bounds (count index : Nat) : 0 ≤ lastTrimCut count index ∧ lastTrimCut count index ≤ 8 := by
  unfold lastTrimCut
  split <;> norm_num

theorem realPoint_eq_scaledCell_of_div_eq {factor : Int} (nonzero : factor ≠ 0) {point : ℝ × ℝ} {cell : Cell}
    (equal : (point.1/(factor : ℝ),point.2/(factor : ℝ)) = realCell cell) : point = realCell (Cell.scale factor cell) := by
  have realNonzero : (factor : ℝ) ≠ 0 := by exact_mod_cast nonzero
  have hx := congrArg Prod.fst equal
  have hy := congrArg Prod.snd equal
  apply Prod.ext
  · simpa [realCell,Cell.scale,mul_comm] using (div_eq_iff realNonzero).mp hx
  · simpa [realCell,Cell.scale,mul_comm] using (div_eq_iff realNonzero).mp hy

theorem clippedScaledRoute_isRealOpenSimple {route : List Cell} (simple : IsRealSimple route)
    (orthogonal : OrthogonalPolyline route) : IsRealOpenSimple (clippedScaledRoute route) := by
  have aligned {tagged : GridSegment × Nat} (member : tagged ∈ (gridPolylineSegments route).zipIdx) :
      tagged.1.IsAxisAligned :=
    (orthogonalPolyline_iff_segments _).mp orthogonal tagged.1 (List.fst_mem_of_mem_zipIdx member)
  have childAligned {tagged : GridSegment × Nat}
      (member : tagged ∈ (gridPolylineSegments (clippedScaledRoute route)).zipIdx) : tagged.1.IsAxisAligned := by
    obtain ⟨original,originalMember,_,piece⟩ := clippedScaledRoute_piece_has_original member
    rw [piece]
    exact (GridSegment.trimScaled_geometry (aligned originalMember)
      (firstTrimCut_bounds _) (lastTrimCut_bounds _ _)).1
  refine ⟨by simpa [clippedScaledRoute_length] using simple.1,?_,?_⟩
  · intro segment member
    obtain ⟨index,equal⟩ := List.mem_iff_get.mp member
    have indexed : (segment,index.val) ∈ (gridPolylineSegments (clippedScaledRoute route)).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff]
      exact ⟨index.isLt,equal⟩
    rcases childAligned indexed with horizontal | vertical
    · intro equal
      exact horizontal.2 (congrArg Prod.fst equal)
    · intro equal
      exact vertical.2 (congrArg Prod.snd equal)
  · intro first firstMember second secondMember ordered point firstContains secondContains
    obtain ⟨a,am,aIndex,aPiece⟩ := clippedScaledRoute_piece_has_original firstMember
    obtain ⟨b,bm,bIndex,bPiece⟩ := clippedScaledRoute_piece_has_original secondMember
    have firstParent : (a.1.scale 32).RealContains point := by
      apply GridSegment.trimScaled_realContains_parent (aligned am) (firstTrimCut_bounds _) (lastTrimCut_bounds _ _)
      simpa only [aPiece] using firstContains
    have secondParent : (b.1.scale 32).RealContains point := by
      apply GridSegment.trimScaled_realContains_parent (aligned bm) (firstTrimCut_bounds _) (lastTrimCut_bounds _ _)
      simpa only [bPiece] using secondContains
    have sourceOrder : a.2 < b.2 := by omega
    have contact := simple.2.2 a am b bm sourceOrder (point.1/(32 : Int),point.2/(32 : Int))
      ((GridSegment.realContains_scale_inverse _ (by norm_num : (32 : Int) ≠ 0) _).mp firstParent)
      ((GridSegment.realContains_scale_inverse _ (by norm_num : (32 : Int) ≠ 0) _).mp secondParent)
    rcases contact with adjacent | closed
    · have bBound := List.snd_lt_of_mem_zipIdx bm
      have firstNotLast : a.2+1 ≠ (gridPolylineSegments route).length := by omega
      have finish : first.1.finish = Cell.scale 32 a.1.finish := by
        rw [aPiece]
        simp [GridSegment.trimScaled,lastTrimCut,firstNotLast,Cell.add,Cell.scale]
      refine ⟨by omega,?_⟩
      rw [finish]
      exact realPoint_eq_scaledCell_of_div_eq (by norm_num : (32 : Int) ≠ 0) adjacent.2
    · have atStart := realPoint_eq_scaledCell_of_div_eq (by norm_num : (32 : Int) ≠ 0) closed.2.2.1
      have avoids := GridSegment.trimScaled_avoids_start (aligned am)
        (by norm_num : (0 : Int) < 8 ∧ (8 : Int) ≤ 8) (lastTrimCut_bounds (gridPolylineSegments route).length a.2)
      apply False.elim
      apply avoids
      rw [← atStart]
      simpa only [aPiece,firstTrimCut,closed.1,ite_true] using firstContains

theorem clippedScaledRoute_orthogonal {route : List Cell} (orthogonal : OrthogonalPolyline route) :
    OrthogonalPolyline (clippedScaledRoute route) := by
  apply (orthogonalPolyline_iff_segments _).mpr
  intro segment member
  obtain ⟨index,equal⟩ := List.mem_iff_get.mp member
  have indexed : (segment,index.val) ∈ (gridPolylineSegments (clippedScaledRoute route)).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff]
    exact ⟨index.isLt,equal⟩
  obtain ⟨original,originalMember,_,piece⟩ := clippedScaledRoute_piece_has_original indexed
  dsimp only [Prod.fst] at piece
  rw [piece]
  exact (GridSegment.trimScaled_geometry
    ((orthogonalPolyline_iff_segments _).mp orthogonal _ (List.fst_mem_of_mem_zipIdx originalMember))
    (firstTrimCut_bounds _) (lastTrimCut_bounds _ _)).1

theorem clippedScaledRoute_realContains_source {route : List Cell} (orthogonal : OrthogonalPolyline route)
    {point : ℝ × ℝ} (contains : RealContains (clippedScaledRoute route) point) :
    RealContains (scalePolyline 32 route) point := by
  obtain ⟨segment,member,contains⟩ := contains
  obtain ⟨index,equal⟩ := List.mem_iff_get.mp member
  have indexed : (segment,index.val) ∈ (gridPolylineSegments (clippedScaledRoute route)).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff]
    exact ⟨index.isLt,equal⟩
  obtain ⟨original,originalMember,_,piece⟩ := clippedScaledRoute_piece_has_original indexed
  dsimp only [Prod.fst] at piece
  rw [piece] at contains
  refine ⟨original.1.scale 32,?_,?_⟩
  · rw [gridPolylineSegments_scalePolyline]
    exact List.mem_map.mpr ⟨original.1,List.fst_mem_of_mem_zipIdx originalMember,rfl⟩
  · exact GridSegment.trimScaled_realContains_parent
      ((orthogonalPolyline_iff_segments _).mp orthogonal _ (List.fst_mem_of_mem_zipIdx originalMember))
      (firstTrimCut_bounds _) (lastTrimCut_bounds _ _) contains

end LeanTrominoes.GridPolyline
