/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineScaledEndpointTrimSimple
import LeanTrominoes.GridPolylineRealSimpleEndpointIndices
import LeanTrominoes.GridSegmentScaledEndpointTrimContacts
import LeanTrominoes.GridSegmentRealScaledNeighborhood
import LeanTrominoes.DegreeThreeVertexNormalizationFans

/-! # A trimmed route reaches a vertex box only at its boundary midpoint -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

theorem clippedScaledRoute_neighborhood_contact {route : List Cell} (simple : IsRealSimple route)
    (orthogonal : OrthogonalPolyline route) {anchor : Cell}
    (vertexAvoidance : RealContains route (realCell anchor) → RealIsEndpoint route (realCell anchor))
    {point : ℝ × ℝ}
    (neighborhood : (32 : ℝ)*anchor.1-8 ≤ point.1 ∧ point.1 ≤ (32 : ℝ)*anchor.1+8 ∧
      (32 : ℝ)*anchor.2-8 ≤ point.2 ∧ point.2 ≤ (32 : ℝ)*anchor.2+8)
    (contains : RealContains (clippedScaledRoute route) point) :
    RealIsEndpoint (clippedScaledRoute route) point ∧
      ∃ side : VertexSide, point = realCell (Cell.add (Cell.scale 32 anchor) (Cell.scale 8 side.direction.step)) := by
  obtain ⟨segment,member,contains⟩ := contains
  obtain ⟨index,equal⟩ := List.mem_iff_get.mp member
  have indexed : (segment,index.val) ∈ (gridPolylineSegments (clippedScaledRoute route)).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_some_iff]
    exact ⟨index.isLt,equal⟩
  obtain ⟨original,originalMember,indexEq,piece⟩ := clippedScaledRoute_piece_has_original indexed
  dsimp only [Prod.fst,Prod.snd] at piece indexEq
  have aligned := (orthogonalPolyline_iff_segments _).mp orthogonal original.1
    (List.fst_mem_of_mem_zipIdx originalMember)
  have parentContains := GridSegment.trimScaled_realContains_parent aligned
    (firstTrimCut_bounds original.2) (lastTrimCut_bounds (gridPolylineSegments route).length original.2)
    (by simpa only [piece] using contains)
  have anchorContained := GridSegment.scaled_neighborhood_contact_implies_incident aligned neighborhood parentContains
  have originalAnchorContains := GridSegment.realContains_of_contains anchorContained
  have endpoint := vertexAvoidance ⟨original.1,List.fst_mem_of_mem_zipIdx originalMember,originalAnchorContains⟩
  have endpointPiece := simple.endpoint_contact_piece endpoint originalMember originalAnchorContains
  have genuine := AxisDirection.between_isGenuine_of_axisAligned aligned
  rcases endpointPiece with ⟨first,anchorEq⟩ | ⟨last,anchorEq⟩
  · have firstCut : firstTrimCut original.2 = 8 := by simp [firstTrimCut,first]
    have trimmedContains : (original.1.trimScaled 8 (lastTrimCut (gridPolylineSegments route).length original.2)).RealContains point := by
      simpa only [piece,firstCut] using contains
    have contact := GridSegment.trimScaled_source_box_contact aligned
      (lastTrimCut_bounds (gridPolylineSegments route).length original.2)
      (by simpa only [anchorEq] using neighborhood) trimmedContains
    have actualContact : point = realCell segment.start := by simpa only [piece,firstCut] using contact
    refine ⟨Or.inl ⟨segment.start,indexed_gridPolylineSegment_head indexed (by omega),actualContact⟩,
      VertexSide.ofDirection (AxisDirection.between original.1.start original.1.finish),?_⟩
    rw [VertexSide.direction_ofDirection _ genuine]
    simpa only [GridSegment.trimScaled,anchorEq] using contact
  · have lastCut : lastTrimCut (gridPolylineSegments route).length original.2 = 8 := by simp [lastTrimCut,last]
    have trimmedContains : (original.1.trimScaled (firstTrimCut original.2) 8).RealContains point := by
      simpa only [piece,lastCut] using contains
    have contact := GridSegment.trimScaled_target_box_contact aligned (firstTrimCut_bounds original.2)
      (by simpa only [anchorEq] using neighborhood) trimmedContains
    have actualContact : point = realCell segment.finish := by simpa only [piece,lastCut] using contact
    have lastIndex : index.val+1 = (gridPolylineSegments (clippedScaledRoute route)).length := by
      have countEq := clippedScaledRoute_segments_length route
      omega
    refine ⟨Or.inr ⟨segment.finish,indexed_gridPolylineSegment_last indexed lastIndex,actualContact⟩,
      VertexSide.ofDirection (AxisDirection.between original.1.start original.1.finish).opposite,?_⟩
    have oppositeGenuine := AxisDirection.opposite_isGenuine genuine
    have oppositeEq := VertexSide.direction_ofDirection _ oppositeGenuine
    rw [oppositeEq]
    have pointEq : (original.1.trimScaled (firstTrimCut original.2) 8).finish =
        Cell.add (Cell.scale 32 anchor) (Cell.scale 8 (AxisDirection.between original.1.start original.1.finish).opposite.step) := by
      cases direction : AxisDirection.between original.1.start original.1.finish <;>
        simp_all [AxisDirection.IsGenuine,GridSegment.trimScaled,AxisDirection.opposite,AxisDirection.step,Cell.add,Cell.scale]
    simpa only [pointEq] using contact

end LeanTrominoes.GridPolyline
