/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteSegmentDirectionBlock
import LeanTrominoes.PeriodicThreeDMContractionPlanarity

/-! # Reversing sparse route direction words -/

namespace LeanTrominoes
namespace Gadget

/-- Traverse a direction word backward. -/
def reverseDirections (directions : List AxisDirection) :
    List AxisDirection :=
  directions.reverse.map AxisDirection.opposite

@[simp] theorem reverseDirections_append
    (first second : List AxisDirection) :
    reverseDirections (first ++ second) =
      reverseDirections second ++ reverseDirections first := by
  simp [reverseDirections]

/-- Manhattan segment length is independent of traversal direction. -/
@[simp] theorem segmentLength_comm (first second : Cell) :
    AxisDirection.segmentLength first second =
      AxisDirection.segmentLength second first := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [AxisDirection.segmentLength]
  rw [show firstX - secondX = -(secondX - firstX) by ring,
    show firstY - secondY = -(secondY - firstY) by ring,
    Int.natAbs_neg, Int.natAbs_neg]

/-- Reversing one genuine axis segment reverses its unary block and flips
every cardinal direction. -/
theorem segmentDirectionBlock_reverse
    (segment : GridSegment) (aligned : segment.IsAxisAligned) :
    segmentDirectionBlock segment.reverse =
      reverseDirections (segmentDirectionBlock segment) := by
  have reverseAligned : segment.reverse.IsAxisAligned := by
    unfold GridSegment.IsAxisAligned GridSegment.IsHorizontal
      GridSegment.IsVertical at aligned
    unfold GridSegment.IsAxisAligned GridSegment.IsHorizontal
      GridSegment.IsVertical GridSegment.reverse
    rcases aligned with ⟨horizontal, nondegenerate⟩ |
        ⟨vertical, nondegenerate⟩
    · exact Or.inl ⟨horizontal.symm, Ne.symm nondegenerate⟩
    · exact Or.inr ⟨vertical.symm, Ne.symm nondegenerate⟩
  rw [segmentDirectionBlock_eq_replicate reverseAligned,
    segmentDirectionBlock_eq_replicate aligned]
  change List.replicate
      (AxisDirection.segmentLength segment.finish segment.start)
      (AxisDirection.between segment.finish segment.start) = _
  rw [segmentLength_comm]
  rw [AxisDirection.between_reverse_eq_opposite
    (AxisDirection.between_isGenuine_of_axisAligned aligned)]
  simp [reverseDirections]

/-- Segment-major blocks commute with reversing a whole aligned segment
list. -/
theorem reversedSegmentDirectionBlocks
    (segments : List GridSegment)
    (aligned : ∀ segment ∈ segments, segment.IsAxisAligned) :
    (segments.reverse.map GridSegment.reverse).flatMap
        segmentDirectionBlock =
      reverseDirections (segments.flatMap segmentDirectionBlock) := by
  induction segments with
  | nil => rfl
  | cons segment segments induction =>
      have segmentAligned : segment.IsAxisAligned :=
        aligned segment (by simp)
      have restAligned : ∀ member ∈ segments, member.IsAxisAligned := by
        intro member memberIn
        exact aligned member (by simp [memberIn])
      simp only [List.reverse_cons, List.map_append, List.map_singleton,
        List.flatMap_append, List.flatMap_cons]
      rw [segmentDirectionBlock_reverse segment segmentAligned,
        induction restAligned]
      simp [reverseDirections_append]

/-- Reversing an orthogonal polyline reverses its complete direction word
and flips every direction. -/
theorem unitSubdivisionDirections_reverse
    (points : List Cell)
    (orthogonal : PeriodicOrthocrossing.OrthogonalPolyline points) :
    unitSubdivisionDirections points.reverse =
      reverseDirections (unitSubdivisionDirections points) := by
  have aligned : ∀ segment ∈ gridPolylineSegments points,
      segment.IsAxisAligned :=
    (PeriodicOrthocrossing.orthogonalPolyline_iff_segments points).mp
      orthogonal
  have reverseOrthogonal := orthogonal.reverse
  have reverseAligned : ∀ segment ∈ gridPolylineSegments points.reverse,
      segment.IsAxisAligned :=
    (PeriodicOrthocrossing.orthogonalPolyline_iff_segments points.reverse).mp
      reverseOrthogonal
  rw [unitSubdivisionDirections_eq_segmentDirectionBlocks
    points.reverse reverseAligned]
  rw [gridPolylineSegments_reverse]
  rw [reversedSegmentDirectionBlocks _ aligned]
  rw [unitSubdivisionDirections_eq_segmentDirectionBlocks points aligned]

end Gadget
end LeanTrominoes
