/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirections

/-! # Unary direction blocks for axis-aligned segments -/

namespace LeanTrominoes
namespace Gadget

/-- Four signed coordinate differences encode one directed segment as a
finite cardinal-direction word.  On a genuine axis-aligned segment exactly
one block is nonempty. -/
def segmentDirectionBlock (segment : GridSegment) : List AxisDirection :=
  List.replicate (segment.finish.1 - segment.start.1).toNat .east ++
    List.replicate (segment.finish.2 - segment.start.2).toNat .north ++
    List.replicate (segment.start.1 - segment.finish.1).toNat .west ++
    List.replicate (segment.start.2 - segment.finish.2).toNat .south

/-- The signed-coordinate block is exactly the repeated direction and
lattice length of one genuine axis-aligned segment. -/
theorem segmentDirectionBlock_eq_replicate
    {segment : GridSegment} (aligned : segment.IsAxisAligned) :
    segmentDirectionBlock segment =
      List.replicate
        (AxisDirection.segmentLength segment.start segment.finish)
        (AxisDirection.between segment.start segment.finish) := by
  rcases segment with ⟨⟨startX, startY⟩, ⟨finishX, finishY⟩⟩
  simp only [GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
    GridSegment.IsVertical] at aligned
  rcases aligned with ⟨horizontal, nondegenerate⟩ |
      ⟨vertical, nondegenerate⟩
  · subst finishY
    by_cases forward : startX < finishX
    · have reverse : (startX - finishX).toNat = 0 := by
        exact Int.toNat_of_nonpos (by omega)
      have length : (finishX - startX).natAbs =
          (finishX - startX).toNat := by
        exact Int.ofNat_inj.mp
          ((Int.natAbs_of_nonneg (by omega)).trans
            (Int.toNat_of_nonneg (by omega)).symm)
      have direction :
          AxisDirection.between (startX, startY) (finishX, startY) =
            .east :=
        (AxisDirection.between_eq_east_iff _ _).2 ⟨rfl, forward⟩
      simp [segmentDirectionBlock, AxisDirection.segmentLength,
        direction, reverse, length]
    · have backward : finishX < startX := by omega
      have forwardZero : (finishX - startX).toNat = 0 := by
        exact Int.toNat_of_nonpos (by omega)
      have length : (finishX - startX).natAbs =
          (startX - finishX).toNat := by
        rw [show finishX - startX = -(startX - finishX) by omega,
          Int.natAbs_neg]
        exact Int.ofNat_inj.mp
          ((Int.natAbs_of_nonneg (by omega)).trans
            (Int.toNat_of_nonneg (by omega)).symm)
      have direction :
          AxisDirection.between (startX, startY) (finishX, startY) =
            .west :=
        (AxisDirection.between_eq_west_iff _ _).2 ⟨rfl, backward⟩
      simp [segmentDirectionBlock, AxisDirection.segmentLength,
        direction, forwardZero, length]
  · subst finishX
    by_cases forward : startY < finishY
    · have reverse : (startY - finishY).toNat = 0 := by
        exact Int.toNat_of_nonpos (by omega)
      have length : (finishY - startY).natAbs =
          (finishY - startY).toNat := by
        exact Int.ofNat_inj.mp
          ((Int.natAbs_of_nonneg (by omega)).trans
            (Int.toNat_of_nonneg (by omega)).symm)
      have direction :
          AxisDirection.between (startX, startY) (startX, finishY) =
            .north :=
        (AxisDirection.between_eq_north_iff _ _).2 ⟨rfl, forward⟩
      simp [segmentDirectionBlock, AxisDirection.segmentLength,
        direction, reverse, length]
    · have backward : finishY < startY := by omega
      have forwardZero : (finishY - startY).toNat = 0 := by
        exact Int.toNat_of_nonpos (by omega)
      have length : (finishY - startY).natAbs =
          (startY - finishY).toNat := by
        rw [show finishY - startY = -(startY - finishY) by omega,
          Int.natAbs_neg]
        exact Int.ofNat_inj.mp
          ((Int.natAbs_of_nonneg (by omega)).trans
            (Int.toNat_of_nonneg (by omega)).symm)
      have direction :
          AxisDirection.between (startX, startY) (startX, finishY) =
            .south :=
        (AxisDirection.between_eq_south_iff _ _).2 ⟨rfl, backward⟩
      simp [segmentDirectionBlock, AxisDirection.segmentLength,
        direction, forwardZero, length]

/-- Segmentwise signed-coordinate blocks recover the exact direction word of
any orthogonal polyline. -/
theorem unitSubdivisionDirections_eq_segmentDirectionBlocks
    (points : List Cell)
    (aligned : ∀ segment ∈ gridPolylineSegments points,
      segment.IsAxisAligned) :
    unitSubdivisionDirections points =
      (gridPolylineSegments points).flatMap segmentDirectionBlock := by
  induction points using List.twoStepInduction with
  | nil => simp [unitSubdivisionDirections, gridPolylineSegments]
  | singleton point =>
      simp [unitSubdivisionDirections, gridPolylineSegments]
  | cons_cons first second rest _ induction =>
      have firstAligned :
          (GridSegment.mk first second).IsAxisAligned :=
        aligned _ (by simp [gridPolylineSegments])
      have restAligned : ∀ segment ∈
          gridPolylineSegments (second :: rest), segment.IsAxisAligned := by
        intro segment member
        exact aligned segment
          (by simp [gridPolylineSegments, member])
      simp only [unitSubdivisionDirections, gridPolylineSegments,
        List.flatMap_cons]
      rw [segmentDirectionBlock_eq_replicate firstAligned,
        induction second restAligned]

end Gadget
end LeanTrominoes
