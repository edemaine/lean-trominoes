/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackSuffixDirectionCompilerData
import LeanTrominoes.GadgetSparseRouteUnitSubdivisionDirectionEndpointJoin
import LeanTrominoes.RetainedAngularFanOuterRadialDecomposition
import LeanTrominoes.RetainedRayRasterizationTranslation

/-! # Direction words of repeated inward retained rays -/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace FallbackSuffixDirectionCompiler

open PeriodicOrthocrossing

private theorem diagonalDirections
    (horizontal vertical : Int) (count : Nat) (start : Cell) :
    Gadget.unitSubdivisionDirections
        (diagonalStaircase horizontal vertical count start) =
      (List.replicate count
        (Gadget.unitSubdivisionDirections
          (diagonalStaircase horizontal vertical 1 (0, 0)))).flatten := by
  induction count generalizing start with
  | zero =>
      simp [diagonalStaircase, Gadget.unitSubdivisionDirections]
  | succ count induction =>
      rw [diagonalStaircase_split_last]
      rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
      · rw [induction]
        have translated := diagonalStaircase_translatePolyline
          horizontal vertical 1 (0, 0)
          (Cell.add start (Cell.scale count (horizontal, vertical)))
        simp only [Cell.add_zero] at translated
        rw [← translated,
          Gadget.unitSubdivisionDirections_translatePolyline]
        simp [List.replicate_succ']
      · intro empty
        have head := diagonalStaircase_head?
          horizontal vertical count start
        simp [empty] at head
      · rw [diagonalStaircase_getLast?, diagonalStaircase_head?]

private theorem routedDirections
    (arm : PlanarThreeSAT.DuplicatorArm)
    (count : Nat) (start : Cell) :
    Gadget.unitSubdivisionDirections (routedClauseRay arm count start) =
      (List.replicate count
        (Gadget.unitSubdivisionDirections
          (routedClauseRay arm 1 (0, 0)))).flatten := by
  induction count generalizing start with
  | zero =>
      simp [routedClauseRay, Gadget.unitSubdivisionDirections]
  | succ count induction =>
      rw [routedClauseRay_split_last]
      rw [Gadget.unitSubdivisionDirections_joinAtEndpoint]
      · rw [induction]
        have translated := routedClauseRay_translatePolyline
          arm 1 (0, 0)
          (Cell.add start
            (Cell.scale count (routedClauseRayPrimitive arm)))
        simp only [Cell.add_zero] at translated
        rw [← translated,
          Gadget.unitSubdivisionDirections_translatePolyline]
        simp [List.replicate_succ']
      · intro empty
        have head := routedClauseRay_head? arm count start
        simp [empty] at head
      · rw [routedClauseRay_getLast?, routedClauseRay_head?]

private theorem compassNorthDirections (count : Nat) (start : Cell) :
    Gadget.unitSubdivisionDirections (compassRay .north count start) =
      (List.replicate count
        (Gadget.unitSubdivisionDirections
          (compassRay .north 1 (0, 0)))).flatten := by
  rcases start with ⟨x, y⟩
  cases count with
  | zero =>
      simp [compassRay, Gadget.unitSubdivisionDirections]
  | succ count =>
      simp [compassRay, Gadget.unitSubdivisionDirections,
        AxisDirection.segmentLength, AxisDirection.between,
        OccurrenceSplitRing.Port.unitVector, Cell.add, Cell.scale]
      have negative : -1 + -(count : Int) < 0 := by omega
      constructor
      · exact Int.ofNat_inj.mp (by
          rw [Int.ofNat_natAbs_of_nonpos negative.le]
          omega)
      · right
        have notLow : ¬(count : Int) < -1 := by omega
        have high : (-1 : Int) < count := by omega
        simp [notLow, high, negative.ne]

private theorem compassEastDirections (count : Nat) (start : Cell) :
    Gadget.unitSubdivisionDirections (compassRay .east count start) =
      (List.replicate count
        (Gadget.unitSubdivisionDirections
          (compassRay .east 1 (0, 0)))).flatten := by
  rcases start with ⟨x, y⟩
  cases count with
  | zero =>
      simp [compassRay, Gadget.unitSubdivisionDirections]
  | succ count =>
      simp [compassRay, Gadget.unitSubdivisionDirections,
        AxisDirection.segmentLength, AxisDirection.between,
        OccurrenceSplitRing.Port.unitVector, Cell.add, Cell.scale]
      omega

private theorem compassSouthDirections (count : Nat) (start : Cell) :
    Gadget.unitSubdivisionDirections (compassRay .south count start) =
      (List.replicate count
        (Gadget.unitSubdivisionDirections
          (compassRay .south 1 (0, 0)))).flatten := by
  rcases start with ⟨x, y⟩
  cases count with
  | zero =>
      simp [compassRay, Gadget.unitSubdivisionDirections]
  | succ count =>
      simp [compassRay, Gadget.unitSubdivisionDirections,
        AxisDirection.segmentLength, AxisDirection.between,
        OccurrenceSplitRing.Port.unitVector, Cell.add, Cell.scale]
      omega

private theorem compassWestDirections (count : Nat) (start : Cell) :
    Gadget.unitSubdivisionDirections (compassRay .west count start) =
      (List.replicate count
        (Gadget.unitSubdivisionDirections
          (compassRay .west 1 (0, 0)))).flatten := by
  rcases start with ⟨x, y⟩
  cases count with
  | zero =>
      simp [compassRay, Gadget.unitSubdivisionDirections]
  | succ count =>
      simp [compassRay, Gadget.unitSubdivisionDirections,
        AxisDirection.segmentLength, AxisDirection.between,
        OccurrenceSplitRing.Port.unitVector, Cell.add, Cell.scale]
      have negative : -1 + -(count : Int) < 0 := by omega
      constructor
      · exact Int.ofNat_inj.mp (by
          rw [Int.ofNat_natAbs_of_nonpos negative.le]
          omega)
      · right
        have notLow : ¬(count : Int) < -1 := by omega
        have high : (-1 : Int) < count := by omega
        simp [notLow, high]

/-- Rasterizing any number of primitive inward retained-ray steps produces
exactly that many copies of its one-step direction word. -/
theorem retainedTerminalFanOuterInwardRayOfLength_directions
    (direction : RetainedTerminalDirection)
    (count : Nat) (start : Cell) :
    Gadget.unitSubdivisionDirections
        ((retainedTerminalFanOuterInwardRayOfLength
          direction count).rasterize start) =
      radialCopies count direction := by
  cases direction with
  | compass port =>
      cases port with
      | northwest =>
          simpa [retainedTerminalFanOuterInwardRayOfLength,
            RetainedRay.rasterize, radialCopies,
            inwardRayUnitDirections, oppositePort] using
            diagonalDirections 1 1 count start
      | north =>
          simpa [retainedTerminalFanOuterInwardRayOfLength,
            RetainedRay.rasterize, radialCopies,
            inwardRayUnitDirections, oppositePort] using
            compassSouthDirections count start
      | northeast =>
          simpa [retainedTerminalFanOuterInwardRayOfLength,
            RetainedRay.rasterize, radialCopies,
            inwardRayUnitDirections, oppositePort] using
            diagonalDirections (-1) 1 count start
      | east =>
          simpa [retainedTerminalFanOuterInwardRayOfLength,
            RetainedRay.rasterize, radialCopies,
            inwardRayUnitDirections, oppositePort] using
            compassWestDirections count start
      | southeast =>
          simpa [retainedTerminalFanOuterInwardRayOfLength,
            RetainedRay.rasterize, radialCopies,
            inwardRayUnitDirections, oppositePort] using
            diagonalDirections (-1) (-1) count start
      | south =>
          simpa [retainedTerminalFanOuterInwardRayOfLength,
            RetainedRay.rasterize, radialCopies,
            inwardRayUnitDirections, oppositePort] using
            compassNorthDirections count start
      | southwest =>
          simpa [retainedTerminalFanOuterInwardRayOfLength,
            RetainedRay.rasterize, radialCopies,
            inwardRayUnitDirections, oppositePort] using
            diagonalDirections 1 (-1) count start
      | west =>
          simpa [retainedTerminalFanOuterInwardRayOfLength,
            RetainedRay.rasterize, radialCopies,
            inwardRayUnitDirections, oppositePort] using
            compassEastDirections count start
  | routedClause arm =>
      simpa [retainedTerminalFanOuterInwardRayOfLength,
        RetainedRay.rasterize, radialCopies,
        inwardRayUnitDirections] using
        routedDirections arm count start

end FallbackSuffixDirectionCompiler
end PeriodicEightOccurrenceSplit
end LeanTrominoes
