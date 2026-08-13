import LeanTrominoes.PartrecFlatPackedCenterCoveringCandidate
import LeanTrominoes.PartrecFlatPackedCenterCandidateSpace

/-!
# Evaluator-space certificate for flat packed center-covering candidates

The candidate program reuses the canonical packed target constructor and the
fitted fixed-assignment predicate.  This file records the exact composition
cost and its semantic fitted execution.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

set_option maxRecDepth 1000000
set_option maxHeartbeats 2000000

def flatPackedCenterCoveringAssignmentArgumentsCost
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedTargetMembershipLookupArgumentsCost
      (Code.packedCoveringColumn symmetry source)
      (-(symmetry.act source).2)
      periodicStrip.period packed.phase periodicStrip.motif
      base.2 packed.assignmentWord +
    flatPackedCenterSourceInputCost periodicStrip packed base

theorem flatPackedCenterCoveringAssignmentArguments
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterCoveringAssignmentArgumentsCode
        symmetry source)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      ([periodicStrip.motif.length,
          (Code.packedCoveringColumn symmetry source).val,
          Encodable.encode (Code.packedCenterCoveringTarget
            periodicStrip packed base symmetry source).1,
          Encodable.encode (Code.packedCenterCoveringTarget
            periodicStrip packed base symmetry source).2,
          packed.assignmentWord] ++
        periodicStrip.motif.flatMap
          PeriodicStripFlatEncoding.cellFields)
      (flatPackedCenterCoveringAssignmentArgumentsCost
        symmetry source periodicStrip packed base) := by
  have target := flatPackedTargetMembershipLookupArguments
    (Code.packedCoveringColumn symmetry source)
    (-(symmetry.act source).2)
    periodicStrip.period packed.phase periodicStrip.motif
    base.2 packed.assignmentWord
  have result :=
    comp target (flatPackedCenterSourceInput periodicStrip packed base)
  let x := Code.packedColumnPhaseNumerator periodicStrip.period
    packed.phase (Code.packedCoveringColumn symmetry source).val %
      periodicStrip.period
  have targetEq :
      ((Int.ofNat x,
        base.2 + -(symmetry.act source).2) : Cell) =
        Code.packedCenterCoveringTarget
          periodicStrip packed base symmetry source := by
    apply Prod.ext
    · simp only [Code.packedCenterCoveringTarget,
        PackedWindowState.columnPhase, x,
        Code.packedColumnPhaseNumerator,
        Code.packedColumnPhaseSum]
      congr 2
      omega
    · simp only [Code.packedCenterCoveringTarget]
      omega
  rw [targetEq] at result
  have encodedX : Encodable.encode
      (Code.packedCenterCoveringTarget periodicStrip packed base symmetry
        source).1 = 2 * x := by
    rw [← targetEq]
    rfl
  rw [encodedX]
  simpa [Code.flatPackedCenterCoveringAssignmentArgumentsCode,
    flatPackedCenterCoveringAssignmentArgumentsCost] using result

theorem flatPackedCenterCoveringTarget_eq_targetMembership
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    Code.packedCenterCoveringTarget
        periodicStrip packed base symmetry source =
      (Int.ofNat
          (Code.packedColumnPhaseNumerator periodicStrip.period
            packed.phase (Code.packedCoveringColumn symmetry source).val %
            periodicStrip.period),
        base.2 + -(symmetry.act source).2) := by
  apply Prod.ext
  · simp only [Code.packedCenterCoveringTarget,
      PackedWindowState.columnPhase,
      Code.packedColumnPhaseNumerator, Code.packedColumnPhaseSum]
    congr 2
    omega
  · simp only [Code.packedCenterCoveringTarget]
    omega

def flatPackedCenterCoveringCandidateCost
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedAssignmentIsCost (some symmetry) periodicStrip.motif
      (Code.packedCoveringColumn symmetry source).val
      (Code.packedCenterCoveringTarget
        periodicStrip packed base symmetry source)
      packed.assignmentWord +
    flatPackedCenterCoveringAssignmentArgumentsCost
      symmetry source periodicStrip packed base

def flatPackedCenterCoveringCandidateSpaceBound
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  flatPackedAssignmentPredicateSpaceBound periodicStrip.motif
      (Code.packedCoveringColumn symmetry source).val
      (Code.packedCenterCoveringTarget
        periodicStrip packed base symmetry source)
      packed.assignmentWord +
    flatPackedCenterCoveringAssignmentArgumentsCost
      symmetry source periodicStrip packed base

theorem flatPackedCenterCoveringCandidateCost_le_bound
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterCoveringCandidateCost symmetry source
        periodicStrip packed base ≤
      flatPackedCenterCoveringCandidateSpaceBound symmetry source
        periodicStrip packed base := by
  exact Nat.add_le_add_right
    (flatPackedAssignmentIsCost_le_bound (some symmetry)
      periodicStrip.motif
      (Code.packedCoveringColumn symmetry source).val
      (Code.packedCenterCoveringTarget
        periodicStrip packed base symmetry source)
      packed.assignmentWord)
    _

/-- Exact fitted execution of one active covering-placement test. -/
theorem flatPackedCenterCoveringCandidate
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (source : Cell)
    (sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.flatPackedCenterCoveringCandidateCode symmetry source)
      (Code.flatPackedCenterCandidateInput periodicStrip packed base)
      [(decide
        (packed.localAssignment periodicStrip
          (Cell.sub (0, base.2) (symmetry.act source)) =
            some symmetry)).toNat]
      (flatPackedCenterCoveringCandidateCost symmetry source
        periodicStrip packed base) := by
  have selected := flatPackedAssignmentIs_semantic
    (some symmetry) periodicStrip packed
    (Code.packedCoveringColumn symmetry source)
    (Code.packedCenterCoveringTarget
      periodicStrip packed base symmetry source)
  have result := comp selected
    (flatPackedCenterCoveringAssignmentArguments
      symmetry source periodicStrip packed base)
  rw [Code.packedCenterCoveringAssignment_eq_local
    tromino symmetry source sourceMember periodicStrip packed base] at result
  simpa [Code.flatPackedCenterCoveringCandidateCode,
    flatPackedCenterCoveringCandidateCost] using result

end EvaluatorCodeFits

end PartrecToTM2
end Turing
