import LeanTrominoes.PartrecPackedCenterCoveringCandidate
import LeanTrominoes.PartrecPackedCenterCandidateSpace

/-!
# Evaluator-space certificate for packed center-covering candidates

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

def packedCenterCoveringAssignmentArgumentsCost
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedTargetMembershipLookupArgumentsCost
      (Code.packedCoveringColumn symmetry source)
      (-(symmetry.act source).2)
      periodicStrip.period packed.phase periodicStrip.motif
      base.2 packed.assignmentWord +
    packedCenterSourceInputCost periodicStrip packed base

theorem packedCenterCoveringAssignmentArguments
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.packedCenterCoveringAssignmentArgumentsCode
        symmetry source)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [Encodable.encode periodicStrip.motif,
        (Code.packedCoveringColumn symmetry source).val,
        Encodable.encode (Code.packedCenterCoveringTarget
          periodicStrip packed base symmetry source),
        packed.assignmentWord]
      (packedCenterCoveringAssignmentArgumentsCost
        symmetry source periodicStrip packed base) := by
  have target := packedTargetMembershipLookupArguments
    (Code.packedCoveringColumn symmetry source)
    (-(symmetry.act source).2)
    periodicStrip.period packed.phase periodicStrip.motif
    base.2 packed.assignmentWord
  have result :=
    comp target (packedCenterSourceInput periodicStrip packed base)
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
  simpa only [Code.packedCenterCoveringAssignmentArgumentsCode,
    packedCenterCoveringAssignmentArgumentsCost] using result

def packedCenterCoveringCandidateCost
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedAssignmentIsCost (some symmetry) periodicStrip.motif
      (Code.packedCoveringColumn symmetry source).val
      (Code.packedCenterCoveringTarget
        periodicStrip packed base symmetry source)
      packed.assignmentWord +
    packedCenterCoveringAssignmentArgumentsCost
      symmetry source periodicStrip packed base

/-- Exact fitted execution of one active covering-placement test. -/
theorem packedCenterCoveringCandidate
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (source : Cell)
    (sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    EvaluatorCodeFits
      (Code.packedCenterCoveringCandidateCode symmetry source)
      (Code.packedCenterCandidateInput periodicStrip packed base)
      [(decide
        (packed.localAssignment periodicStrip
          (Cell.sub (0, base.2) (symmetry.act source)) =
            some symmetry)).toNat]
      (packedCenterCoveringCandidateCost symmetry source
        periodicStrip packed base) := by
  have selected := packedAssignmentIs_semantic
    (some symmetry) periodicStrip packed
    (Code.packedCoveringColumn symmetry source)
    (Code.packedCenterCoveringTarget
      periodicStrip packed base symmetry source)
  have result := comp selected
    (packedCenterCoveringAssignmentArguments
      symmetry source periodicStrip packed base)
  rw [Code.packedCenterCoveringAssignment_eq_local
    tromino symmetry source sourceMember periodicStrip packed base] at result
  simpa [Code.packedCenterCoveringCandidateCode,
    packedCenterCoveringCandidateCost] using result

end EvaluatorCodeFits

end PartrecToTM2
end Turing
