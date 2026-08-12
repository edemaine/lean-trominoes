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

theorem packedCenterCoveringTarget_eq_targetMembership
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

/-- Workspace envelope for constructing the assignment query associated
with one possible center-covering placement. -/
def packedCenterCoveringAssignmentArgumentsSpaceBound
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  1000000000000000000000000000000000000000000000000000000 *
      (intOffsetAmount (-(symmetry.act source).2) + 1) *
      packedTargetMembershipUnit
        (Code.packedCoveringColumn symmetry source)
        (-(symmetry.act source).2) periodicStrip.period packed.phase
        periodicStrip.motif base.2 packed.assignmentWord +
    1000000000 *
      packedCenterCandidateInputUnit periodicStrip packed base

theorem packedCenterCoveringAssignmentArgumentsCost_le_linear
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterCoveringAssignmentArgumentsCost symmetry source
        periodicStrip packed base ≤
      packedCenterCoveringAssignmentArgumentsSpaceBound symmetry source
        periodicStrip packed base := by
  exact Nat.add_le_add
    (packedTargetMembershipLookupArgumentsCost_le_linear
      (Code.packedCoveringColumn symmetry source)
      (-(symmetry.act source).2) periodicStrip.period packed.phase
      periodicStrip.motif base.2 packed.assignmentWord)
    (packedCenterSourceInputCost_le_linear periodicStrip packed base)

def packedCenterCoveringAssignmentArgumentsLinearCoefficient : Nat :=
  packedCenterSourceInsideLinearCoefficient

theorem packedCenterCoveringAssignmentArgumentsSpaceBound_le_input
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell)
    (offsetSmall :
      intOffsetAmount (-(symmetry.act source).2) ≤ 4) :
    packedCenterCoveringAssignmentArgumentsSpaceBound symmetry source
        periodicStrip packed base ≤
      packedCenterCoveringAssignmentArgumentsLinearCoefficient *
        packedCenterCandidateInputUnit periodicStrip packed base := by
  have membershipGlobal := packedCenterTargetMembershipUnit_le_input
    (Code.packedCoveringColumn symmetry source)
    (-(symmetry.act source).2) periodicStrip packed base offsetSmall
  have factorBound :
      1000000000000000000000000000000000000000000000000000000 *
          (intOffsetAmount (-(symmetry.act source).2) + 1) ≤
        1000000000000000000000000000000000000000000000000000000 * 5 := by
    exact Nat.mul_le_mul_left _ (by omega)
  have targetGlobal := Nat.mul_le_mul factorBound membershipGlobal
  simp only [packedCenterCoveringAssignmentArgumentsSpaceBound,
    packedCenterCoveringAssignmentArgumentsLinearCoefficient,
    packedCenterSourceInsideLinearCoefficient]
  omega

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

def packedCenterCoveringCandidateSpaceBound
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : Nat :=
  packedAssignmentIsSpaceBound
      (Encodable.encode periodicStrip.motif)
      (Code.packedCoveringColumn symmetry source).val
      (Encodable.encode (Code.packedCenterCoveringTarget
        periodicStrip packed base symmetry source))
      packed.assignmentWord +
    packedCenterCoveringAssignmentArgumentsSpaceBound
      symmetry source periodicStrip packed base

theorem packedCenterCoveringCandidateCost_le_linear
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterCoveringCandidateCost symmetry source
        periodicStrip packed base ≤
      packedCenterCoveringCandidateSpaceBound symmetry source
        periodicStrip packed base := by
  exact Nat.add_le_add
    (packedAssignmentIsCost_le_linear (some symmetry)
      periodicStrip.motif
      (Code.packedCoveringColumn symmetry source).val
      (Code.packedCenterCoveringTarget
        periodicStrip packed base symmetry source)
      packed.assignmentWord)
    (packedCenterCoveringAssignmentArgumentsCost_le_linear
      symmetry source periodicStrip packed base)

/-- Uniform coefficient for one fixed covering-placement candidate. -/
def packedCenterCoveringCandidateLinearCoefficient : Nat :=
  10000000000000000 * 100000000000000000000000000 +
    packedCenterCoveringAssignmentArgumentsLinearCoefficient

set_option maxRecDepth 100000 in
theorem packedCenterCoveringCandidateSpaceBound_le_input
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell)
    (offsetSmall :
      intOffsetAmount (-(symmetry.act source).2) ≤ 4) :
    packedCenterCoveringCandidateSpaceBound symmetry source
        periodicStrip packed base ≤
      packedCenterCoveringCandidateLinearCoefficient *
        packedCenterCandidateInputUnit periodicStrip packed base := by
  let column := Code.packedCoveringColumn symmetry source
  let offset := -(symmetry.act source).2
  let motifCode := Encodable.encode periodicStrip.motif
  let targetCode := Encodable.encode (Code.packedCenterCoveringTarget
    periodicStrip packed base symmetry source)
  let word := packed.assignmentWord
  have assignment := packedAssignmentIsSpaceBound_le_lookupSpaceBound
    motifCode column.val targetCode word
  have lookupLe :
      packedAssignmentLookupSpaceBound motifCode column.val targetCode word ≤
        packedTargetMembershipUnit column offset periodicStrip.period
          packed.phase periodicStrip.motif base.2 word := by
    simp only [packedTargetMembershipUnit]
    simp only [column, offset, motifCode, targetCode, word,
      packedCenterCoveringTarget_eq_targetMembership]
    omega
  have membership := packedCenterTargetMembershipUnit_le_input
    column offset periodicStrip packed base (by simpa [offset] using offsetSmall)
  have assignmentMembership := assignment.trans
    (Nat.mul_le_mul_left _ lookupLe)
  have assignmentGlobal := assignmentMembership.trans
    (Nat.mul_le_mul_left _ membership)
  have arguments :=
    packedCenterCoveringAssignmentArgumentsSpaceBound_le_input
      symmetry source periodicStrip packed base offsetSmall
  have assignmentGlobal' :
      packedAssignmentIsSpaceBound
          (Encodable.encode periodicStrip.motif)
          (Code.packedCoveringColumn symmetry source).val
          (Encodable.encode (Code.packedCenterCoveringTarget
            periodicStrip packed base symmetry source))
          packed.assignmentWord ≤
        (10000000000000000 *
          100000000000000000000000000) *
          packedCenterCandidateInputUnit periodicStrip packed base := by
    simpa only [column, motifCode, targetCode, word,
      Nat.mul_assoc] using assignmentGlobal
  change
    packedAssignmentIsSpaceBound
          (Encodable.encode periodicStrip.motif)
          (Code.packedCoveringColumn symmetry source).val
          (Encodable.encode (Code.packedCenterCoveringTarget
            periodicStrip packed base symmetry source))
          packed.assignmentWord +
        packedCenterCoveringAssignmentArgumentsSpaceBound symmetry source
          periodicStrip packed base ≤
      packedCenterCoveringCandidateLinearCoefficient *
        packedCenterCandidateInputUnit periodicStrip packed base
  calc
    _ ≤ (10000000000000000 *
            100000000000000000000000000) *
          packedCenterCandidateInputUnit periodicStrip packed base +
        packedCenterCoveringAssignmentArgumentsLinearCoefficient *
          packedCenterCandidateInputUnit periodicStrip packed base :=
      Nat.add_le_add assignmentGlobal' arguments
    _ = (10000000000000000 *
            100000000000000000000000000 +
          packedCenterCoveringAssignmentArgumentsLinearCoefficient) *
        packedCenterCandidateInputUnit periodicStrip packed base := by ring
    _ = _ := rfl

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
