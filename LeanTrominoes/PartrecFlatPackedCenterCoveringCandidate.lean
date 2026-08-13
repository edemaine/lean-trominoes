import LeanTrominoes.PartrecFlatPackedCenterCandidate
import LeanTrominoes.PartrecPackedCenterCoveringCandidate

/-!
# Flat packed center-covering candidates

Every placement covering the center target is determined by a square symmetry
and one of the tromino's three source cells.  This file constructs the flat
assignment lookup for one such pair and proves that it tests exactly whether
the corresponding covering placement is active.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Assemble the flat assignment-lookup input for one covering placement
candidate from the shared center-base input. -/
def flatPackedCenterCoveringAssignmentArgumentsCode
    (symmetry : SquareSymmetry) (source : Cell) : Code :=
  (flatPackedTargetMembershipLookupArgumentsCode
    (packedCoveringColumn symmetry source)
    (-(symmetry.act source).2)).comp flatPackedCenterSourceInputCode

@[simp]
theorem flatPackedCenterCoveringAssignmentArgumentsCode_eval
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (flatPackedCenterCoveringAssignmentArgumentsCode
        symmetry source).eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure
        ([periodicStrip.motif.length,
            (packedCoveringColumn symmetry source).val,
            Encodable.encode (packedCenterCoveringTarget
              periodicStrip packed base symmetry source).1,
            Encodable.encode (packedCenterCoveringTarget
              periodicStrip packed base symmetry source).2,
            packed.assignmentWord] ++
          periodicStrip.motif.flatMap
            PeriodicStripFlatEncoding.cellFields) := by
  have sourceInput := flatPackedCenterSourceInputCode_eval
    periodicStrip packed base
  have targetInput := flatPackedTargetMembershipLookupArgumentsCode_eval
    (packedCoveringColumn symmetry source)
    (-(symmetry.act source).2)
    periodicStrip.period packed.phase periodicStrip.motif
    packed.assignmentWord base.2
  let x := packedColumnPhaseNumerator periodicStrip.period
    packed.phase (packedCoveringColumn symmetry source).val %
      periodicStrip.period
  have run :
      (flatPackedCenterCoveringAssignmentArgumentsCode
          symmetry source).eval
          (flatPackedCenterCandidateInput periodicStrip packed base) =
        pure
          ([periodicStrip.motif.length,
              (packedCoveringColumn symmetry source).val,
              Encodable.encode (Int.ofNat x),
              Encodable.encode
                (base.2 + -(symmetry.act source).2),
              packed.assignmentWord] ++
            periodicStrip.motif.flatMap
              PeriodicStripFlatEncoding.cellFields) := by
    simpa only [flatPackedCenterCoveringAssignmentArgumentsCode] using
      (comp_eval_pure _ _ _ _ sourceInput).trans targetInput
  rw [run]
  have targetEq :
      ((Int.ofNat x,
        base.2 + -(symmetry.act source).2) : Cell) =
        packedCenterCoveringTarget
          periodicStrip packed base symmetry source := by
    apply Prod.ext
    · simp only [packedCenterCoveringTarget,
        PackedWindowState.columnPhase, x,
        packedColumnPhaseNumerator, packedColumnPhaseSum]
      congr 2
      omega
    · simp only [packedCenterCoveringTarget]
      omega
  rw [← targetEq]

/-- Test whether the covering placement determined by a fixed symmetry/source
pair is selected by the flat packed frontier. -/
def flatPackedCenterCoveringCandidateCode
    (symmetry : SquareSymmetry) (source : Cell) : Code :=
  (flatPackedAssignmentIsCode (some symmetry)).comp
    (flatPackedCenterCoveringAssignmentArgumentsCode symmetry source)

/-- One flat covering-candidate program computes exactly the active-placement
filter predicate. -/
theorem flatPackedCenterCoveringCandidateCode_eval_semantic
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (source : Cell)
    (sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (flatPackedCenterCoveringCandidateCode symmetry source).eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [(decide
        (packed.localAssignment periodicStrip
          (Cell.sub (0, base.2) (symmetry.act source)) =
            some symmetry)).toNat] := by
  let column := packedCoveringColumn symmetry source
  let target := packedCenterCoveringTarget
    periodicStrip packed base symmetry source
  have arguments := flatPackedCenterCoveringAssignmentArgumentsCode_eval
    symmetry source periodicStrip packed base
  have selected := flatPackedAssignmentIsCode_eval_semantic
    (some symmetry) periodicStrip packed column target
  have run :
      (flatPackedCenterCoveringCandidateCode symmetry source).eval
          (flatPackedCenterCandidateInput periodicStrip packed base) =
        pure [(decide
          (packed.assignmentAtCell periodicStrip column target =
            some symmetry)).toNat] := by
    simpa [flatPackedCenterCoveringCandidateCode, column, target] using
      (comp_eval_pure _ _ _ _ arguments).trans selected
  rw [packedCenterCoveringAssignment_eq_local
    tromino symmetry source sourceMember periodicStrip packed base] at run
  exact run

end Turing.ToPartrec.Code
