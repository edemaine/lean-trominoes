import LeanTrominoes.PartrecPackedCenterCandidate

/-!
# Packed center-covering candidates

Every placement covering the center target is determined by a square symmetry
and one of the tromino's three source cells.  This file constructs the packed
assignment lookup for one such pair and proves that it tests exactly whether
the corresponding covering placement is active.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip
open LeanTrominoes.PeriodicStrip.RawWindowState

attribute [local simp] Part.bind_eq_bind

private theorem comp_eval_pure
    (outer inner : Code) (input output : List Nat)
    (innerCorrect : inner.eval input = pure output) :
    (outer.comp inner).eval input = outer.eval output := by
  simp [innerCorrect, Part.bind_eq_bind]

/-- Packed window column containing the base of the placement that makes the
transformed source cell cover the center target. -/
def packedCoveringColumn
    (symmetry : SquareSymmetry) (source : Cell) : WindowColumn :=
  ⟨((-(symmetry.act source).1 + 2).toNat % 5),
    Nat.mod_lt _ (by omega)⟩

theorem packedCoveringColumn_displacement
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (source : Cell)
    (sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino) :
    (packedCoveringColumn symmetry source).displacement =
      -(symmetry.act source).1 := by
  cases tromino <;> cases symmetry <;>
    simp [TrominoAssignment.trominoCellList] at sourceMember
  all_goals rcases sourceMember with rfl | rfl | rfl <;> native_decide

/-- Canonical motif coordinate queried for one covering-placement base. -/
def packedCenterCoveringTarget
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell)
    (symmetry : SquareSymmetry) (source : Cell) : Cell :=
  let column := packedCoveringColumn symmetry source
  ((packed.columnPhase periodicStrip column : Int),
    base.2 - (symmetry.act source).2)

/-- Assemble the four-field assignment-lookup input for one covering
placement candidate from the shared six-field center-base input. -/
def packedCenterCoveringAssignmentArgumentsCode
    (symmetry : SquareSymmetry) (source : Cell) : Code :=
  (packedTargetMembershipLookupArgumentsCode
    (packedCoveringColumn symmetry source)
    (-(symmetry.act source).2)).comp packedCenterSourceInputCode

@[simp]
theorem packedCenterCoveringAssignmentArgumentsCode_eval
    (symmetry : SquareSymmetry) (source : Cell)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterCoveringAssignmentArgumentsCode
        symmetry source).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [Encodable.encode periodicStrip.motif,
        (packedCoveringColumn symmetry source).val,
        Encodable.encode (packedCenterCoveringTarget
          periodicStrip packed base symmetry source),
        packed.assignmentWord] := by
  have sourceInput := packedCenterSourceInputCode_eval
    periodicStrip packed base
  have targetInput := packedTargetMembershipLookupArgumentsCode_eval
    (packedCoveringColumn symmetry source)
    (-(symmetry.act source).2)
    periodicStrip.period packed.phase periodicStrip.motif
    packed.assignmentWord base.2
  let x := packedColumnPhaseNumerator periodicStrip.period
    packed.phase (packedCoveringColumn symmetry source).val %
      periodicStrip.period
  have run :
      (packedCenterCoveringAssignmentArgumentsCode
          symmetry source).eval
          (packedCenterCandidateInput periodicStrip packed base) =
        pure [Encodable.encode periodicStrip.motif,
          (packedCoveringColumn symmetry source).val,
          Encodable.encode
            ((Int.ofNat x,
              base.2 + -(symmetry.act source).2) : Cell),
          packed.assignmentWord] := by
    simpa only [packedCenterCoveringAssignmentArgumentsCode] using
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
  rw [targetEq]

/-- The canonical packed lookup for a covering candidate is the same lookup
performed by `localAssignment` at that placement's relative offset. -/
theorem packedCenterCoveringAssignment_eq_local
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (source : Cell)
    (sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packed.assignmentAtCell periodicStrip
        (packedCoveringColumn symmetry source)
        (packedCenterCoveringTarget
          periodicStrip packed base symmetry source) =
      packed.localAssignment periodicStrip
        (Cell.sub (0, base.2) (symmetry.act source)) := by
  have horizontal := packedCoveringColumn_displacement
    tromino symmetry source sourceMember
  rw [show Cell.sub (0, base.2) (symmetry.act source) =
      ((packedCoveringColumn symmetry source).displacement,
        base.2 - (symmetry.act source).2) by
    simp [Cell.sub, horizontal]]
  simp [PackedWindowState.localAssignment,
    WindowColumn.ofDisplacementCode?_eq,
    PackedWindowState.valueAt, packedCenterCoveringTarget]

/-- Test whether the covering placement determined by a fixed symmetry/source
pair is selected by the packed frontier. -/
def packedCenterCoveringCandidateCode
    (symmetry : SquareSymmetry) (source : Cell) : Code :=
  (packedAssignmentIsCode (some symmetry)).comp
    (packedCenterCoveringAssignmentArgumentsCode symmetry source)

/-- One covering-candidate program computes exactly the active-placement
filter predicate. -/
theorem packedCenterCoveringCandidateCode_eval_semantic
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (source : Cell)
    (sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterCoveringCandidateCode symmetry source).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(decide
        (packed.localAssignment periodicStrip
          (Cell.sub (0, base.2) (symmetry.act source)) =
            some symmetry)).toNat] := by
  let column := packedCoveringColumn symmetry source
  let target := packedCenterCoveringTarget
    periodicStrip packed base symmetry source
  have arguments := packedCenterCoveringAssignmentArgumentsCode_eval
    symmetry source periodicStrip packed base
  have selected := packedAssignmentIsCode_eval_semantic
    (some symmetry) periodicStrip packed column target
  have run :
      (packedCenterCoveringCandidateCode symmetry source).eval
          (packedCenterCandidateInput periodicStrip packed base) =
        pure [(decide
          (packed.assignmentAtCell periodicStrip column target =
            some symmetry)).toNat] := by
    simpa [packedCenterCoveringCandidateCode, column, target] using
      (comp_eval_pure _ _ _ _ arguments).trans selected
  rw [packedCenterCoveringAssignment_eq_local
    tromino symmetry source sourceMember periodicStrip packed base] at run
  exact run

end Turing.ToPartrec.Code
