import LeanTrominoes.PartrecPackedAssignmentPredicates
import LeanTrominoes.PartrecPackedTargetMembership

/-!
# Packed center-placement candidates

For one motif base and one fixed square symmetry, center containment says that
either the packed frontier does not select that symmetry or all three cells of
the resulting tromino lie in the strip.  This file expresses that implication
as an explicit fixed-width program.  Its native input is

`[period, phase, motifCode, baseCellCode, encodedBaseRow, assignmentWord]`.

The base-cell code supports assignment lookup, while the separately retained
row encoding lets the three translated membership leaves reuse the canonical
target constructor without decoding a complete frontier.
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

/-- Fixed-width native state for one center-base candidate check. -/
def packedCenterCandidateInput
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : List Nat :=
  [periodicStrip.period, packed.phase,
    Encodable.encode periodicStrip.motif,
    Encodable.encode base, Encodable.encode base.2,
    packed.assignmentWord]

/-- Assemble the standard packed lookup input for the center-column base. -/
def packedCenterAssignmentArgumentsCode : Code :=
  prepend (get 2) <|
    prepend (numeral WindowState.center.val) <|
      prepend (get 3) (get 5)

@[simp]
theorem packedCenterAssignmentArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterAssignmentArgumentsCode.eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [Encodable.encode periodicStrip.motif,
        WindowState.center.val, Encodable.encode base,
        packed.assignmentWord] := by
  simp [packedCenterAssignmentArgumentsCode,
    packedCenterCandidateInput]

/-- Test whether the center base selects one fixed symmetry. -/
def packedCenterAssignmentIsCode
    (symmetry : SquareSymmetry) : Code :=
  (packedAssignmentIsCode (some symmetry)).comp
    packedCenterAssignmentArgumentsCode

@[simp]
theorem packedCenterAssignmentIsCode_eval_semantic
    (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterAssignmentIsCode symmetry).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(decide
        (packed.assignmentAtCell periodicStrip
          WindowState.center base = some symmetry)).toNat] := by
  have arguments :=
    packedCenterAssignmentArgumentsCode_eval
      periodicStrip packed base
  have selected :=
    packedAssignmentIsCode_eval_semantic
      (some symmetry) periodicStrip packed
      WindowState.center base
  simpa only [packedCenterAssignmentIsCode] using
    (comp_eval_pure _ _ _ _ arguments).trans selected

/-- Assemble the five-field input shared by translated target-membership
leaves. -/
def packedCenterSourceInputCode : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (get 2) <|
        prepend (get 4) (get 5)

@[simp]
theorem packedCenterSourceInputCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    packedCenterSourceInputCode.eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [periodicStrip.period, packed.phase,
        Encodable.encode periodicStrip.motif,
        Encodable.encode base.2, packed.assignmentWord] := by
  simp [packedCenterSourceInputCode,
    packedCenterCandidateInput]

/-- Total five-column encoding of a transformed source's horizontal
displacement.  Canonical tromino cells always transform into `[-2, 2]`, so
the reduction modulo five is inactive on the inputs used below. -/
def packedSourceColumn
    (symmetry : SquareSymmetry) (source : Cell) : WindowColumn :=
  ⟨((symmetry.act source).1 + 2).toNat % 5,
    Nat.mod_lt _ (by omega)⟩

theorem packedSourceColumn_displacement
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (source : Cell)
    (sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino) :
    (packedSourceColumn symmetry source).displacement =
      (symmetry.act source).1 := by
  cases tromino <;> cases symmetry <;>
    simp [TrominoAssignment.trominoCellList] at sourceMember
  all_goals rcases sourceMember with rfl | rfl | rfl <;> native_decide

/-- Membership test for one transformed source cell of a candidate. -/
def packedCenterSourceInsideCode
    (symmetry : SquareSymmetry) (source : Cell) : Code :=
  (packedTargetMembershipCode
    (packedSourceColumn symmetry source)
    (symmetry.act source).2).comp packedCenterSourceInputCode

theorem packedCenterSourceInsideCode_eval_semantic
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (source : Cell)
    (sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterSourceInsideCode symmetry source).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(packed.centerSourceInsideBool periodicStrip
        base symmetry source).toNat] := by
  have horizontal :
      (symmetry.act source).1 =
        (packedSourceColumn symmetry source).displacement :=
    (packedSourceColumn_displacement
      tromino symmetry source sourceMember).symm
  have membership :=
    packedTargetMembershipCode_eval_centerSourceInside
      periodicStrip wellFormed packed base symmetry source
      (packedSourceColumn symmetry source) horizontal
  simp only [packedCenterSourceInsideCode]
  simpa [packedCenterCandidateInput] using
    (comp_eval_pure _ _ _ _
      (packedCenterSourceInputCode_eval
        periodicStrip packed base)).trans membership

private theorem boolAndThree_eval_bool
    (first second third : Code) (values : List Nat)
    (firstValue secondValue thirdValue : Bool)
    (firstCorrect : first.eval values = pure [firstValue.toNat])
    (secondCorrect : second.eval values = pure [secondValue.toNat])
    (thirdCorrect : third.eval values = pure [thirdValue.toNat]) :
    (boolAnd first (boolAnd second third)).eval values =
      pure [(firstValue && (secondValue && thirdValue)).toNat] := by
  have tailRaw := boolAnd_eval_at second third values
    secondValue.toNat thirdValue.toNat secondCorrect thirdCorrect
  have tail :
      (boolAnd second third).eval values =
        pure [(secondValue && thirdValue).toNat] := by
    cases secondValue <;> cases thirdValue <;> simpa using tailRaw
  have resultRaw := boolAnd_eval_at first (boolAnd second third) values
    firstValue.toNat (secondValue && thirdValue).toNat
    firstCorrect tail
  cases firstValue <;> cases secondValue <;> cases thirdValue <;>
    simpa using resultRaw

/-- Conjoin the three canonical source-cell membership tests for one fixed
candidate symmetry. -/
def packedCenterAllSourcesInsideCode
    (tromino : Tromino) (symmetry : SquareSymmetry) : Code :=
  match tromino with
  | .I =>
      boolAnd
        (packedCenterSourceInsideCode symmetry (0, 0)) <|
        boolAnd
          (packedCenterSourceInsideCode symmetry (1, 0))
          (packedCenterSourceInsideCode symmetry (2, 0))
  | .L =>
      boolAnd
        (packedCenterSourceInsideCode symmetry (0, 0)) <|
        boolAnd
          (packedCenterSourceInsideCode symmetry (1, 0))
          (packedCenterSourceInsideCode symmetry (0, 1))

theorem packedCenterAllSourcesInsideCode_eval_semantic
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterAllSourcesInsideCode tromino symmetry).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [((TrominoAssignment.trominoCellList tromino).all
        fun source => packed.centerSourceInsideBool periodicStrip
          base symmetry source).toNat] := by
  cases tromino with
  | I =>
      simpa [packedCenterAllSourcesInsideCode,
        TrominoAssignment.trominoCellList] using
        boolAndThree_eval_bool
          (packedCenterSourceInsideCode symmetry (0, 0))
          (packedCenterSourceInsideCode symmetry (1, 0))
          (packedCenterSourceInsideCode symmetry (2, 0))
          (packedCenterCandidateInput periodicStrip packed base)
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (0, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (1, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (2, 0))
          (packedCenterSourceInsideCode_eval_semantic .I symmetry
            (0, 0) (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (packedCenterSourceInsideCode_eval_semantic .I symmetry
            (1, 0) (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (packedCenterSourceInsideCode_eval_semantic .I symmetry
            (2, 0) (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
  | L =>
      simpa [packedCenterAllSourcesInsideCode,
        TrominoAssignment.trominoCellList] using
        boolAndThree_eval_bool
          (packedCenterSourceInsideCode symmetry (0, 0))
          (packedCenterSourceInsideCode symmetry (1, 0))
          (packedCenterSourceInsideCode symmetry (0, 1))
          (packedCenterCandidateInput periodicStrip packed base)
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (0, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (1, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (0, 1))
          (packedCenterSourceInsideCode_eval_semantic .L symmetry
            (0, 0) (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (packedCenterSourceInsideCode_eval_semantic .L symmetry
            (1, 0) (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (packedCenterSourceInsideCode_eval_semantic .L symmetry
            (0, 1) (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)

/-- Check the center-containment implication for one fixed symmetry. -/
def packedCenterCandidateInsideCode
    (tromino : Tromino) (symmetry : SquareSymmetry) : Code :=
  boolOr
    (isZero (packedCenterAssignmentIsCode symmetry))
    (packedCenterAllSourcesInsideCode tromino symmetry)

/-- The fixed candidate program computes the corresponding semantic packed
center-containment Boolean. -/
theorem packedCenterCandidateInsideCode_eval_semantic
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    (packedCenterCandidateInsideCode tromino symmetry).eval
        (packedCenterCandidateInput periodicStrip packed base) =
      pure [(packed.centerSymmetryInsideBool tromino periodicStrip
        base symmetry).toNat] := by
  let values := packedCenterCandidateInput periodicStrip packed base
  let selected := decide
    (packed.assignmentAtCell periodicStrip
      WindowState.center base = some symmetry)
  let inside :=
    (TrominoAssignment.trominoCellList tromino).all fun source =>
      packed.centerSourceInsideBool periodicStrip base symmetry source
  have selectedRun :
      (packedCenterAssignmentIsCode symmetry).eval values =
        pure [selected.toNat] := by
    simp [values, selected]
  have absentRaw := isZero_eval_at
    (packedCenterAssignmentIsCode symmetry) values selected.toNat
    selectedRun
  have absentRun :
      (isZero (packedCenterAssignmentIsCode symmetry)).eval values =
        pure [(!selected).toNat] := by
    cases selectedEq : selected <;>
      simpa [selectedEq] using absentRaw
  have insideRun :
      (packedCenterAllSourcesInsideCode tromino symmetry).eval values =
        pure [inside.toNat] := by
    simpa [values, inside] using
      packedCenterAllSourcesInsideCode_eval_semantic
        tromino symmetry periodicStrip wellFormed packed base
  have resultRaw := boolOr_eval_at
    (isZero (packedCenterAssignmentIsCode symmetry))
    (packedCenterAllSourcesInsideCode tromino symmetry)
    values (!selected).toNat inside.toNat absentRun insideRun
  have result :
      (boolOr
        (isZero (packedCenterAssignmentIsCode symmetry))
        (packedCenterAllSourcesInsideCode tromino symmetry)).eval values =
        pure [((!selected) || inside).toNat] := by
    cases selectedEq : selected <;> cases insideEq : inside <;>
      simpa [selectedEq, insideEq] using resultRaw
  have semanticEq :
      packed.centerSymmetryInsideBool tromino periodicStrip
          base symmetry =
        ((!selected) || inside) := by
    unfold PackedWindowState.centerSymmetryInsideBool
    change
      (decide
          (packed.assignmentAtCell periodicStrip
            WindowState.center base ≠ some symmetry) || inside) =
        ((!selected) || inside)
    simp [selected]
  simp only [packedCenterCandidateInsideCode]
  change
    (boolOr
      (isZero (packedCenterAssignmentIsCode symmetry))
      (packedCenterAllSourcesInsideCode tromino symmetry)).eval values =
      pure [(packed.centerSymmetryInsideBool tromino periodicStrip
        base symmetry).toNat]
  rw [semanticEq]
  exact result

end Turing.ToPartrec.Code
