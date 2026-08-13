/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatPackedAssignmentPredicates
import LeanTrominoes.PartrecFlatPackedTargetMembership
import LeanTrominoes.PartrecPackedCenterCandidate

/-!
# Packed center-placement candidates on flat motif fields

For one motif base and one fixed square symmetry, center containment says that
either the packed frontier does not select that symmetry or all three cells of
the resulting tromino lie in the strip.  This flat port has native input

`[period, phase, motif length, base x, base y, assignment word, coordinates...]`.

It retains the coordinate stream across both the assignment-selection lookup
and the three translated target-membership scans, without constructing a
recursively paired motif code.
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

/-- Native flat state for one center-base candidate check. -/
def flatPackedCenterCandidateInput
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) : List Nat :=
  [periodicStrip.period, packed.phase, periodicStrip.motif.length,
      Encodable.encode base.1, Encodable.encode base.2,
      packed.assignmentWord] ++
    periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields

/-- Assemble the flat packed lookup input for the center-column base. -/
def flatPackedCenterAssignmentArgumentsCode : Code :=
  prepend (get 2) <|
    prepend (numeral WindowState.center.val) <|
      prepend (get 3) <|
        prepend (get 4) <|
          prepend (get 5) (drop 6)

@[simp]
theorem flatPackedCenterAssignmentArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterAssignmentArgumentsCode.eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure
        ([periodicStrip.motif.length, WindowState.center.val,
            Encodable.encode base.1, Encodable.encode base.2,
            packed.assignmentWord] ++
          periodicStrip.motif.flatMap
            PeriodicStripFlatEncoding.cellFields) := by
  simp [flatPackedCenterAssignmentArgumentsCode,
    flatPackedCenterCandidateInput]

/-- Test whether the center base selects one fixed symmetry. -/
def flatPackedCenterAssignmentIsCode
    (symmetry : SquareSymmetry) : Code :=
  (flatPackedAssignmentIsCode (some symmetry)).comp
    flatPackedCenterAssignmentArgumentsCode

@[simp]
theorem flatPackedCenterAssignmentIsCode_eval_semantic
    (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    (flatPackedCenterAssignmentIsCode symmetry).eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [(decide
        (packed.assignmentAtCell periodicStrip
          WindowState.center base = some symmetry)).toNat] := by
  have arguments :=
    flatPackedCenterAssignmentArgumentsCode_eval
      periodicStrip packed base
  have selected :=
    flatPackedAssignmentIsCode_eval_semantic
      (some symmetry) periodicStrip packed
      WindowState.center base
  simpa only [flatPackedCenterAssignmentIsCode] using
    (comp_eval_pure _ _ _ _ arguments).trans selected

/-- Assemble the flat target-membership input shared by translated source
leaves. -/
def flatPackedCenterSourceInputCode : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (get 2) <|
        prepend (get 4) <|
          prepend (get 5) (drop 6)

@[simp]
theorem flatPackedCenterSourceInputCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (base : Cell) :
    flatPackedCenterSourceInputCode.eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure
        ([periodicStrip.period, packed.phase,
            periodicStrip.motif.length, Encodable.encode base.2,
            packed.assignmentWord] ++
          periodicStrip.motif.flatMap
            PeriodicStripFlatEncoding.cellFields) := by
  simp [flatPackedCenterSourceInputCode,
    flatPackedCenterCandidateInput]

/-- Membership test for one transformed source cell of a candidate. -/
def flatPackedCenterSourceInsideCode
    (symmetry : SquareSymmetry) (source : Cell) : Code :=
  (flatPackedTargetMembershipCode
    (packedSourceColumn symmetry source)
    (symmetry.act source).2).comp flatPackedCenterSourceInputCode

theorem flatPackedCenterSourceInsideCode_eval_semantic
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (source : Cell)
    (sourceMember :
      source ∈ TrominoAssignment.trominoCellList tromino)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    (flatPackedCenterSourceInsideCode symmetry source).eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [(packed.centerSourceInsideBool periodicStrip
        base symmetry source).toNat] := by
  have horizontal :
      (symmetry.act source).1 =
        (packedSourceColumn symmetry source).displacement :=
    (packedSourceColumn_displacement
      tromino symmetry source sourceMember).symm
  have membership :=
    flatPackedTargetMembershipCode_eval_centerSourceInside
      periodicStrip wellFormed packed base symmetry source
      (packedSourceColumn symmetry source) horizontal
  simp only [flatPackedCenterSourceInsideCode]
  exact (comp_eval_pure _ _ _ _
    (flatPackedCenterSourceInputCode_eval
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
def flatPackedCenterAllSourcesInsideCode
    (tromino : Tromino) (symmetry : SquareSymmetry) : Code :=
  match tromino with
  | .I =>
      boolAnd
        (flatPackedCenterSourceInsideCode symmetry (0, 0)) <|
        boolAnd
          (flatPackedCenterSourceInsideCode symmetry (1, 0))
          (flatPackedCenterSourceInsideCode symmetry (2, 0))
  | .L =>
      boolAnd
        (flatPackedCenterSourceInsideCode symmetry (0, 0)) <|
        boolAnd
          (flatPackedCenterSourceInsideCode symmetry (1, 0))
          (flatPackedCenterSourceInsideCode symmetry (0, 1))

theorem flatPackedCenterAllSourcesInsideCode_eval_semantic
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    (flatPackedCenterAllSourcesInsideCode tromino symmetry).eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [((TrominoAssignment.trominoCellList tromino).all
        fun source => packed.centerSourceInsideBool periodicStrip
          base symmetry source).toNat] := by
  cases tromino with
  | I =>
      simpa [flatPackedCenterAllSourcesInsideCode,
        TrominoAssignment.trominoCellList] using
        boolAndThree_eval_bool
          (flatPackedCenterSourceInsideCode symmetry (0, 0))
          (flatPackedCenterSourceInsideCode symmetry (1, 0))
          (flatPackedCenterSourceInsideCode symmetry (2, 0))
          (flatPackedCenterCandidateInput periodicStrip packed base)
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (0, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (1, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (2, 0))
          (flatPackedCenterSourceInsideCode_eval_semantic .I symmetry
            (0, 0) (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (flatPackedCenterSourceInsideCode_eval_semantic .I symmetry
            (1, 0) (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (flatPackedCenterSourceInsideCode_eval_semantic .I symmetry
            (2, 0) (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
  | L =>
      simpa [flatPackedCenterAllSourcesInsideCode,
        TrominoAssignment.trominoCellList] using
        boolAndThree_eval_bool
          (flatPackedCenterSourceInsideCode symmetry (0, 0))
          (flatPackedCenterSourceInsideCode symmetry (1, 0))
          (flatPackedCenterSourceInsideCode symmetry (0, 1))
          (flatPackedCenterCandidateInput periodicStrip packed base)
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (0, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (1, 0))
          (packed.centerSourceInsideBool periodicStrip
            base symmetry (0, 1))
          (flatPackedCenterSourceInsideCode_eval_semantic .L symmetry
            (0, 0) (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (flatPackedCenterSourceInsideCode_eval_semantic .L symmetry
            (1, 0) (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)
          (flatPackedCenterSourceInsideCode_eval_semantic .L symmetry
            (0, 1) (by simp [TrominoAssignment.trominoCellList])
            periodicStrip wellFormed packed base)

/-- Check the center-containment implication for one fixed symmetry. -/
def flatPackedCenterCandidateInsideCode
    (tromino : Tromino) (symmetry : SquareSymmetry) : Code :=
  boolOr
    (isZero (flatPackedCenterAssignmentIsCode symmetry))
    (flatPackedCenterAllSourcesInsideCode tromino symmetry)

/-- The flat candidate program computes the corresponding semantic packed
center-containment Boolean. -/
theorem flatPackedCenterCandidateInsideCode_eval_semantic
    (tromino : Tromino) (symmetry : SquareSymmetry)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell) :
    (flatPackedCenterCandidateInsideCode tromino symmetry).eval
        (flatPackedCenterCandidateInput periodicStrip packed base) =
      pure [(packed.centerSymmetryInsideBool tromino periodicStrip
        base symmetry).toNat] := by
  let values := flatPackedCenterCandidateInput periodicStrip packed base
  let selected := decide
    (packed.assignmentAtCell periodicStrip
      WindowState.center base = some symmetry)
  let inside :=
    (TrominoAssignment.trominoCellList tromino).all fun source =>
      packed.centerSourceInsideBool periodicStrip base symmetry source
  have selectedRun :
      (flatPackedCenterAssignmentIsCode symmetry).eval values =
        pure [selected.toNat] := by
    simp [values, selected]
  have absentRaw := isZero_eval_at
    (flatPackedCenterAssignmentIsCode symmetry) values selected.toNat
    selectedRun
  have absentRun :
      (isZero (flatPackedCenterAssignmentIsCode symmetry)).eval values =
        pure [(!selected).toNat] := by
    cases selectedEq : selected <;>
      simpa [selectedEq] using absentRaw
  have insideRun :
      (flatPackedCenterAllSourcesInsideCode tromino symmetry).eval values =
        pure [inside.toNat] := by
    simpa [values, inside] using
      flatPackedCenterAllSourcesInsideCode_eval_semantic
        tromino symmetry periodicStrip wellFormed packed base
  have resultRaw := boolOr_eval_at
    (isZero (flatPackedCenterAssignmentIsCode symmetry))
    (flatPackedCenterAllSourcesInsideCode tromino symmetry)
    values (!selected).toNat inside.toNat absentRun insideRun
  have result :
      (boolOr
        (isZero (flatPackedCenterAssignmentIsCode symmetry))
        (flatPackedCenterAllSourcesInsideCode tromino symmetry)).eval values =
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
  simp only [flatPackedCenterCandidateInsideCode]
  change
    (boolOr
      (isZero (flatPackedCenterAssignmentIsCode symmetry))
      (flatPackedCenterAllSourcesInsideCode tromino symmetry)).eval values =
      pure [(packed.centerSymmetryInsideBool tromino periodicStrip
        base symmetry).toNat]
  rw [semanticEq]
  exact result

end Turing.ToPartrec.Code
