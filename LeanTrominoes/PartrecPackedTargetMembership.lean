import LeanTrominoes.PartrecPackedAssignmentAt
import LeanTrominoes.PartrecPackedTargetCell
import LeanTrominoes.PeriodicStripCanonicalMembership

/-!
# Packed target membership

Center validity asks whether a fixed translated source cell belongs to the
periodic strip.  On native input

`[period, phase, motifCode, encodedRow, assignmentWord]`,

this file constructs the canonical motif cell for a fixed frontier column and
vertical offset, scans the encoded motif using the existing five-column
packed lookup, and projects its `found` bit.  The assignment word is retained
because later center-validity leaves use the same live state for membership
and assignment tests.
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

/-- Assemble `[period, phase, column, encodedRow]` for the canonical target
cell constructor. -/
def packedTargetMembershipTargetArgumentsCode
    (column : WindowColumn) : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (numeral column.val) (get 3)

@[simp]
theorem packedTargetMembershipTargetArgumentsCode_eval
    (column : WindowColumn)
    (period phase motifCode word : Nat) (row : Int) :
    (packedTargetMembershipTargetArgumentsCode column).eval
        [period, phase, motifCode, Encodable.encode row, word] =
      pure [period, phase, column.val, Encodable.encode row] := by
  simp [packedTargetMembershipTargetArgumentsCode]

/-- Construct the canonical encoded motif cell at a fixed vertical offset. -/
def packedTargetMembershipTargetCode
    (column : WindowColumn) (verticalOffset : Int) : Code :=
  (packedTargetCellCode verticalOffset).comp
    (packedTargetMembershipTargetArgumentsCode column)

@[simp]
theorem packedTargetMembershipTargetCode_eval
    (column : WindowColumn) (verticalOffset : Int)
    (period phase motifCode word : Nat) (row : Int) :
    (packedTargetMembershipTargetCode column verticalOffset).eval
        [period, phase, motifCode, Encodable.encode row, word] =
      let x := packedColumnPhaseNumerator period phase column.val % period
      pure [Encodable.encode
        ((Int.ofNat x, row + verticalOffset) : Cell)] := by
  simp [packedTargetMembershipTargetCode]

/-- Assemble the four-field input of the packed motif scanner. -/
def packedTargetMembershipLookupArgumentsCode
    (column : WindowColumn) (verticalOffset : Int) : Code :=
  prepend (get 2) <|
    prepend (numeral column.val) <|
      prepend (packedTargetMembershipTargetCode column verticalOffset)
        (get 4)

@[simp]
theorem packedTargetMembershipLookupArgumentsCode_eval
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell) (word : Nat) (row : Int) :
    (packedTargetMembershipLookupArgumentsCode
        column verticalOffset).eval
        [period, phase, Encodable.encode motif,
          Encodable.encode row, word] =
      let x := packedColumnPhaseNumerator period phase column.val % period
      pure [Encodable.encode motif, column.val,
        Encodable.encode ((Int.ofNat x, row + verticalOffset) : Cell),
        word] := by
  simp [packedTargetMembershipLookupArgumentsCode]

/-- Scan the motif for the canonical target and project the scanner's
normalized `found` bit. -/
def packedTargetMembershipCode
    (column : WindowColumn) (verticalOffset : Int) : Code :=
  (get 1).comp <|
    packedAssignmentLookupCode.comp
      (packedTargetMembershipLookupArgumentsCode column verticalOffset)

@[simp]
theorem packedTargetMembershipCode_eval
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell) (word : Nat) (row : Int) :
    (packedTargetMembershipCode column verticalOffset).eval
        [period, phase, Encodable.encode motif,
          Encodable.encode row, word] =
      let target : Cell :=
        (Int.ofNat
            (packedColumnPhaseNumerator period phase column.val % period),
          row + verticalOffset)
      pure [(packedAssignmentLookupOutcome motif column.val
        target word).2.2.toNat] := by
  let target : Cell :=
    (Int.ofNat
        (packedColumnPhaseNumerator period phase column.val % period),
      row + verticalOffset)
  have arguments :
      (packedTargetMembershipLookupArgumentsCode
          column verticalOffset).eval
          [period, phase, Encodable.encode motif,
            Encodable.encode row, word] =
        pure [Encodable.encode motif, column.val,
          Encodable.encode target, word] := by
    simp [target]
  have lookup :=
    packedAssignmentLookupCode_eval motif column.val target word
  have assembled :
      (packedAssignmentLookupCode.comp
          (packedTargetMembershipLookupArgumentsCode
            column verticalOffset)).eval
          [period, phase, Encodable.encode motif,
            Encodable.encode row, word] =
        pure
          [(packedAssignmentLookupOutcome motif column.val
              target word).2.1,
            (packedAssignmentLookupOutcome motif column.val
              target word).2.2.toNat] :=
    (comp_eval_pure _ _ _ _ arguments).trans lookup
  change
    ((get 1).comp
      (packedAssignmentLookupCode.comp
        (packedTargetMembershipLookupArgumentsCode
          column verticalOffset))).eval
        [period, phase, Encodable.encode motif,
          Encodable.encode row, word] =
      pure [(packedAssignmentLookupOutcome motif column.val
        target word).2.2.toNat]
  calc
    _ = (get 1).eval
        [(packedAssignmentLookupOutcome motif column.val
            target word).2.1,
          (packedAssignmentLookupOutcome motif column.val
            target word).2.2.toNat] :=
      comp_eval_pure _ _ _ _ assembled
    _ = _ := by simp

/-- The packed scanner's `found` field is precisely motif membership for a
genuine frontier column. -/
theorem packedAssignmentLookupOutcome_found_eq_decide_mem
    (motif : List Cell) (column : WindowColumn)
    (target : Cell) (word : Nat) :
    (packedAssignmentLookupOutcome motif column.val target word).2.2 =
      decide (target ∈ motif) := by
  by_cases member : target ∈ motif
  · rw [packedAssignmentLookupOutcome_found_of_mem
      motif target word column member]
    simp [member]
  · have outcome := packedAssignmentLookupOutcome_of_not_mem
      motif column.val target word member
    have foundFalse :
        (packedAssignmentLookupOutcome motif column.val
          target word).2.2 = false := by
      exact congrArg Prod.snd outcome
    rw [foundFalse]
    simp [member]

/-- Semantic finite-motif form of the complete target-membership leaf. -/
theorem packedTargetMembershipCode_eval_motif
    (column : WindowColumn) (verticalOffset : Int)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (row : Int) :
    (packedTargetMembershipCode column verticalOffset).eval
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif,
          Encodable.encode row, packed.assignmentWord] =
      pure [(decide
        (((packed.columnPhase periodicStrip column : Int),
          row + verticalOffset) ∈ periodicStrip.motif)).toNat] := by
  rw [packedTargetMembershipCode_eval]
  simp only
  have targetEq :
      ((Int.ofNat
          (packedColumnPhaseNumerator periodicStrip.period
            packed.phase column.val % periodicStrip.period),
        row + verticalOffset) : Cell) =
        ((packed.columnPhase periodicStrip column : Int),
          row + verticalOffset) := by
    apply Prod.ext
    · simp only [PackedWindowState.columnPhase,
        packedColumnPhaseNumerator, packedColumnPhaseSum]
      congr 2
      omega
    · rfl
  rw [targetEq]
  rw [packedAssignmentLookupOutcome_found_eq_decide_mem]

/-- On a well-formed strip, the finite lookup computes actual membership of
the physical translated cell represented by the packed column. -/
theorem packedTargetMembershipCode_eval_contains
    (column : WindowColumn) (verticalOffset : Int)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (row : Int) :
    (packedTargetMembershipCode column verticalOffset).eval
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif,
          Encodable.encode row, packed.assignmentWord] =
      pure [(periodicStrip.contains
        ((packed.phase : Int) + column.displacement,
          row + verticalOffset)).toNat] := by
  rw [packedTargetMembershipCode_eval_motif]
  have membershipEq :
      periodicStrip.contains
          ((packed.phase : Int) + column.displacement,
            row + verticalOffset) =
        decide
          ((((packed.columnPhase periodicStrip column : Nat) : Int),
            row + verticalOffset) ∈ periodicStrip.motif) := by
    apply Bool.eq_iff_iff.mpr
    rw [decide_eq_true_eq]
    exact PackedWindowState.contains_column_eq_true_iff_mem_motif
      periodicStrip wellFormed packed column (row + verticalOffset)
  rw [membershipEq]

/-- Specialization to the source-cell containment predicate used by packed
center validity. -/
theorem packedTargetMembershipCode_eval_centerSourceInside
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell)
    (symmetry : SquareSymmetry) (source : Cell)
    (column : WindowColumn)
    (horizontal : (symmetry.act source).1 = column.displacement) :
    (packedTargetMembershipCode column
        (symmetry.act source).2).eval
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif,
          Encodable.encode base.2, packed.assignmentWord] =
      pure [(packed.centerSourceInsideBool periodicStrip
        base symmetry source).toNat] := by
  rw [packedTargetMembershipCode_eval_contains
    column (symmetry.act source).2 periodicStrip wellFormed packed base.2]
  simp [PackedWindowState.centerSourceInsideBool,
    Cell.add, horizontal]

end Turing.ToPartrec.Code
