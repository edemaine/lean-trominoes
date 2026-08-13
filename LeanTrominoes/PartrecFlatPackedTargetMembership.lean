import LeanTrominoes.PartrecFlatPackedAssignmentAt
import LeanTrominoes.PartrecPackedTargetMembership

/-!
# Packed target membership on flat motif fields

Input is

`[period, phase, motif length, encoded row, word, coordinates...]`.

The canonical target coordinates are constructed separately and passed to the
flat five-column lookup; the projected `found` bit therefore decides finite
motif membership without a nested motif code.
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

/-- Assemble `[period, phase, column, encoded row]`. -/
def flatPackedTargetArgumentsCode
    (column : WindowColumn) : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (numeral column.val) (get 3)

def flatPackedTargetXCode (column : WindowColumn) : Code :=
  packedTargetXCode.comp (flatPackedTargetArgumentsCode column)

def flatPackedTargetYCode
    (column : WindowColumn) (verticalOffset : Int) : Code :=
  (packedTargetYCode verticalOffset).comp
    (flatPackedTargetArgumentsCode column)

@[simp]
theorem flatPackedTargetXCode_eval
    (column : WindowColumn) (period phase motifLength word : Nat)
    (row : Int) (coordinates : List Nat) :
    (flatPackedTargetXCode column).eval
        ([period, phase, motifLength, Encodable.encode row, word] ++
          coordinates) =
      pure
        [Encodable.encode
          (Int.ofNat
            (packedColumnPhaseNumerator period phase column.val % period))] := by
  have arguments :
      (flatPackedTargetArgumentsCode column).eval
          ([period, phase, motifLength, Encodable.encode row, word] ++
            coordinates) =
        pure [period, phase, column.val, Encodable.encode row] := by
    simp [flatPackedTargetArgumentsCode]
  calc
    _ = packedTargetXCode.eval
        [period, phase, column.val, Encodable.encode row] :=
      comp_eval_pure _ _ _ _ arguments
    _ = pure
        [2 * (packedColumnPhaseNumerator period phase column.val % period)] :=
      packedTargetXCode_eval _ _ _ _
    _ = _ := by simp only [IntEncoding.encode_ofNat]

@[simp]
theorem flatPackedTargetYCode_eval
    (column : WindowColumn) (verticalOffset : Int)
    (period phase motifLength word : Nat)
    (row : Int) (coordinates : List Nat) :
    (flatPackedTargetYCode column verticalOffset).eval
        ([period, phase, motifLength, Encodable.encode row, word] ++
          coordinates) =
      pure [Encodable.encode (row + verticalOffset)] := by
  simp [flatPackedTargetYCode, flatPackedTargetArgumentsCode]

/-- Build the public input of the flat five-column assignment lookup. -/
def flatPackedTargetMembershipLookupArgumentsCode
    (column : WindowColumn) (verticalOffset : Int) : Code :=
  prepend (get 2) <|
    prepend (numeral column.val) <|
      prepend (flatPackedTargetXCode column) <|
        prepend (flatPackedTargetYCode column verticalOffset) <|
          prepend (get 4) (drop 5)

@[simp]
theorem flatPackedTargetMembershipLookupArgumentsCode_eval
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell) (word : Nat)
    (row : Int) :
    (flatPackedTargetMembershipLookupArgumentsCode
      column verticalOffset).eval
        ([period, phase, motif.length, Encodable.encode row, word] ++
          motif.flatMap PeriodicStripFlatEncoding.cellFields) =
      let x := packedColumnPhaseNumerator period phase column.val % period
      pure
        ([motif.length, column.val, Encodable.encode (Int.ofNat x),
            Encodable.encode (row + verticalOffset), word] ++
          motif.flatMap PeriodicStripFlatEncoding.cellFields) := by
  have xRun := flatPackedTargetXCode_eval column period phase
    motif.length word row
      (motif.flatMap PeriodicStripFlatEncoding.cellFields)
  have yRun := flatPackedTargetYCode_eval column verticalOffset period phase
    motif.length word row
      (motif.flatMap PeriodicStripFlatEncoding.cellFields)
  simp only [flatPackedTargetMembershipLookupArgumentsCode,
    prepend_eval_eq]
  rw [show (get 2).eval
      ([period, phase, motif.length, Encodable.encode row, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields) =
      pure [motif.length] by simp]
  rw [show (numeral column.val).eval
      ([period, phase, motif.length, Encodable.encode row, word] ++
        motif.flatMap PeriodicStripFlatEncoding.cellFields) =
      pure [column.val] by simp]
  rw [xRun, yRun]
  simp

/-- Scan the flat motif and project the normalized `found` bit. -/
def flatPackedTargetMembershipCode
    (column : WindowColumn) (verticalOffset : Int) : Code :=
  (get 1).comp <|
    flatPackedAssignmentLookupCode.comp
      (flatPackedTargetMembershipLookupArgumentsCode
        column verticalOffset)

@[simp]
theorem flatPackedTargetMembershipCode_eval
    (column : WindowColumn) (verticalOffset : Int)
    (period phase : Nat) (motif : List Cell) (word : Nat)
    (row : Int) :
    (flatPackedTargetMembershipCode column verticalOffset).eval
        ([period, phase, motif.length, Encodable.encode row, word] ++
          motif.flatMap PeriodicStripFlatEncoding.cellFields) =
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
  have arguments :=
    flatPackedTargetMembershipLookupArgumentsCode_eval
      column verticalOffset period phase motif word row
  have lookup := flatPackedAssignmentLookupCode_eval
    motif column.val target word
  have assembled :
      (flatPackedAssignmentLookupCode.comp
        (flatPackedTargetMembershipLookupArgumentsCode
          column verticalOffset)).eval
          ([period, phase, motif.length, Encodable.encode row, word] ++
            motif.flatMap PeriodicStripFlatEncoding.cellFields) =
        pure
          [(packedAssignmentLookupOutcome motif column.val
              target word).2.1,
            (packedAssignmentLookupOutcome motif column.val
              target word).2.2.toNat] := by
    calc
      _ = flatPackedAssignmentLookupCode.eval
          ([motif.length, column.val, Encodable.encode target.1,
              Encodable.encode target.2, word] ++
            motif.flatMap PeriodicStripFlatEncoding.cellFields) := by
        simpa [target] using comp_eval_pure _ _ _ _ arguments
      _ = _ := lookup
  calc
    _ = (get 1).eval
        [(packedAssignmentLookupOutcome motif column.val
            target word).2.1,
          (packedAssignmentLookupOutcome motif column.val
            target word).2.2.toNat] :=
      comp_eval_pure _ _ _ _ assembled
    _ = pure
        [(packedAssignmentLookupOutcome motif column.val
          target word).2.2.toNat] := by simp
    _ = _ := by rfl

@[simp]
theorem flatPackedTargetMembershipCode_eval_motif
    (column : WindowColumn) (verticalOffset : Int)
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (row : Int) :
    (flatPackedTargetMembershipCode column verticalOffset).eval
        ([periodicStrip.period, packed.phase,
            periodicStrip.motif.length, Encodable.encode row,
            packed.assignmentWord] ++
          periodicStrip.motif.flatMap
            PeriodicStripFlatEncoding.cellFields) =
      pure
        [(decide
          (((packed.columnPhase periodicStrip column : Int),
            row + verticalOffset) ∈ periodicStrip.motif)).toNat] := by
  rw [flatPackedTargetMembershipCode_eval]
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

theorem flatPackedTargetMembershipCode_eval_contains
    (column : WindowColumn) (verticalOffset : Int)
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (row : Int) :
    (flatPackedTargetMembershipCode column verticalOffset).eval
        ([periodicStrip.period, packed.phase,
            periodicStrip.motif.length, Encodable.encode row,
            packed.assignmentWord] ++
          periodicStrip.motif.flatMap
            PeriodicStripFlatEncoding.cellFields) =
      pure
        [(periodicStrip.contains
          ((packed.phase : Int) + column.displacement,
            row + verticalOffset)).toNat] := by
  rw [flatPackedTargetMembershipCode_eval_motif]
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

theorem flatPackedTargetMembershipCode_eval_centerSourceInside
    (periodicStrip : PeriodicStrip)
    (wellFormed : periodicStrip.IsWellFormed)
    (packed : PackedWindowState) (base : Cell)
    (symmetry : SquareSymmetry) (source : Cell)
    (column : WindowColumn)
    (horizontal : (symmetry.act source).1 = column.displacement) :
    (flatPackedTargetMembershipCode column
      (symmetry.act source).2).eval
        ([periodicStrip.period, packed.phase,
            periodicStrip.motif.length, Encodable.encode base.2,
            packed.assignmentWord] ++
          periodicStrip.motif.flatMap
            PeriodicStripFlatEncoding.cellFields) =
      pure
        [(packed.centerSourceInsideBool periodicStrip
          base symmetry source).toNat] := by
  rw [flatPackedTargetMembershipCode_eval_contains
    column (symmetry.act source).2 periodicStrip wellFormed packed base.2]
  simp [PackedWindowState.centerSourceInsideBool,
    Cell.add, horizontal]

end Turing.ToPartrec.Code
