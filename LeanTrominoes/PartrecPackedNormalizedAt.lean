import LeanTrominoes.PartrecCellDecode
import LeanTrominoes.PartrecNatEquality
import LeanTrominoes.PartrecPackedAssignmentPredicates
import LeanTrominoes.PartrecPackedColumnPhase

/-!
# Packed normalization at one motif cell

On native input

`[period, phase, motifCode, column, cellCode, assignmentWord]`,

the program checks the normalization disjunction at one motif occurrence:
the cell lies in the horizontal phase represented by the selected column, or
that column assigns no placement to the cell.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

/-- Decode the cell stored in field four. -/
def packedNormalizedAtCellViewCode : Code :=
  cellViewCode.comp (get 4)

def packedNormalizedAtCellFieldCode (field : Nat) : Code :=
  (get field).comp packedNormalizedAtCellViewCode

@[simp]
theorem packedNormalizedAtCellFieldCode_eval
    (field : Nat) (period phase motifCode column word : Nat)
    (cell : Cell) :
    (packedNormalizedAtCellFieldCode field).eval
        [period, phase, motifCode, column,
          Encodable.encode cell, word] =
      pure
        [[IntEncoding.magnitude cell.1,
            IntEncoding.sign cell.1,
            IntEncoding.magnitude cell.2,
            IntEncoding.sign cell.2][field]?.getD 0] := by
  simp [packedNormalizedAtCellFieldCode,
    packedNormalizedAtCellViewCode]

/-- Return one when the cell's horizontal coordinate is nonnegative. -/
def packedNormalizedAtXNonnegativeCode : Code :=
  isZero (packedNormalizedAtCellFieldCode 1)

@[simp]
theorem packedNormalizedAtXNonnegativeCode_eval
    (period phase motifCode column word : Nat)
    (cell : Cell) :
    packedNormalizedAtXNonnegativeCode.eval
        [period, phase, motifCode, column,
          Encodable.encode cell, word] =
      pure
        [if IntEncoding.sign cell.1 = 0 then 1 else 0] := by
  exact isZero_eval_at
    (packedNormalizedAtCellFieldCode 1) _
    (IntEncoding.sign cell.1) (by simp)

/-- Assemble `[period, phase, column]` for wrapped-phase arithmetic. -/
def packedNormalizedAtPhaseArgumentsCode : Code :=
  prepend (get 0) <|
    prepend (get 1) (get 3)

def packedNormalizedAtPhaseCode : Code :=
  packedColumnPhaseCode.comp
    packedNormalizedAtPhaseArgumentsCode

@[simp]
theorem packedNormalizedAtPhaseCode_eval
    (period phase motifCode column cellCode word : Nat) :
    packedNormalizedAtPhaseCode.eval
        [period, phase, motifCode, column, cellCode, word] =
      pure
        [packedColumnPhaseNumerator period phase column % period] := by
  simp [packedNormalizedAtPhaseCode,
    packedNormalizedAtPhaseArgumentsCode]

/-- Assemble `[xMagnitude, wrappedPhase]`. -/
def packedNormalizedAtXPhaseArgumentsCode : Code :=
  prepend (packedNormalizedAtCellFieldCode 0)
    packedNormalizedAtPhaseCode

def packedNormalizedAtXPhaseEqualCode : Code :=
  natEqCode.comp packedNormalizedAtXPhaseArgumentsCode

@[simp]
theorem packedNormalizedAtXPhaseEqualCode_eval
    (period phase motifCode column word : Nat)
    (cell : Cell) :
    packedNormalizedAtXPhaseEqualCode.eval
        [period, phase, motifCode, column,
          Encodable.encode cell, word] =
      pure
        [if IntEncoding.magnitude cell.1 =
            packedColumnPhaseNumerator period phase column % period
          then 1 else 0] := by
  simp [packedNormalizedAtXPhaseEqualCode,
    packedNormalizedAtXPhaseArgumentsCode]

/-- The horizontal coordinate is the selected column phase. -/
def packedNormalizedAtCoordinateCode : Code :=
  boolAnd packedNormalizedAtXNonnegativeCode
    packedNormalizedAtXPhaseEqualCode

theorem int_eq_natCast_iff_encoding
    (value : Int) (natural : Nat) :
    value = (natural : Int) ↔
      IntEncoding.sign value = 0 ∧
        IntEncoding.magnitude value = natural := by
  cases value <;>
    simp [IntEncoding.sign, IntEncoding.magnitude]

theorem packedNormalizedAtCoordinateTag_eq
    (period phase column : Nat) (cell : Cell) :
    let nonnegative :=
      if IntEncoding.sign cell.1 = 0 then 1 else 0
    let equal :=
      if IntEncoding.magnitude cell.1 =
          packedColumnPhaseNumerator period phase column % period
        then 1 else 0
    (if nonnegative = 0 ∨ equal = 0 then 0 else 1) =
      (decide
        (cell.1 =
          ((packedColumnPhaseNumerator
            period phase column % period : Nat) : Int))).toNat := by
  simp only
  by_cases nonnegativeH :
      IntEncoding.sign cell.1 = 0
  · by_cases equalH :
        IntEncoding.magnitude cell.1 =
          packedColumnPhaseNumerator period phase column % period
    · have coordinateH :=
        (int_eq_natCast_iff_encoding cell.1
          (packedColumnPhaseNumerator
            period phase column % period)).mpr
          ⟨nonnegativeH, equalH⟩
      have decision :
          decide
              (cell.1 =
                ((packedColumnPhaseNumerator
                  period phase column % period : Nat) : Int)) =
            true := by
        rw [decide_eq_true_eq]
        exact coordinateH
      rw [decision]
      simp only [nonnegativeH, equalH, if_pos]
      native_decide
    · have coordinateH :
          ¬ cell.1 =
            ((packedColumnPhaseNumerator
              period phase column % period : Nat) : Int) :=
        fun coordinate =>
          equalH
            ((int_eq_natCast_iff_encoding _ _).mp
              coordinate).2
      have decision :
          decide
              (cell.1 =
                ((packedColumnPhaseNumerator
                  period phase column % period : Nat) : Int)) =
            false :=
        Bool.eq_false_of_not_eq_true (by
          rw [decide_eq_true_eq]
          exact coordinateH)
      rw [decision]
      simp only [nonnegativeH, equalH, if_pos]
      native_decide
  · have coordinateH :
        ¬ cell.1 =
          ((packedColumnPhaseNumerator
            period phase column % period : Nat) : Int) :=
      fun coordinate =>
        nonnegativeH
          ((int_eq_natCast_iff_encoding _ _).mp
            coordinate).1
    have decision :
        decide
            (cell.1 =
              ((packedColumnPhaseNumerator
                period phase column % period : Nat) : Int)) =
          false :=
      Bool.eq_false_of_not_eq_true (by
        rw [decide_eq_true_eq]
        exact coordinateH)
    rw [decision]
    simp only [nonnegativeH, if_false, true_or,
      if_true, Bool.toNat]
    native_decide

@[simp]
theorem packedNormalizedAtCoordinateCode_eval
    (period phase motifCode column word : Nat)
    (cell : Cell) :
    packedNormalizedAtCoordinateCode.eval
        [period, phase, motifCode, column,
          Encodable.encode cell, word] =
      pure
        [(decide
          (cell.1 =
            ((packedColumnPhaseNumerator
              period phase column % period : Nat) : Int))).toNat] := by
  let values :=
    [period, phase, motifCode, column,
      Encodable.encode cell, word]
  let nonnegative :=
    if IntEncoding.sign cell.1 = 0 then 1 else 0
  let equal :=
    if IntEncoding.magnitude cell.1 =
        packedColumnPhaseNumerator period phase column % period
      then 1 else 0
  have combined :=
    boolAnd_eval_at packedNormalizedAtXNonnegativeCode
      packedNormalizedAtXPhaseEqualCode
      values nonnegative equal
      (by simp [values, nonnegative])
      (by simp [values, equal])
  simp only [packedNormalizedAtCoordinateCode]
  have tagEq :
      (decide
        (cell.1 =
          ((packedColumnPhaseNumerator
            period phase column % period : Nat) : Int))).toNat =
        if nonnegative = 0 ∨ equal = 0 then 0 else 1 := by
    by_cases nonnegativeH :
        IntEncoding.sign cell.1 = 0
    · by_cases equalH :
          IntEncoding.magnitude cell.1 =
            packedColumnPhaseNumerator period phase column % period
      · have coordinateH :
            cell.1 =
              ((packedColumnPhaseNumerator
                period phase column % period : Nat) : Int) :=
          (int_eq_natCast_iff_encoding _ _).mpr
            ⟨nonnegativeH, equalH⟩
        have decision :
            decide
                (cell.1 =
                  ((packedColumnPhaseNumerator
                    period phase column % period : Nat) : Int)) =
              true := by
          rw [decide_eq_true_eq]
          exact coordinateH
        rw [decision]
        simp only [nonnegative, equal, nonnegativeH,
          equalH, if_pos]
        native_decide
      · have coordinateH :
            ¬ cell.1 =
              ((packedColumnPhaseNumerator
                period phase column % period : Nat) : Int) :=
          fun coordinate =>
            equalH
              ((int_eq_natCast_iff_encoding _ _).mp
                coordinate).2
        have decision :
            decide
                (cell.1 =
                  ((packedColumnPhaseNumerator
                    period phase column % period : Nat) : Int)) =
              false :=
          Bool.eq_false_of_not_eq_true (by
            rw [decide_eq_true_eq]
            exact coordinateH)
        rw [decision]
        simp only [nonnegative, equal, nonnegativeH,
          equalH, if_pos]
        native_decide
    · have coordinateH :
          ¬ cell.1 =
            ((packedColumnPhaseNumerator
              period phase column % period : Nat) : Int) :=
        fun coordinate =>
          nonnegativeH
            ((int_eq_natCast_iff_encoding _ _).mp
              coordinate).1
      have decision :
          decide
              (cell.1 =
                ((packedColumnPhaseNumerator
                  period phase column % period : Nat) : Int)) =
            false :=
        Bool.eq_false_of_not_eq_true (by
          rw [decide_eq_true_eq]
          exact coordinateH)
      rw [decision]
      simp only [nonnegative, nonnegativeH, if_false,
        true_or, if_true, Bool.toNat]
      native_decide
  rw [tagEq]
  exact combined

/-- Assemble the four-field packed assignment lookup input. -/
def packedNormalizedAtAssignmentArgumentsCode : Code :=
  prepend (get 2) <|
    prepend (get 3) <|
      prepend (get 4) (get 5)

def packedNormalizedAtAssignmentIsNoneCode : Code :=
  packedAssignmentIsNoneCode.comp
    packedNormalizedAtAssignmentArgumentsCode

@[simp]
theorem packedNormalizedAtAssignmentIsNoneCode_eval
    (period phase motifCode column cellCode word : Nat) :
    packedNormalizedAtAssignmentIsNoneCode.eval
        [period, phase, motifCode, column, cellCode, word] =
      packedAssignmentIsNoneCode.eval
        [motifCode, column, cellCode, word] := by
  simp [packedNormalizedAtAssignmentIsNoneCode,
    packedNormalizedAtAssignmentArgumentsCode]

/-- Complete one-cell normalization disjunction. -/
def packedNormalizedAtCode : Code :=
  boolOr packedNormalizedAtCoordinateCode
    packedNormalizedAtAssignmentIsNoneCode

/-- Native result computed by the one-cell predicate. -/
def packedNormalizedAtResult
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : Nat :=
  let coordinate :=
    (decide
      (cell.1 =
        ((packedColumnPhaseNumerator
          period phase column % period : Nat) : Int))).toNat
  let assignmentNone :=
    if (packedAssignmentLookupOutcome
      motif column cell word).2.1 = 0 then 1 else 0
  if coordinate = 0 ∧ assignmentNone = 0 then 0 else 1

@[simp]
theorem packedNormalizedAtCode_eval
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    packedNormalizedAtCode.eval
        [period, phase, Encodable.encode motif, column,
          Encodable.encode cell, word] =
      pure
        [packedNormalizedAtResult
          period phase motif column cell word] := by
  let values :=
    [period, phase, Encodable.encode motif, column,
      Encodable.encode cell, word]
  let coordinate :=
    (decide
      (cell.1 =
        ((packedColumnPhaseNumerator
          period phase column % period : Nat) : Int))).toNat
  let assignmentNone :=
    if (packedAssignmentLookupOutcome
      motif column cell word).2.1 = 0 then 1 else 0
  have combined :=
    boolOr_eval_at packedNormalizedAtCoordinateCode
      packedNormalizedAtAssignmentIsNoneCode
      values coordinate assignmentNone
      (by simp [values, coordinate])
      (by
        simp [values,
          packedNormalizedAtAssignmentIsNoneCode,
          packedNormalizedAtAssignmentArgumentsCode,
          assignmentNone])
  simpa [packedNormalizedAtCode,
    packedNormalizedAtResult, coordinate,
    assignmentNone] using combined

theorem packedNormalizedAtCode_eval_semantic
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (column : WindowColumn) (cell : Cell) :
    packedNormalizedAtCode.eval
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif, column.val,
          Encodable.encode cell, packed.assignmentWord] =
      pure
        [(packed.normalizedAtBool periodicStrip column cell).toNat] := by
  let values :=
    [periodicStrip.period, packed.phase,
      Encodable.encode periodicStrip.motif, column.val,
      Encodable.encode cell, packed.assignmentWord]
  let coordinate :=
    (decide
      (cell.1 =
        (packed.columnPhase periodicStrip column : Int))).toNat
  let assignmentNone :=
    (decide
      (packed.assignmentAtCell periodicStrip column cell =
        none)).toNat
  have phaseEq :
      packedColumnPhaseNumerator periodicStrip.period
            packed.phase column.val %
          periodicStrip.period =
        packed.columnPhase periodicStrip column := by
    simp only [PackedWindowState.columnPhase,
      packedColumnPhaseNumerator, packedColumnPhaseSum]
    congr 1
    omega
  have phaseCastEq :
      ((packedColumnPhaseNumerator periodicStrip.period
            packed.phase column.val %
          periodicStrip.period : Nat) : Int) =
        (packed.columnPhase periodicStrip column : Int) :=
    congrArg Int.ofNat phaseEq
  have coordinateEval :
      packedNormalizedAtCoordinateCode.eval values =
        pure [coordinate] := by
    have generic :=
      packedNormalizedAtCoordinateCode_eval
        periodicStrip.period packed.phase
          (Encodable.encode periodicStrip.motif)
          column.val packed.assignmentWord cell
    rw [phaseCastEq] at generic
    simpa only [values, coordinate] using generic
  have assignmentEval :
      packedNormalizedAtAssignmentIsNoneCode.eval values =
        pure [assignmentNone] := by
    rw [show
      packedNormalizedAtAssignmentIsNoneCode.eval values =
        packedAssignmentIsNoneCode.eval
          [Encodable.encode periodicStrip.motif, column.val,
            Encodable.encode cell, packed.assignmentWord] by
      simp [values]]
    simpa [assignmentNone] using
      packedAssignmentIsNoneCode_eval_semantic
        periodicStrip packed column cell
  have combined :=
    boolOr_eval_at packedNormalizedAtCoordinateCode
      packedNormalizedAtAssignmentIsNoneCode
      values coordinate assignmentNone
      coordinateEval assignmentEval
  simp only [packedNormalizedAtCode]
  change
    (boolOr packedNormalizedAtCoordinateCode
        packedNormalizedAtAssignmentIsNoneCode).eval values =
      pure
        [((decide
            (cell.1 =
              (packed.columnPhase periodicStrip column : Int))) ||
          decide
            (packed.assignmentAtCell periodicStrip column cell =
              none)).toNat]
  have tagEq :
      ((decide
          (cell.1 =
            (packed.columnPhase periodicStrip column : Int))) ||
        decide
          (packed.assignmentAtCell periodicStrip column cell =
            none)).toNat =
        if coordinate = 0 ∧ assignmentNone = 0 then 0 else 1 := by
    by_cases coordinateH :
        cell.1 =
          (packed.columnPhase periodicStrip column : Int) <;>
      by_cases assignmentH :
        packed.assignmentAtCell periodicStrip column cell = none <;>
      simp only [coordinate, assignmentNone,
        coordinateH, assignmentH, decide_true, decide_false] <;>
      native_decide
  rw [tagEq]
  exact combined

theorem packedNormalizedAtResult_eq_semantic
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState)
    (column : WindowColumn) (cell : Cell) :
    packedNormalizedAtResult periodicStrip.period packed.phase
        periodicStrip.motif column.val cell packed.assignmentWord =
      (packed.normalizedAtBool periodicStrip column cell).toNat := by
  have native :=
    packedNormalizedAtCode_eval periodicStrip.period packed.phase
      periodicStrip.motif column.val cell packed.assignmentWord
  have semantic :=
    packedNormalizedAtCode_eval_semantic
      periodicStrip packed column cell
  rw [semantic] at native
  simpa using native.symm

end Turing.ToPartrec.Code
