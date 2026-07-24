import LeanTrominoes.PartrecBooleanSpace
import LeanTrominoes.PartrecCellDecodeSpace
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecPackedAssignmentPredicatesSpace
import LeanTrominoes.PartrecPackedColumnPhaseSpace
import LeanTrominoes.PartrecPackedNormalizedAt
import Mathlib.Tactic.ClearExcept

/-!
# Evaluator-space certificate for one-cell packed normalization

The fitted predicate decodes only the queried cell, computes one wrapped
column phase, and performs one packed assignment lookup.  The coordinate and
absence tags are then combined by fitted Boolean conjunction/disjunction.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes

namespace EvaluatorCodeFits

private def normalizedValues
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : List Nat :=
  [period, phase, Encodable.encode motif, column,
    Encodable.encode cell, word]

def packedNormalizedAtCellViewCost
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : Nat :=
  cellViewCost cell +
    getCost 4
      (normalizedValues period phase motif column cell word)

theorem packedNormalizedAtCellView
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedNormalizedAtCellViewCode
      (normalizedValues period phase motif column cell word)
      [IntEncoding.magnitude cell.1,
        IntEncoding.sign cell.1,
        IntEncoding.magnitude cell.2,
        IntEncoding.sign cell.2]
      (packedNormalizedAtCellViewCost
        period phase motif column cell word) := by
  simpa [Code.packedNormalizedAtCellViewCode,
    packedNormalizedAtCellViewCost,
    normalizedValues] using
    comp (cellView cell)
      (get 4
        (normalizedValues period phase motif column cell word))

def packedNormalizedAtCellFieldCost
    (field period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : Nat :=
  let view :=
    [IntEncoding.magnitude cell.1,
      IntEncoding.sign cell.1,
      IntEncoding.magnitude cell.2,
      IntEncoding.sign cell.2]
  getCost field view +
    packedNormalizedAtCellViewCost
      period phase motif column cell word

theorem packedNormalizedAtCellField
    (field period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    let view :=
      [IntEncoding.magnitude cell.1,
        IntEncoding.sign cell.1,
        IntEncoding.magnitude cell.2,
        IntEncoding.sign cell.2]
    EvaluatorCodeFits
      (Code.packedNormalizedAtCellFieldCode field)
      (normalizedValues period phase motif column cell word)
      [view[field]?.getD 0]
      (packedNormalizedAtCellFieldCost field
        period phase motif column cell word) := by
  simp only
  let view :=
    [IntEncoding.magnitude cell.1,
      IntEncoding.sign cell.1,
      IntEncoding.magnitude cell.2,
      IntEncoding.sign cell.2]
  simpa [Code.packedNormalizedAtCellFieldCode,
    packedNormalizedAtCellFieldCost, view] using
    comp (get field view)
      (packedNormalizedAtCellView
        period phase motif column cell word)

def packedNormalizedAtXNonnegativeCost
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : Nat :=
  let values :=
    normalizedValues period phase motif column cell word
  let sign := IntEncoding.sign cell.1
  isZeroCost values sign
    (packedNormalizedAtCellFieldCost 1
      period phase motif column cell word)

theorem packedNormalizedAtXNonnegative
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedNormalizedAtXNonnegativeCode
      (normalizedValues period phase motif column cell word)
      [if IntEncoding.sign cell.1 = 0 then 1 else 0]
      (packedNormalizedAtXNonnegativeCost
        period phase motif column cell word) := by
  simpa [Code.packedNormalizedAtXNonnegativeCode,
    packedNormalizedAtXNonnegativeCost] using
    isZero
      (packedNormalizedAtCellField 1
        period phase motif column cell word)

def packedNormalizedAtPhaseArgumentsCost
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : Nat :=
  let values :=
    normalizedValues period phase motif column cell word
  let rest :=
    prependCost values [phase] [column]
      (getCost 1 values) (getCost 3 values)
  prependCost values [period] [phase, column]
    (getCost 0 values) rest

theorem packedNormalizedAtPhaseArguments
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedNormalizedAtPhaseArgumentsCode
      (normalizedValues period phase motif column cell word)
      [period, phase, column]
      (packedNormalizedAtPhaseArgumentsCost
        period phase motif column cell word) := by
  let values :=
    normalizedValues period phase motif column cell word
  have rest :=
    prepend (get 1 values) (get 3 values)
  simpa [Code.packedNormalizedAtPhaseArgumentsCode,
    packedNormalizedAtPhaseArgumentsCost,
    prependCost, normalizedValues, values] using
    prepend (get 0 values) rest

def packedNormalizedAtPhaseCost
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : Nat :=
  packedColumnPhaseCost period phase column +
    packedNormalizedAtPhaseArgumentsCost
      period phase motif column cell word

theorem packedNormalizedAtPhase
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedNormalizedAtPhaseCode
      (normalizedValues period phase motif column cell word)
      [Code.packedColumnPhaseNumerator
        period phase column % period]
      (packedNormalizedAtPhaseCost
        period phase motif column cell word) := by
  simpa [Code.packedNormalizedAtPhaseCode,
    packedNormalizedAtPhaseCost] using
    comp (packedColumnPhase period phase column)
      (packedNormalizedAtPhaseArguments
        period phase motif column cell word)

def packedNormalizedAtXPhaseArgumentsCost
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : Nat :=
  let values :=
    normalizedValues period phase motif column cell word
  let columnPhase :=
    Code.packedColumnPhaseNumerator period phase column % period
  prependCost values
    [IntEncoding.magnitude cell.1] [columnPhase]
    (packedNormalizedAtCellFieldCost 0
      period phase motif column cell word)
    (packedNormalizedAtPhaseCost
      period phase motif column cell word)

theorem packedNormalizedAtXPhaseArguments
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedNormalizedAtXPhaseArgumentsCode
      (normalizedValues period phase motif column cell word)
      [IntEncoding.magnitude cell.1,
        Code.packedColumnPhaseNumerator
          period phase column % period]
      (packedNormalizedAtXPhaseArgumentsCost
        period phase motif column cell word) := by
  simpa [Code.packedNormalizedAtXPhaseArgumentsCode,
    packedNormalizedAtXPhaseArgumentsCost,
    prependCost] using
    prepend
      (packedNormalizedAtCellField 0
        period phase motif column cell word)
      (packedNormalizedAtPhase
        period phase motif column cell word)

def packedNormalizedAtXPhaseEqualCost
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : Nat :=
  let columnPhase :=
    Code.packedColumnPhaseNumerator period phase column % period
  natEqCost (IntEncoding.magnitude cell.1) columnPhase +
    packedNormalizedAtXPhaseArgumentsCost
      period phase motif column cell word

theorem packedNormalizedAtXPhaseEqual
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    let columnPhase :=
      Code.packedColumnPhaseNumerator period phase column % period
    EvaluatorCodeFits Code.packedNormalizedAtXPhaseEqualCode
      (normalizedValues period phase motif column cell word)
      [if IntEncoding.magnitude cell.1 = columnPhase
        then 1 else 0]
      (packedNormalizedAtXPhaseEqualCost
        period phase motif column cell word) := by
  simp only
  simpa [Code.packedNormalizedAtXPhaseEqualCode,
    packedNormalizedAtXPhaseEqualCost] using
    comp
      (natEq (IntEncoding.magnitude cell.1)
        (Code.packedColumnPhaseNumerator
          period phase column % period))
      (packedNormalizedAtXPhaseArguments
        period phase motif column cell word)

def packedNormalizedAtCoordinateCost
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : Nat :=
  let values :=
    normalizedValues period phase motif column cell word
  let nonnegative :=
    if IntEncoding.sign cell.1 = 0 then 1 else 0
  let equal :=
    if IntEncoding.magnitude cell.1 =
        Code.packedColumnPhaseNumerator period phase column % period
      then 1 else 0
  boolAndCost values nonnegative equal
    (packedNormalizedAtXNonnegativeCost
      period phase motif column cell word)
    (packedNormalizedAtXPhaseEqualCost
      period phase motif column cell word)

theorem packedNormalizedAtCoordinate
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    let nonnegative :=
      if IntEncoding.sign cell.1 = 0 then 1 else 0
    let equal :=
      if IntEncoding.magnitude cell.1 =
          Code.packedColumnPhaseNumerator period phase column % period
        then 1 else 0
    EvaluatorCodeFits Code.packedNormalizedAtCoordinateCode
      (normalizedValues period phase motif column cell word)
      [if nonnegative = 0 ∨ equal = 0 then 0 else 1]
      (packedNormalizedAtCoordinateCost
        period phase motif column cell word) := by
  simp only
  simpa [Code.packedNormalizedAtCoordinateCode,
    packedNormalizedAtCoordinateCost] using
    boolAnd
      (packedNormalizedAtXNonnegative
        period phase motif column cell word)
      (packedNormalizedAtXPhaseEqual
        period phase motif column cell word)

def packedNormalizedAtAssignmentArgumentsCost
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : Nat :=
  let values :=
    normalizedValues period phase motif column cell word
  let rest5 :=
    prependCost values [Encodable.encode cell] [word]
      (getCost 4 values) (getCost 5 values)
  let rest3 :=
    prependCost values [column]
      [Encodable.encode cell, word]
      (getCost 3 values) rest5
  prependCost values [Encodable.encode motif]
    [column, Encodable.encode cell, word]
    (getCost 2 values) rest3

theorem packedNormalizedAtAssignmentArguments
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    EvaluatorCodeFits
      Code.packedNormalizedAtAssignmentArgumentsCode
      (normalizedValues period phase motif column cell word)
      [Encodable.encode motif, column,
        Encodable.encode cell, word]
      (packedNormalizedAtAssignmentArgumentsCost
        period phase motif column cell word) := by
  let values :=
    normalizedValues period phase motif column cell word
  have rest5 := prepend (get 4 values) (get 5 values)
  have rest3 := prepend (get 3 values) rest5
  simpa [Code.packedNormalizedAtAssignmentArgumentsCode,
    packedNormalizedAtAssignmentArgumentsCost,
    prependCost, normalizedValues, values] using
    prepend (get 2 values) rest3

def packedNormalizedAtAssignmentIsNoneCost
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : Nat :=
  packedAssignmentIsNoneCost motif column cell word +
    packedNormalizedAtAssignmentArgumentsCost
      period phase motif column cell word

theorem packedNormalizedAtAssignmentIsNone
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    let digit :=
      (Code.packedAssignmentLookupOutcome motif column cell word).2.1
    EvaluatorCodeFits Code.packedNormalizedAtAssignmentIsNoneCode
      (normalizedValues period phase motif column cell word)
      [if digit = 0 then 1 else 0]
      (packedNormalizedAtAssignmentIsNoneCost
        period phase motif column cell word) := by
  simp only
  simpa [Code.packedNormalizedAtAssignmentIsNoneCode,
    packedNormalizedAtAssignmentIsNoneCost] using
    comp (packedAssignmentIsNone motif column cell word)
      (packedNormalizedAtAssignmentArguments
        period phase motif column cell word)

def packedNormalizedAtCost
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) : Nat :=
  let values :=
    normalizedValues period phase motif column cell word
  let nonnegative :=
    if IntEncoding.sign cell.1 = 0 then 1 else 0
  let equal :=
    if IntEncoding.magnitude cell.1 =
        Code.packedColumnPhaseNumerator period phase column % period
      then 1 else 0
  let coordinate :=
    if nonnegative = 0 ∨ equal = 0 then 0 else 1
  let assignmentNone :=
    if (Code.packedAssignmentLookupOutcome
      motif column cell word).2.1 = 0 then 1 else 0
  boolOrCost values coordinate assignmentNone
    (packedNormalizedAtCoordinateCost
      period phase motif column cell word)
    (packedNormalizedAtAssignmentIsNoneCost
      period phase motif column cell word)

theorem packedNormalizedAt
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    let nonnegative :=
      if IntEncoding.sign cell.1 = 0 then 1 else 0
    let equal :=
      if IntEncoding.magnitude cell.1 =
          Code.packedColumnPhaseNumerator period phase column % period
        then 1 else 0
    let coordinate :=
      if nonnegative = 0 ∨ equal = 0 then 0 else 1
    let assignmentNone :=
      if (Code.packedAssignmentLookupOutcome
        motif column cell word).2.1 = 0 then 1 else 0
    EvaluatorCodeFits Code.packedNormalizedAtCode
      (normalizedValues period phase motif column cell word)
      [if coordinate = 0 ∧ assignmentNone = 0 then 0 else 1]
      (packedNormalizedAtCost
        period phase motif column cell word) := by
  simp only
  simpa [Code.packedNormalizedAtCode,
    packedNormalizedAtCost] using
    boolOr
      (packedNormalizedAtCoordinate
        period phase motif column cell word)
      (packedNormalizedAtAssignmentIsNone
        period phase motif column cell word)

theorem packedNormalizedAtResult
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    EvaluatorCodeFits Code.packedNormalizedAtCode
      (normalizedValues period phase motif column cell word)
      [Code.packedNormalizedAtResult
        period phase motif column cell word]
      (packedNormalizedAtCost
        period phase motif column cell word) := by
  let nonnegative :=
    if IntEncoding.sign cell.1 = 0 then 1 else 0
  let equal :=
    if IntEncoding.magnitude cell.1 =
        Code.packedColumnPhaseNumerator period phase column % period
      then 1 else 0
  let coordinateArithmetic :=
    if nonnegative = 0 ∨ equal = 0 then 0 else 1
  let coordinateNative :=
    (decide
      (cell.1 =
        ((Code.packedColumnPhaseNumerator
          period phase column % period : Nat) : Int))).toNat
  let assignmentNone :=
    if (Code.packedAssignmentLookupOutcome
      motif column cell word).2.1 = 0 then 1 else 0
  have coordinateEq :
      coordinateArithmetic = coordinateNative := by
    simpa [nonnegative, equal,
      coordinateArithmetic, coordinateNative] using
    Code.packedNormalizedAtCoordinateTag_eq
      period phase column cell
  have outputEq :
      (if coordinateArithmetic = 0 ∧ assignmentNone = 0
        then 0 else 1) =
        Code.packedNormalizedAtResult
          period phase motif column cell word := by
    change
      (if coordinateArithmetic = 0 ∧ assignmentNone = 0
        then 0 else 1) =
      if coordinateNative = 0 ∧ assignmentNone = 0
        then 0 else 1
    by_cases left :
        coordinateArithmetic = 0 ∧ assignmentNone = 0
    · have right :
          coordinateNative = 0 ∧ assignmentNone = 0 := by
        exact ⟨by omega, left.2⟩
      simp [left, right]
    · have right :
          ¬(coordinateNative = 0 ∧ assignmentNone = 0) := by
        intro right
        exact left ⟨by omega, right.2⟩
      simp [left, right]
  have fitted :=
    packedNormalizedAt period phase motif column cell word
  simpa only [nonnegative, equal, coordinateArithmetic,
    assignmentNone, outputEq] using fitted

def packedNormalizedAtSpaceBound
    (period phase motifCode column cellCode word : Nat) : Nat :=
  1000000000000000000000000000000 *
    (encodedListSpace
      [1024 * (period + phase +
        motifCode + motifCode + motifCode +
        cellCode + column + word + 100) + 1000] + 1)

private theorem packedNormalizedAtNonnegativeBudgetGrowth
    (unit : Nat) (positive : 1 ≤ unit) :
    1000 * (1000000000000000000 * unit + 1) ≤
      10000000000000000000000 * unit := by
  omega

private theorem packedNormalizedAtCoordinateBudgetGrowth
    (unit : Nat) (positive : 1 ≤ unit) :
    1000 * (10000000000000000000000 * unit + 1) ≤
      100000000000000000000000000 * unit := by
  omega

private theorem packedNormalizedAtFinalBudgetGrowth
    (unit : Nat) (positive : 1 ≤ unit) :
    1000 * (100000000000000000000000000 * unit + 1) ≤
      1000000000000000000000000000000 * unit := by
  omega

private theorem tailCost_le_linear (values : List Nat) :
    tailCost values ≤
      3 * (encodedListSpace values + 1) := by
  have tailSpace := encodedListSpace_tail_le values
  simp only [tailCost]
  omega

private theorem getCost_le_linear
    (index : Nat) (values : List Nat) :
    getCost index values ≤
      (10000 * (index + 1)) *
        (encodedListSpace values + 1) := by
  induction index generalizing values with
  | zero =>
      simpa using getZeroCost_le values
  | succ index induction =>
      have recurrence :
          getCost (index + 1) values =
            getCost index values.tail + tailCost values := by
        cases values <;>
          simp [getCost, dropCost, Nat.add_assoc]
      rw [recurrence]
      calc
        getCost index values.tail + tailCost values ≤
            (10000 * (index + 1)) *
                (encodedListSpace values.tail + 1) +
              3 * (encodedListSpace values + 1) :=
          Nat.add_le_add (induction values.tail)
            (tailCost_le_linear values)
        _ ≤
            (10000 * (index + 1)) *
                (encodedListSpace values + 1) +
              3 * (encodedListSpace values + 1) := by
          gcongr
          exact encodedListSpace_tail_le values
        _ ≤
            (10000 * (index + 1)) *
                (encodedListSpace values + 1) +
              10000 * (encodedListSpace values + 1) := by
          gcongr
          norm_num
        _ =
            (10000 * (index + 1 + 1)) *
              (encodedListSpace values + 1) := by
          ring

private theorem intEncoding_sign_le_one (coordinate : Int) :
    IntEncoding.sign coordinate ≤ 1 := by
  cases coordinate <;> simp [IntEncoding.sign]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 100000 in
theorem packedNormalizedAtCost_le_linear
    (period phase : Nat) (motif : List Cell)
    (column : Nat) (cell : Cell) (word : Nat) :
    packedNormalizedAtCost period phase motif column cell word ≤
      packedNormalizedAtSpaceBound period phase
        (Encodable.encode motif) column
        (Encodable.encode cell) word := by
  rcases cell with ⟨x, y⟩
  let motifCode := Encodable.encode motif
  let xCode := Encodable.encode x
  let yCode := Encodable.encode y
  let cellCode := Encodable.encode (x, y)
  let xMagnitude := IntEncoding.magnitude x
  let xSign := IntEncoding.sign x
  let yMagnitude := IntEncoding.magnitude y
  let ySign := IntEncoding.sign y
  let columnPhase :=
    Code.packedColumnPhaseNumerator period phase column % period
  let values :=
    normalizedValues period phase motif column (x, y) word
  let limit :=
    1024 * (period + phase +
      motifCode + motifCode + motifCode +
      cellCode + column + word + 100) + 1000
  let unit := encodedListSpace [limit] + 1
  change
    packedNormalizedAtCost period phase motif column (x, y) word ≤
      1000000000000000000000000000000 * unit
  have unitPositive : 1 ≤ unit := by
    simp [unit, encodedListSpace_cons,
      encodedListSpace_nil]
  have unitEq :
      unit = (Computability.encodeNat limit).length + 2 := by
    simp [unit, encodedListSpace_cons,
      encodedListSpace_nil]
  have cellCodeEq : cellCode = Nat.pair xCode yCode := rfl
  have xCodeCell : xCode ≤ cellCode := by
    rw [cellCodeEq]
    exact Nat.left_le_pair _ _
  have yCodeCell : yCode ≤ cellCode := by
    rw [cellCodeEq]
    exact Nat.right_le_pair _ _
  have xIdentity := Nat.bodd_add_div2 xCode
  have yIdentity := Nat.bodd_add_div2 yCode
  have xMagnitudeEq : xMagnitude = xCode.div2 := by
    simp [xMagnitude, xCode]
  have yMagnitudeEq : yMagnitude = yCode.div2 := by
    simp [yMagnitude, yCode]
  have xMagnitudeCode : xMagnitude ≤ xCode := by
    rw [xMagnitudeEq]
    omega
  have yMagnitudeCode : yMagnitude ≤ yCode := by
    rw [yMagnitudeEq]
    omega
  have xSignOne : xSign ≤ 1 := by
    simpa [xSign] using intEncoding_sign_le_one x
  have ySignOne : ySign ≤ 1 := by
    simpa [ySign] using intEncoding_sign_le_one y
  have periodBound : period ≤ limit := by
    simp only [limit]
    omega
  have phaseBound : phase ≤ limit := by
    simp only [limit]
    omega
  have motifBound : motifCode ≤ limit := by
    simp only [limit]
    omega
  have cellBound : cellCode ≤ limit := by
    simp only [limit]
    omega
  have columnBound : column ≤ limit := by
    simp only [limit]
    omega
  have wordBound : word ≤ limit := by
    simp only [limit]
    omega
  have xMagnitudeBound : xMagnitude ≤ limit :=
    xMagnitudeCode.trans (xCodeCell.trans cellBound)
  have yMagnitudeBound : yMagnitude ≤ limit :=
    yMagnitudeCode.trans (yCodeCell.trans cellBound)
  have xSignBound : xSign ≤ limit := by
    simp only [limit]
    omega
  have ySignBound : ySign ≤ limit := by
    simp only [limit]
    omega
  have phaseNumeratorBound :
      Code.packedColumnPhaseNumerator period phase column ≤ limit := by
    simp only [Code.packedColumnPhaseNumerator,
      Code.packedColumnPhaseSum, limit]
    omega
  have phaseNumeratorSuccBound :
      Code.packedColumnPhaseNumerator period phase column + 1 ≤
        limit := by
    simp only [Code.packedColumnPhaseNumerator,
      Code.packedColumnPhaseSum, limit]
    omega
  have columnPhaseBound : columnPhase ≤ limit :=
    (Nat.mod_le
      (Code.packedColumnPhaseNumerator period phase column)
      period).trans phaseNumeratorBound
  have xMagnitudeCell : xMagnitude ≤ cellCode :=
    xMagnitudeCode.trans xCodeCell
  have columnPhaseSmall :
      columnPhase ≤ phase + column + (period + period) := by
    have phaseLe :=
      Nat.mod_le
        (Code.packedColumnPhaseNumerator
          period phase column) period
    simp only [columnPhase,
      Code.packedColumnPhaseNumerator,
      Code.packedColumnPhaseSum] at phaseLe ⊢
    omega
  have periodBits := encodeNat_length_mono periodBound
  have phaseBits := encodeNat_length_mono phaseBound
  have motifBits := encodeNat_length_mono motifBound
  have cellBits := encodeNat_length_mono cellBound
  have columnBits := encodeNat_length_mono columnBound
  have wordBits := encodeNat_length_mono wordBound
  have xMagnitudeBits :=
    encodeNat_length_mono xMagnitudeBound
  have yMagnitudeBits :=
    encodeNat_length_mono yMagnitudeBound
  have xSignBits := encodeNat_length_mono xSignBound
  have ySignBits := encodeNat_length_mono ySignBound
  have columnPhaseBits :=
    encodeNat_length_mono columnPhaseBound
  have periodSuccBits :=
    encodeNat_length_mono
      (show period + 1 ≤ limit by
        simp only [limit]
        clear * - period
        omega)
  have phaseSuccBits :=
    encodeNat_length_mono
      (show phase + 1 ≤ limit by
        simp only [limit]
        clear * - period
        omega)
  have motifSuccBits :=
    encodeNat_length_mono
      (show motifCode + 1 ≤ limit by
        simp only [limit]
        clear * - period
        omega)
  have cellSuccBits :=
    encodeNat_length_mono
      (show cellCode + 1 ≤ limit by
        simp only [limit]
        clear * - period
        omega)
  have columnSuccBits :=
    encodeNat_length_mono
      (show column + 1 ≤ limit by
        simp only [limit]
        clear * - period
        omega)
  have wordSuccBits :=
    encodeNat_length_mono
      (show word + 1 ≤ limit by
        simp only [limit]
        clear * - period
        omega)
  have xMagnitudeSuccBits :=
    encodeNat_length_mono
      (show xMagnitude + 1 ≤ limit by
        simp only [limit]
        clear * - xMagnitudeCode xCodeCell
        omega)
  have yMagnitudeSuccBits :=
    encodeNat_length_mono
      (show yMagnitude + 1 ≤ limit by
        simp only [limit]
        clear * - yMagnitudeCode yCodeCell
        omega)
  have xSignSuccBits :=
    encodeNat_length_mono
      (show xSign + 1 ≤ limit by
        simp only [limit]
        clear * - xSignOne
        omega)
  have ySignSuccBits :=
    encodeNat_length_mono
      (show ySign + 1 ≤ limit by
        simp only [limit]
        clear * - ySignOne
        omega)
  have columnPhaseSuccBits :=
    encodeNat_length_mono
      (show columnPhase + 1 ≤ limit by
        have phaseLe :=
          Nat.mod_le
            (Code.packedColumnPhaseNumerator
              period phase column) period
        exact (Nat.add_le_add_right phaseLe 1).trans
          phaseNumeratorSuccBound)
  have motifBitsRaw :
      (Computability.encodeNat
        (Encodable.encode motif)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [motifCode] using motifBits
  have cellBitsRaw :
      (Computability.encodeNat
        (Encodable.encode (x, y))).length ≤
        (Computability.encodeNat limit).length := by
    simpa [cellCode] using cellBits
  have motifSuccBitsRaw :
      (Computability.encodeNat
        (Encodable.encode motif + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [motifCode] using motifSuccBits
  have cellSuccBitsRaw :
      (Computability.encodeNat
        (Encodable.encode (x, y) + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [cellCode] using cellSuccBits
  have cellPairBitsRaw :
      (Computability.encodeNat
        (Nat.pair (Encodable.encode x)
          (Encodable.encode y))).length ≤
        (Computability.encodeNat limit).length := by
    simpa using cellBitsRaw
  have cellPairSuccBitsRaw :
      (Computability.encodeNat
        (Nat.pair (Encodable.encode x)
          (Encodable.encode y) + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa using cellSuccBitsRaw
  have xMagnitudeBitsRaw :
      (Computability.encodeNat
        (IntEncoding.magnitude x)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [xMagnitude] using xMagnitudeBits
  have yMagnitudeBitsRaw :
      (Computability.encodeNat
        (IntEncoding.magnitude y)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [yMagnitude] using yMagnitudeBits
  have xSignBitsRaw :
      (Computability.encodeNat
        (IntEncoding.sign x)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [xSign] using xSignBits
  have ySignBitsRaw :
      (Computability.encodeNat
        (IntEncoding.sign y)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [ySign] using ySignBits
  have xMagnitudeSuccBitsRaw :
      (Computability.encodeNat
        (IntEncoding.magnitude x + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [xMagnitude] using xMagnitudeSuccBits
  have yMagnitudeSuccBitsRaw :
      (Computability.encodeNat
        (IntEncoding.magnitude y + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [yMagnitude] using yMagnitudeSuccBits
  have xSignSuccBitsRaw :
      (Computability.encodeNat
        (IntEncoding.sign x + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [xSign] using xSignSuccBits
  have ySignSuccBitsRaw :
      (Computability.encodeNat
        (IntEncoding.sign y + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [ySign] using ySignSuccBits
  have columnPhaseBitsRaw :
      (Computability.encodeNat
        (Code.packedColumnPhaseNumerator
          period phase column % period)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [columnPhase] using columnPhaseBits
  have columnPhaseSuccBitsRaw :
      (Computability.encodeNat
        (Code.packedColumnPhaseNumerator period
          phase column % period + 1)).length ≤
        (Computability.encodeNat limit).length := by
    simpa [columnPhase] using columnPhaseSuccBits
  have zeroBits :
      (Computability.encodeNat 0).length = 0 := rfl
  have oneBits :
      (Computability.encodeNat 1).length = 1 := rfl
  have twoBits :
      (Computability.encodeNat 2).length = 2 := rfl
  have valuesSpace :
      encodedListSpace values ≤ 10 * unit := by
    simp only [values, normalizedValues,
      encodedListSpace_cons, encodedListSpace_nil,
      unitEq]
    clear * - periodBits phaseBits motifBitsRaw
      cellBitsRaw columnBits wordBits unitEq
    omega
  have valuesSpaceRaw :
      encodedListSpace
        (normalizedValues period phase motif column (x, y) word) ≤
          10 * unit := by
    simpa [values] using valuesSpace
  have getGlobal (index : Nat) (indexBound : index < 6) :
      getCost index values ≤
        1000000 * unit := by
    have coefficientBound :
        10000 * (index + 1) ≤ 60000 := by
      omega
    have getLocal := getCost_le_linear index values
    have localUniform :
        getCost index values ≤
          60000 * (encodedListSpace values + 1) := by
      exact getLocal.trans
        (Nat.mul_le_mul_right
          (encodedListSpace values + 1) coefficientBound)
    clear * - localUniform valuesSpace unitPositive
    omega
  have getZero := getGlobal 0 (by omega)
  have getOne := getGlobal 1 (by omega)
  have getTwo := getGlobal 2 (by omega)
  have getThree := getGlobal 3 (by omega)
  have getFour := getGlobal 4 (by omega)
  have getFive := getGlobal 5 (by omega)
  have getZeroRaw :
      getCost 0
          (normalizedValues period phase motif column (x, y) word) ≤
        1000000 * unit := by
    simpa [values] using getZero
  have getOneRaw :
      getCost 1
          (normalizedValues period phase motif column (x, y) word) ≤
        1000000 * unit := by
    simpa [values] using getOne
  have getTwoRaw :
      getCost 2
          (normalizedValues period phase motif column (x, y) word) ≤
        1000000 * unit := by
    simpa [values] using getTwo
  have getThreeRaw :
      getCost 3
          (normalizedValues period phase motif column (x, y) word) ≤
        1000000 * unit := by
    simpa [values] using getThree
  have getFourRaw :
      getCost 4
          (normalizedValues period phase motif column (x, y) word) ≤
        1000000 * unit := by
    simpa [values] using getFour
  have getFiveRaw :
      getCost 5
          (normalizedValues period phase motif column (x, y) word) ≤
        1000000 * unit := by
    simpa [values] using getFive
  have cellViewArgument : 2 * cellCode + 4 ≤ limit := by
    simp only [limit]
    omega
  have cellViewArgumentBits :=
    encodeNat_length_mono cellViewArgument
  have cellViewLocal := cellViewCost_le_linear (x, y)
  have cellViewLocalAligned :
      cellViewCost (x, y) ≤
        12000000000 *
          (encodedListSpace [2 * cellCode + 4] + 1) := by
    simpa [cellCode] using cellViewLocal
  have cellViewGlobal :
      cellViewCost (x, y) ≤
        12000000000 * unit := by
    simp only [unitEq,
      encodedListSpace_cons,
      encodedListSpace_nil] at cellViewLocalAligned ⊢
    clear * - cellViewLocalAligned
      cellViewArgumentBits unitEq
    omega
  have cellViewWrapped :
      packedNormalizedAtCellViewCost period phase motif
          column (x, y) word ≤
        1000000000000000 * unit := by
    simp only [packedNormalizedAtCellViewCost]
    clear * - cellViewGlobal getFourRaw
    omega
  have fieldZero :
      packedNormalizedAtCellFieldCost 0 period phase motif
          column (x, y) word ≤
        100000000000000000 * unit := by
    simp [packedNormalizedAtCellFieldCost,
      getCost, dropCost, headCost, idCost, nilCost,
      tailCost, zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      unitEq, zeroBits]
    clear * - cellViewWrapped xMagnitudeBitsRaw
      xSignBitsRaw yMagnitudeBitsRaw ySignBitsRaw
      xMagnitudeSuccBitsRaw xSignSuccBitsRaw
      yMagnitudeSuccBitsRaw ySignSuccBitsRaw
      zeroBits oneBits twoBits unitEq
    omega
  have fieldOne :
      packedNormalizedAtCellFieldCost 1 period phase motif
          column (x, y) word ≤
        100000000000000000 * unit := by
    simp [packedNormalizedAtCellFieldCost,
      getCost, dropCost, headCost, idCost, nilCost,
      tailCost, zeroPrimeCost, succCost,
      encodedListSpace_cons, encodedListSpace_nil,
      unitEq, zeroBits]
    clear * - cellViewWrapped xMagnitudeBitsRaw
      xSignBitsRaw yMagnitudeBitsRaw ySignBitsRaw
      xMagnitudeSuccBitsRaw xSignSuccBitsRaw
      yMagnitudeSuccBitsRaw ySignSuccBitsRaw
      zeroBits oneBits twoBits unitEq
    omega
  let nonnegative := if xSign = 0 then 1 else 0
  have nonnegativeBound : nonnegative ≤ 1 := by
    simp only [nonnegative]
    split <;> omega
  let nonnegativeBudget :=
    1000000000000000000 * unit
  have nonnegativeRaw :=
    isZeroCost_le_budget values xSign
      (packedNormalizedAtCellFieldCost 1 period phase motif
        column (x, y) word)
      nonnegativeBudget
      (by
        simp only [nonnegativeBudget]
        clear * - valuesSpace unitPositive unitEq
        omega)
      (by
        simp only [nonnegativeBudget, encodedListSpace_cons,
          encodedListSpace_nil, unitEq]
        clear * - xSignBits unitEq
        omega)
      (by
        have predLe := Nat.pred_le xSign
        have predBound : xSign.pred ≤ limit :=
          predLe.trans xSignBound
        have predBits := encodeNat_length_mono predBound
        simp only [nonnegativeBudget, encodedListSpace_cons,
          encodedListSpace_nil, unitEq]
        clear * - predBits unitEq
        omega)
      (by
        simp [values, normalizedValues,
          nonnegativeBudget, unitEq]
        clear * - periodBits unitEq
        omega)
      (by
        simp [values, normalizedValues,
          nonnegativeBudget, unitEq]
        clear * - periodSuccBits unitEq
        omega)
      (by
        simp only [nonnegativeBudget]
        clear * - fieldOne unitPositive
        omega)
      (by
        simp only [nonnegativeBudget]
        clear * - unitPositive
        omega)
  have xNonnegativeGlobal :
      packedNormalizedAtXNonnegativeCost period phase motif
          column (x, y) word ≤
        10000000000000000000000 * unit := by
    have exact :
        packedNormalizedAtXNonnegativeCost period phase motif
            column (x, y) word ≤
          1000 * (nonnegativeBudget + 1) := by
      simpa [packedNormalizedAtXNonnegativeCost,
        values, xSign, nonnegative] using nonnegativeRaw
    exact exact.trans
      (packedNormalizedAtNonnegativeBudgetGrowth
        unit unitPositive)
  have phaseArguments :
      packedNormalizedAtPhaseArgumentsCost period phase motif
          column (x, y) word ≤
        1000000000000000 * unit := by
    simp [packedNormalizedAtPhaseArgumentsCost,
      prependCost,
      encodedListSpace_cons, encodedListSpace_nil,
      unitEq]
    clear * - getZeroRaw getOneRaw getThreeRaw
      valuesSpaceRaw
      periodBits phaseBits columnBits
      periodSuccBits phaseSuccBits columnSuccBits
      zeroBits oneBits twoBits unitEq
    omega
  have phaseArgument :
      128 * (period + phase + column + 32) + 200 ≤ limit := by
    simp only [limit]
    omega
  have phaseArgumentBits :=
    encodeNat_length_mono phaseArgument
  have phaseLocal :=
    packedColumnPhaseCost_le_linear period phase column
  have phaseGlobal :
      packedColumnPhaseCost period phase column ≤
        10000000000000000 * unit := by
    simp only [unitEq, encodedListSpace_cons,
      encodedListSpace_nil] at phaseLocal ⊢
    clear * - phaseLocal phaseArgumentBits unitEq
    omega
  have phaseCostGlobal :
      packedNormalizedAtPhaseCost period phase motif
          column (x, y) word ≤
        1000000000000000000 * unit := by
    simp only [packedNormalizedAtPhaseCost]
    clear * - phaseGlobal phaseArguments
    omega
  have xPhaseArguments :
      packedNormalizedAtXPhaseArgumentsCost period phase motif
          column (x, y) word ≤
        100000000000000000000 * unit := by
    simp [packedNormalizedAtXPhaseArgumentsCost,
      prependCost, encodedListSpace_cons,
      encodedListSpace_nil, unitEq]
    clear * - fieldZero phaseCostGlobal
      valuesSpaceRaw xMagnitudeBitsRaw
      columnPhaseBitsRaw xMagnitudeSuccBitsRaw
      columnPhaseSuccBitsRaw zeroBits oneBits twoBits
      unitEq
    omega
  have equalityArgument :
      2 * (xMagnitude + columnPhase) + 4 ≤ limit := by
    simp only [limit]
    clear * - xMagnitudeCell columnPhaseSmall
    omega
  have equalityArgumentBits :=
    encodeNat_length_mono equalityArgument
  have equalityLocal :=
    natEqCost_le_linear xMagnitude columnPhase
  have equalityGlobal :
      natEqCost xMagnitude columnPhase ≤
        1000000000000 * unit := by
    simp only [unitEq, encodedListSpace_cons,
      encodedListSpace_nil] at equalityLocal ⊢
    clear * - equalityLocal equalityArgumentBits unitEq
    omega
  have xPhaseEqualGlobal :
      packedNormalizedAtXPhaseEqualCost period phase motif
          column (x, y) word ≤
        1000000000000000000000 * unit := by
    simp only [packedNormalizedAtXPhaseEqualCost]
    have equalityGlobalRaw :
        natEqCost (IntEncoding.magnitude x)
            (Code.packedColumnPhaseNumerator
              period phase column % period) ≤
          1000000000000 * unit := by
      simpa [xMagnitude, columnPhase] using equalityGlobal
    clear * - equalityGlobalRaw xPhaseArguments
    omega
  let equal := if xMagnitude = columnPhase then 1 else 0
  have equalBound : equal ≤ 1 := by
    simp only [equal]
    split <;> omega
  let coordinateBudget :=
    10000000000000000000000 * unit
  have coordinateRaw :=
    boolAndCost_le_budget values nonnegative equal
      (packedNormalizedAtXNonnegativeCost period phase motif
        column (x, y) word)
      (packedNormalizedAtXPhaseEqualCost period phase motif
        column (x, y) word)
      coordinateBudget nonnegativeBound equalBound
      (by
        simp only [coordinateBudget]
        clear * - valuesSpace unitPositive
        omega)
      (by
        simp [values, normalizedValues,
          coordinateBudget, unitEq]
        clear * - periodBits unitEq
        omega)
      (by
        simp [values, normalizedValues,
          coordinateBudget, unitEq]
        clear * - periodSuccBits unitEq
        omega)
      (by
        simp only [coordinateBudget]
        clear * - xNonnegativeGlobal unitPositive
        omega)
      (by
        simp only [coordinateBudget]
        clear * - xPhaseEqualGlobal unitPositive
        omega)
      (by
        simp only [coordinateBudget]
        clear * - unitPositive
        omega)
  have coordinateGlobal :
      packedNormalizedAtCoordinateCost period phase motif
          column (x, y) word ≤
        100000000000000000000000000 * unit := by
    have exact :
        packedNormalizedAtCoordinateCost period phase motif
            column (x, y) word ≤
          1000 * (coordinateBudget + 1) := by
      simpa [packedNormalizedAtCoordinateCost,
        values, nonnegative, equal, xSign,
        xMagnitude, columnPhase] using coordinateRaw
    exact exact.trans
      (packedNormalizedAtCoordinateBudgetGrowth
        unit unitPositive)
  have assignmentGetCosts :
      getCost 2
          (normalizedValues period phase motif column (x, y) word) +
        getCost 3
          (normalizedValues period phase motif column (x, y) word) +
        getCost 4
          (normalizedValues period phase motif column (x, y) word) +
        getCost 5
          (normalizedValues period phase motif column (x, y) word) ≤
        4000000 * unit := by
    clear * - getTwoRaw getThreeRaw getFourRaw getFiveRaw
    omega
  have assignmentArguments :
      packedNormalizedAtAssignmentArgumentsCost period phase motif
          column (x, y) word ≤
        10000000 * unit := by
    simp [packedNormalizedAtAssignmentArgumentsCost,
      prependCost,
      encodedListSpace_cons, encodedListSpace_nil,
      unitEq]
    clear * - assignmentGetCosts valuesSpaceRaw
      motifBitsRaw cellPairBitsRaw columnBits wordBits
      unitEq
    omega
  have noneArgument :
      32 * (motifCode + motifCode + motifCode +
        cellCode + column + word + 40 + 32) + 200 ≤ limit := by
    simp only [limit]
    omega
  have noneArgumentBits :=
    encodeNat_length_mono noneArgument
  have noneLocal :=
    packedAssignmentIsNoneCost_le_linear
      motif column (x, y) word
  have noneGlobal :
      packedAssignmentIsNoneCost motif column (x, y) word ≤
        1000000000000000000000000 * unit := by
    have noneLocalAligned :
        packedAssignmentIsNoneCost motif column (x, y) word ≤
          1000000000000000000000000 *
            (encodedListSpace
              [32 * (motifCode + motifCode + motifCode +
                cellCode + column + word + 40 + 32) + 200] +
              1) := by
      simpa [packedAssignmentIsNoneSpaceBound,
        motifCode, cellCode] using noneLocal
    simp only [unitEq, encodedListSpace_cons,
      encodedListSpace_nil] at noneLocalAligned ⊢
    clear * - noneLocalAligned noneArgumentBits unitEq
    omega
  have assignmentNoneGlobal :
      packedNormalizedAtAssignmentIsNoneCost period phase motif
          column (x, y) word ≤
        10000000000000000000000000 * unit := by
    simp only [packedNormalizedAtAssignmentIsNoneCost]
    clear * - noneGlobal assignmentArguments
    omega
  let coordinate :=
    if nonnegative = 0 ∨ equal = 0 then 0 else 1
  let assignmentNone :=
    if (Code.packedAssignmentLookupOutcome
      motif column (x, y) word).2.1 = 0 then 1 else 0
  have coordinateBound : coordinate ≤ 1 := by
    simp only [coordinate]
    split <;> omega
  have assignmentNoneBound : assignmentNone ≤ 1 := by
    simp only [assignmentNone]
    split <;> omega
  let finalBudget :=
    100000000000000000000000000 * unit
  have finalRaw :=
    boolOrCost_le_budget values coordinate assignmentNone
      (packedNormalizedAtCoordinateCost period phase motif
        column (x, y) word)
      (packedNormalizedAtAssignmentIsNoneCost period phase motif
        column (x, y) word)
      finalBudget coordinateBound assignmentNoneBound
      (by
        simp only [finalBudget]
        clear * - valuesSpace unitPositive
        omega)
      (by
        simp [values, normalizedValues,
          finalBudget, unitEq]
        clear * - periodBits unitEq
        omega)
      (by
        simp [values, normalizedValues,
          finalBudget, unitEq]
        clear * - periodSuccBits unitEq
        omega)
      (by
        simp only [finalBudget]
        clear * - coordinateGlobal unitPositive
        omega)
      (by
        simp only [finalBudget]
        clear * - assignmentNoneGlobal unitPositive
        omega)
      (by
        simp only [finalBudget]
        clear * - unitPositive
        omega)
  have exact :
      packedNormalizedAtCost period phase motif
          column (x, y) word ≤
        1000 * (finalBudget + 1) := by
    simpa [packedNormalizedAtCost,
      values, nonnegative, equal, coordinate,
      assignmentNone, xSign, xMagnitude,
      columnPhase] using finalRaw
  exact exact.trans
    (packedNormalizedAtFinalBudgetGrowth
      unit unitPositive)

end EvaluatorCodeFits

end PartrecToTM2
end Turing
