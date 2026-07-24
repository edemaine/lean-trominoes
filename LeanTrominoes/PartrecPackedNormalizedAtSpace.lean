import LeanTrominoes.PartrecBooleanSpace
import LeanTrominoes.PartrecCellDecodeSpace
import LeanTrominoes.PartrecNatEqualitySpace
import LeanTrominoes.PartrecPackedAssignmentPredicatesSpace
import LeanTrominoes.PartrecPackedColumnPhaseSpace
import LeanTrominoes.PartrecPackedNormalizedAt

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

end EvaluatorCodeFits

end PartrecToTM2
end Turing
