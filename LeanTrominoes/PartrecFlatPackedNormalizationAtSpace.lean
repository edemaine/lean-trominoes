import LeanTrominoes.PartrecFlatMotifIndexSpace
import LeanTrominoes.PartrecFlatPackedAssignmentPredicatesSpace
import LeanTrominoes.PartrecFlatPackedNormalizationAt
import LeanTrominoes.PartrecPackedNormalizedAtSpace
import LeanTrominoes.PartrecPairSpace

/-!
# Evaluator-space certificate for one-cell flat packed normalization

This module fits the indexed native coordinate projections and composes them
with the existing coordinate-phase predicate and the flat assignment-absence
predicate.
-/

namespace Turing
namespace PartrecToTM2

open ToPartrec
open LeanTrominoes
open LeanTrominoes.PeriodicStrip

namespace EvaluatorCodeFits

def flatPackedTransitionCellFieldCost
    (field : Fin 2) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool) (index : Nat) : Nat :=
  flatMotifCellFieldAtCost 9 1 field.val
    (Code.flatPackedTransitionScanState periodicStrip current next valid index)

theorem flatPackedTransitionCellField
    (field : Fin 2) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedTransitionCellFieldCode field)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [(PeriodicStripFlatEncoding.cellFields cell)[field.val]?.getD 0]
      (flatPackedTransitionCellFieldCost field periodicStrip current next valid
        processed.length) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let offset := 9 + 2 * values[1]?.getD 0
  have fitted := flatMotifCellFieldAt 9 1 field.val values
  have generic := Code.flatMotifCellFieldAtCode_eval 9 1 field.val values
  have semantic := Code.flatPackedTransitionCellFieldCode_eval field
    periodicStrip current next valid processed cell remaining split
  have outputEq :
      [(values.drop offset)[field.val]?.getD 0] =
        [(PeriodicStripFlatEncoding.cellFields cell)[field.val]?.getD 0] := by
    rw [show Code.flatPackedTransitionCellFieldCode field =
        Code.flatMotifCellFieldAtCode 9 1 field.val by rfl] at semantic
    rw [generic] at semantic
    simpa [offset] using semantic
  rw [← outputEq]
  simpa [Code.flatPackedTransitionCellFieldCode,
    flatPackedTransitionCellFieldCost, values, offset] using fitted

def flatPackedTransitionCellCost
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) (cell : Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let x := Encodable.encode cell.1
  let y := Encodable.encode cell.2
  natPairCost x y +
    prependCost values [x] [y]
      (flatPackedTransitionCellFieldCost (0 : Fin 2) periodicStrip current next
        valid processed.length)
      (flatPackedTransitionCellFieldCost (1 : Fin 2) periodicStrip current next
        valid processed.length)

theorem flatPackedTransitionCell
    (periodicStrip : PeriodicStrip) (current next : PackedWindowState)
    (valid : Bool) (processed : List Cell) (cell : Cell)
    (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits Code.flatPackedTransitionCellCode
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [Encodable.encode cell]
      (flatPackedTransitionCellCost periodicStrip current next valid processed
        cell) := by
  rcases cell with ⟨cellX, cellY⟩
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let x := Encodable.encode cellX
  let y := Encodable.encode cellY
  have arguments := prepend
    (flatPackedTransitionCellField (0 : Fin 2) periodicStrip current next valid
      processed (cellX, cellY) remaining split)
    (flatPackedTransitionCellField (1 : Fin 2) periodicStrip current next valid
      processed (cellX, cellY) remaining split)
  have paired := comp (natPair x y) arguments
  simpa [Code.flatPackedTransitionCellCode, flatPackedTransitionCellCost,
    prependCost, values, x, y, Encodable.encode_prod_val,
    PeriodicStripFlatEncoding.cellFields] using paired

def flatPackedNormalizedCoordinateArgumentsCost
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let cost5 := prependCost values [Encodable.encode cell]
    [current.assignmentWord]
    (flatPackedTransitionCellCost periodicStrip current next valid processed
      cell) (getCost 5 values)
  let costColumn := prependCost values [column.val]
    [Encodable.encode cell, current.assignmentWord]
    (numeralCost column.val values) cost5
  let costZero := prependCost values [0]
    [column.val, Encodable.encode cell, current.assignmentWord]
    (zeroCost values) costColumn
  let costPhase := prependCost values [current.phase]
    [0, column.val, Encodable.encode cell, current.assignmentWord]
    (getCost 6 values) costZero
  prependCost values [periodicStrip.period]
    [current.phase, 0, column.val, Encodable.encode cell,
      current.assignmentWord] (getCost 3 values) costPhase

theorem flatPackedNormalizedCoordinateArguments
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedNormalizedCoordinateArgumentsCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [periodicStrip.period, current.phase, 0, column.val,
        Encodable.encode cell, current.assignmentWord]
      (flatPackedNormalizedCoordinateArgumentsCost column periodicStrip current
        next valid processed cell) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  have cost5 := prepend
    (flatPackedTransitionCell periodicStrip current next valid processed cell
      remaining split) (get 5 values)
  have costColumn := prepend (numeral column.val values) cost5
  have costZero := prepend (zero values) costColumn
  have costPhase := prepend (get 6 values) costZero
  have result := prepend (get 3 values) costPhase
  simpa [Code.flatPackedNormalizedCoordinateArgumentsCode,
    flatPackedNormalizedCoordinateArgumentsCost,
    Code.flatPackedTransitionScanState, prependCost, values] using result

def flatPackedNormalizedCoordinateCost
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  packedNormalizedAtCoordinateCost periodicStrip.period current.phase []
      column.val cell current.assignmentWord +
    flatPackedNormalizedCoordinateArgumentsCost column periodicStrip current
      next valid processed cell

theorem flatPackedNormalizedCoordinate
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    let nonnegative := if IntEncoding.sign cell.1 = 0 then 1 else 0
    let equal := if IntEncoding.magnitude cell.1 =
        Code.packedColumnPhaseNumerator periodicStrip.period current.phase
          column.val % periodicStrip.period then 1 else 0
    EvaluatorCodeFits (Code.flatPackedNormalizedCoordinateCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [if nonnegative = 0 ∨ equal = 0 then 0 else 1]
      (flatPackedNormalizedCoordinateCost column periodicStrip current next
        valid processed cell) := by
  simp only
  simpa [Code.flatPackedNormalizedCoordinateCode,
    flatPackedNormalizedCoordinateCost] using
    comp
      (packedNormalizedAtCoordinate periodicStrip.period current.phase []
        column.val cell current.assignmentWord)
      (flatPackedNormalizedCoordinateArguments column periodicStrip current
        next valid processed cell remaining split)

theorem flatPackedNormalizedCoordinateResult
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedNormalizedCoordinateCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [(decide (cell.1 =
        ((Code.packedColumnPhaseNumerator periodicStrip.period current.phase
          column.val % periodicStrip.period : Nat) : Int))).toNat]
      (flatPackedNormalizedCoordinateCost column periodicStrip current next
        valid processed cell) := by
  let nonnegative := if IntEncoding.sign cell.1 = 0 then 1 else 0
  let equal := if IntEncoding.magnitude cell.1 =
      Code.packedColumnPhaseNumerator periodicStrip.period current.phase
        column.val % periodicStrip.period then 1 else 0
  let coordinateArithmetic :=
    if nonnegative = 0 ∨ equal = 0 then 0 else 1
  let coordinateNative :=
    (decide (cell.1 =
      ((Code.packedColumnPhaseNumerator periodicStrip.period current.phase
        column.val % periodicStrip.period : Nat) : Int))).toNat
  have outputEq : coordinateArithmetic = coordinateNative := by
    simpa [nonnegative, equal, coordinateArithmetic, coordinateNative] using
      Code.packedNormalizedAtCoordinateTag_eq periodicStrip.period
        current.phase column.val cell
  have fitted := flatPackedNormalizedCoordinate column periodicStrip current
    next valid processed cell remaining split
  simpa only [nonnegative, equal, coordinateArithmetic, outputEq,
    coordinateNative] using fitted

def flatPackedNormalizedNoneArgumentsCost
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let coordinates := periodicStrip.motif.flatMap
    PeriodicStripFlatEncoding.cellFields
  let cost5 := prependCost values [current.assignmentWord] coordinates
    (getCost 5 values) (dropCost 9 values)
  let costY := prependCost values [Encodable.encode cell.2]
    (current.assignmentWord :: coordinates)
    (flatPackedTransitionCellFieldCost (1 : Fin 2) periodicStrip current next
      valid processed.length) cost5
  let costX := prependCost values [Encodable.encode cell.1]
    (Encodable.encode cell.2 :: current.assignmentWord :: coordinates)
    (flatPackedTransitionCellFieldCost (0 : Fin 2) periodicStrip current next
      valid processed.length) costY
  let costColumn := prependCost values [column.val]
    (Encodable.encode cell.1 :: Encodable.encode cell.2 ::
      current.assignmentWord :: coordinates)
    (numeralCost column.val values) costX
  prependCost values [periodicStrip.motif.length]
    (column.val :: Encodable.encode cell.1 :: Encodable.encode cell.2 ::
      current.assignmentWord :: coordinates) (getCost 4 values) costColumn

theorem flatPackedNormalizedNoneArguments
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedNormalizedNoneArgumentsCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      ([periodicStrip.motif.length, column.val, Encodable.encode cell.1,
          Encodable.encode cell.2, current.assignmentWord] ++
        periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields)
      (flatPackedNormalizedNoneArgumentsCost column periodicStrip current next
        valid processed cell) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  have cost5 := prepend (get 5 values) (drop 9 values)
  have costY := prepend
    (flatPackedTransitionCellField (1 : Fin 2) periodicStrip current next valid
      processed cell remaining split) cost5
  have costX := prepend
    (flatPackedTransitionCellField (0 : Fin 2) periodicStrip current next valid
      processed cell remaining split) costY
  have costColumn := prepend (numeral column.val values) costX
  have result := prepend (get 4 values) costColumn
  simpa [Code.flatPackedNormalizedNoneArgumentsCode,
    flatPackedNormalizedNoneArgumentsCost,
    Code.flatPackedTransitionScanState,
    PeriodicStripFlatEncoding.cellFields, prependCost, values] using result

def flatPackedNormalizedNoneCost
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  flatPackedAssignmentIsNoneCost periodicStrip.motif column.val cell
      current.assignmentWord +
    flatPackedNormalizedNoneArgumentsCost column periodicStrip current next
      valid processed cell

theorem flatPackedNormalizedNone
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    let digit := (Code.packedAssignmentLookupOutcome periodicStrip.motif
      column.val cell current.assignmentWord).2.1
    EvaluatorCodeFits (Code.flatPackedNormalizedNoneCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [if digit = 0 then 1 else 0]
      (flatPackedNormalizedNoneCost column periodicStrip current next valid
        processed cell) := by
  simp only
  simpa [Code.flatPackedNormalizedNoneCode, flatPackedNormalizedNoneCost] using
    comp
      (flatPackedAssignmentIsNone periodicStrip.motif column.val cell
        current.assignmentWord)
      (flatPackedNormalizedNoneArguments column periodicStrip current next
        valid processed cell remaining split)

def flatPackedNormalizedAtCost
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) : Nat :=
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let coordinate :=
    (decide (cell.1 =
      ((Code.packedColumnPhaseNumerator periodicStrip.period current.phase
        column.val % periodicStrip.period : Nat) : Int))).toNat
  let assignmentNone := if (Code.packedAssignmentLookupOutcome
    periodicStrip.motif column.val cell current.assignmentWord).2.1 = 0
    then 1 else 0
  boolOrCost values coordinate assignmentNone
    (flatPackedNormalizedCoordinateCost column periodicStrip current next valid
      processed cell)
    (flatPackedNormalizedNoneCost column periodicStrip current next valid
      processed cell)

theorem flatPackedNormalizedAtResult
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedNormalizedAtCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [Code.packedNormalizedAtResult periodicStrip.period current.phase
        periodicStrip.motif column.val cell current.assignmentWord]
      (flatPackedNormalizedAtCost column periodicStrip current next valid
        processed cell) := by
  let coordinate :=
    (decide (cell.1 =
      ((Code.packedColumnPhaseNumerator periodicStrip.period current.phase
        column.val % periodicStrip.period : Nat) : Int))).toNat
  let assignmentNone := if (Code.packedAssignmentLookupOutcome
    periodicStrip.motif column.val cell current.assignmentWord).2.1 = 0
    then 1 else 0
  have combined := boolOr
    (flatPackedNormalizedCoordinateResult column periodicStrip current next
      valid processed cell remaining split)
    (flatPackedNormalizedNone column periodicStrip current next valid processed
      cell remaining split)
  simpa [Code.flatPackedNormalizedAtCode, flatPackedNormalizedAtCost,
    Code.packedNormalizedAtResult, coordinate, assignmentNone] using
    combined

theorem flatPackedNormalizedAt
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedNormalizedAtCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [(current.normalizedAtBool periodicStrip column cell).toNat]
      (flatPackedNormalizedAtCost column periodicStrip current next valid
        processed cell) := by
  have fitted := flatPackedNormalizedAtResult column periodicStrip current next
    valid processed cell remaining split
  rw [Code.packedNormalizedAtResult_eq_semantic periodicStrip current column
    cell] at fitted
  exact fitted

end EvaluatorCodeFits
end PartrecToTM2
end Turing
