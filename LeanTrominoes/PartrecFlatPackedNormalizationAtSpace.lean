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

/-! ## Polynomial bound -/

/-- A shared native unit for every one-cell transition-scan adapter. -/
def flatPackedNormalizationAtUnit (values : List Nat) : Nat :=
  encodedListSpace values + 10

/-- Common allowance for the arithmetic children and fixed-width adapters of
one normalization check. -/
def flatPackedNormalizationAtCoreBound (values : List Nat) : Nat :=
  100000000000000000000000000000000000000000000000000000000000000000 *
    (flatPackedNormalizationAtUnit values) ^ 2

/-- Public quadratic allowance for one indexed flat normalization check. -/
def flatPackedNormalizedAtSpaceBound (values : List Nat) : Nat :=
  100000000000000000000000000000000000000000000000000000000000000000000000 *
    (flatPackedNormalizationAtUnit values) ^ 2

theorem flatPackedTransitionScanMemberSpace_le
    (field : Nat) (values : List Nat) (member : field ∈ values) :
    encodedListSpace [field] ≤ encodedListSpace values := by
  simpa [encodedListSpace_cons] using
    flatLookupEncodedFieldSpace_le_of_mem field values member

theorem flatPackedTransitionCellXSpace_le
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    encodedListSpace [Encodable.encode cell.1] ≤
      encodedListSpace
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  apply flatPackedTransitionScanMemberSpace_le
  simp [Code.flatPackedTransitionScanState, split,
    PeriodicStripFlatEncoding.cellFields]

theorem flatPackedTransitionCellYSpace_le
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    encodedListSpace [Encodable.encode cell.2] ≤
      encodedListSpace
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  apply flatPackedTransitionScanMemberSpace_le
  simp [Code.flatPackedTransitionScanState, split,
    PeriodicStripFlatEncoding.cellFields]

theorem flatPackedTransitionCoordinatesSpace_le
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool) (index : Nat) :
    encodedListSpace
        (periodicStrip.motif.flatMap
          PeriodicStripFlatEncoding.cellFields) ≤
      encodedListSpace
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          index) := by
  simpa [Code.flatPackedTransitionScanState] using
    flatLookupEncodedListSpace_suffix_le
      [valid.toNat, index, periodicStrip.width, periodicStrip.period,
        periodicStrip.motif.length, current.assignmentWord, current.phase,
        next.assignmentWord, next.phase]
      (periodicStrip.motif.flatMap
        PeriodicStripFlatEncoding.cellFields)

theorem flatPackedNormalizationAssignmentNativeSpace_le
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedAssignmentLookupNativeInputSpace periodicStrip.motif column.val
        cell current.assignmentWord ≤
      7 * flatPackedNormalizationAtUnit
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationAtUnit values
  change flatPackedAssignmentLookupNativeInputSpace periodicStrip.motif
    column.val cell current.assignmentWord ≤ 7 * unit
  have xSpace := flatPackedTransitionCellXSpace_le periodicStrip current next
    valid processed cell remaining split
  have ySpace := flatPackedTransitionCellYSpace_le periodicStrip current next
    valid processed cell remaining split
  have coordinatesSpace := flatPackedTransitionCoordinatesSpace_le
    periodicStrip current next valid processed.length
  change encodedListSpace [Encodable.encode cell.1] ≤
    encodedListSpace values at xSpace
  change encodedListSpace [Encodable.encode cell.2] ≤
    encodedListSpace values at ySpace
  change encodedListSpace
    (periodicStrip.motif.flatMap PeriodicStripFlatEncoding.cellFields) ≤
      encodedListSpace values at coordinatesSpace
  have motifLengthSpace : encodedListSpace [periodicStrip.motif.length] ≤
      encodedListSpace values :=
    flatPackedTransitionScanMemberSpace_le _ values (by
      simp [values, Code.flatPackedTransitionScanState])
  have wordSpace : encodedListSpace [current.assignmentWord] ≤
      encodedListSpace values :=
    flatPackedTransitionScanMemberSpace_le _ values (by
      simp [values, Code.flatPackedTransitionScanState])
  have columnLe : column.val ≤ 4 := by omega
  have columnBits := listCodeEncodeNat_length_mono columnLe
  have fourBits : (Computability.encodeNat 4).length = 3 := by native_decide
  have columnSpace : encodedListSpace [column.val] ≤ unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil]
    rw [fourBits] at columnBits
    simp [unit, flatPackedNormalizationAtUnit]
    omega
  change encodedListSpace
      ([periodicStrip.motif.length, column.val,
          Encodable.encode cell.1, Encodable.encode cell.2,
          current.assignmentWord] ++
        periodicStrip.motif.flatMap
          PeriodicStripFlatEncoding.cellFields) + 1 ≤ 7 * unit
  simp only [List.cons_append, List.nil_append, encodedListSpace_cons]
  simp only [encodedListSpace_cons, encodedListSpace_nil] at xSpace ySpace
  simp only [encodedListSpace_cons, encodedListSpace_nil] at motifLengthSpace wordSpace
  simp only [encodedListSpace_cons, encodedListSpace_nil] at columnSpace
  simp only [unit, flatPackedNormalizationAtUnit] at columnSpace ⊢
  omega

theorem flatPackedNormalizationPackedInputUnit_le
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    packedNormalizedAtInputUnit periodicStrip.period current.phase 0 column.val
        (Encodable.encode cell) current.assignmentWord ≤
      15 * flatPackedNormalizationAtUnit
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationAtUnit values
  change packedNormalizedAtInputUnit periodicStrip.period current.phase 0
    column.val (Encodable.encode cell) current.assignmentWord ≤ 15 * unit
  have xSpace := flatPackedTransitionCellXSpace_le periodicStrip current next
    valid processed cell remaining split
  have ySpace := flatPackedTransitionCellYSpace_le periodicStrip current next
    valid processed cell remaining split
  change encodedListSpace [Encodable.encode cell.1] ≤
    encodedListSpace values at xSpace
  change encodedListSpace [Encodable.encode cell.2] ≤
    encodedListSpace values at ySpace
  have periodSpace : encodedListSpace [periodicStrip.period] ≤
      encodedListSpace values :=
    flatPackedTransitionScanMemberSpace_le _ values (by
      simp [values, Code.flatPackedTransitionScanState])
  have phaseSpace : encodedListSpace [current.phase] ≤
      encodedListSpace values :=
    flatPackedTransitionScanMemberSpace_le _ values (by
      simp [values, Code.flatPackedTransitionScanState])
  have wordSpace : encodedListSpace [current.assignmentWord] ≤
      encodedListSpace values :=
    flatPackedTransitionScanMemberSpace_le _ values (by
      simp [values, Code.flatPackedTransitionScanState])
  change encodedListSpace [periodicStrip.period] ≤
    encodedListSpace values at periodSpace
  change encodedListSpace [current.phase] ≤
    encodedListSpace values at phaseSpace
  change encodedListSpace [current.assignmentWord] ≤
    encodedListSpace values at wordSpace
  have columnLe : column.val ≤ 4 := by omega
  have columnBits := listCodeEncodeNat_length_mono columnLe
  have pairBits := encodeNat_pair_length_le
    (Encodable.encode cell.1) (Encodable.encode cell.2)
  have fourBits : (Computability.encodeNat 4).length = 3 := by native_decide
  have zeroBits : (Computability.encodeNat 0).length = 0 := rfl
  have cellSpace : encodedListSpace [Encodable.encode cell] ≤ 7 * unit := by
    rcases cell with ⟨x, y⟩
    simp only [Encodable.encode_prod_val] at pairBits ⊢
    simp only [encodedListSpace_cons, encodedListSpace_nil] at xSpace ySpace ⊢
    simp [unit, flatPackedNormalizationAtUnit] at xSpace ySpace ⊢
    omega
  simp only [packedNormalizedAtInputUnit, encodedListSpace_cons,
    encodedListSpace_nil]
  rw [fourBits] at columnBits
  rw [zeroBits]
  simp only [encodedListSpace_cons, encodedListSpace_nil] at periodSpace phaseSpace wordSpace cellSpace
  simp only [unit, flatPackedNormalizationAtUnit] at cellSpace ⊢
  omega

theorem flatPackedTransitionCellFieldCost_le_core
    (field : Fin 2) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool) (index : Nat) :
    flatPackedTransitionCellFieldCost field periodicStrip current next valid
        index ≤
      flatPackedNormalizationAtCoreBound
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          index) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid index
  calc
    flatPackedTransitionCellFieldCost field periodicStrip current next valid
        index ≤ flatMotifIndexSpaceBound values := by
      simpa [flatPackedTransitionCellFieldCost, values] using
        flatMotifCellFieldAtCost_le_quadratic field values
    _ ≤ flatPackedNormalizationAtCoreBound values := by
      simp [flatMotifIndexSpaceBound, flatMotifIndexUnit,
        flatPackedNormalizationAtCoreBound, flatPackedNormalizationAtUnit]

theorem flatPackedTransitionPairCost_le_core
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    natPairCost (Encodable.encode cell.1) (Encodable.encode cell.2) ≤
      flatPackedNormalizationAtCoreBound
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationAtUnit values
  have xSpace := flatPackedTransitionCellXSpace_le periodicStrip current next
    valid processed cell remaining split
  have ySpace := flatPackedTransitionCellYSpace_le periodicStrip current next
    valid processed cell remaining split
  change encodedListSpace [Encodable.encode cell.1] ≤
    encodedListSpace values at xSpace
  change encodedListSpace [Encodable.encode cell.2] ≤
    encodedListSpace values at ySpace
  have pairUnit := natPairUnit_le_linear
    (Encodable.encode cell.1) (Encodable.encode cell.2)
  have pairUnitBound : natPairUnit (Encodable.encode cell.1)
      (Encodable.encode cell.2) ≤ 300 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at xSpace ySpace
    dsimp [unit, flatPackedNormalizationAtUnit]
    omega
  have pairCost := natPairCost_le_linear
    (Encodable.encode cell.1) (Encodable.encode cell.2)
  calc
    natPairCost (Encodable.encode cell.1) (Encodable.encode cell.2) ≤
        10000000000000000000000000000000000000000 *
          natPairUnit (Encodable.encode cell.1)
            (Encodable.encode cell.2) := pairCost
    _ ≤ 10000000000000000000000000000000000000000 *
          (300 * unit) := Nat.mul_le_mul_left _ pairUnitBound
    _ ≤ flatPackedNormalizationAtCoreBound values := by
      simp [flatPackedNormalizationAtCoreBound,
        flatPackedNormalizationAtUnit, unit]
      nlinarith

theorem flatPackedNormalizationGetCost_le_core
    (index : Nat) (values : List Nat) (fixed : index ≤ 9) :
    getCost index values ≤ flatPackedNormalizationAtCoreBound values := by
  have raw := listCodeGetCost_le_linear index values
  have unitPositive : 10 ≤ flatPackedNormalizationAtUnit values := by
    simp [flatPackedNormalizationAtUnit]
  calc
    getCost index values ≤
        (10000 * (index + 1)) * (encodedListSpace values + 1) := raw
    _ ≤ 100000 * flatPackedNormalizationAtUnit values := by
      simp [flatPackedNormalizationAtUnit]
      nlinarith
    _ ≤ flatPackedNormalizationAtCoreBound values := by
      simp [flatPackedNormalizationAtCoreBound]
      nlinarith

theorem flatPackedNormalizationDropCost_le_core
    (values : List Nat) :
    dropCost 9 values ≤ flatPackedNormalizationAtCoreBound values := by
  have whole := flatPackedNormalizationGetCost_le_core 9 values (by omega)
  have part : dropCost 9 values ≤ getCost 9 values := by
    simp only [getCost]
    omega
  exact part.trans whole

theorem flatPackedNormalizationZeroCost_le_core (values : List Nat) :
    zeroCost values ≤ flatPackedNormalizationAtCoreBound values := by
  have raw := listCodeZeroCost_le_linear values
  calc
    zeroCost values ≤ 10000 * (encodedListSpace values + 1) := raw
    _ ≤ flatPackedNormalizationAtCoreBound values := by
      simp [flatPackedNormalizationAtCoreBound,
        flatPackedNormalizationAtUnit]
      nlinarith

theorem flatPackedNormalizationNumeralCost_le_core
    (column : WindowColumn) (values : List Nat) :
    numeralCost column.val values ≤
      flatPackedNormalizationAtCoreBound values := by
  have zero := listCodeZeroCost_le_linear values
  have addSmall : addConstCost column.val [0] ≤ 1000000 := by
    fin_cases column <;> native_decide
  simp only [numeralCost]
  simp [flatPackedNormalizationAtCoreBound,
    flatPackedNormalizationAtUnit] at zero ⊢
  nlinarith

theorem flatPackedTransitionCellCost_le_core
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedTransitionCellCost periodicStrip current next valid processed
        cell ≤
      4 * flatPackedNormalizationAtCoreBound
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationAtUnit values
  let core := flatPackedNormalizationAtCoreBound values
  change flatPackedTransitionCellCost periodicStrip current next valid
    processed cell ≤ 4 * core
  have xSpace := flatPackedTransitionCellXSpace_le periodicStrip current next
    valid processed cell remaining split
  have ySpace := flatPackedTransitionCellYSpace_le periodicStrip current next
    valid processed cell remaining split
  change encodedListSpace [Encodable.encode cell.1] ≤
    encodedListSpace values at xSpace
  change encodedListSpace [Encodable.encode cell.2] ≤
    encodedListSpace values at ySpace
  have valuesSpace : encodedListSpace values ≤ 3 * unit := by
    simp [unit, flatPackedNormalizationAtUnit]
    omega
  have xLocal : encodedListSpace [Encodable.encode cell.1] ≤ 3 * unit :=
    xSpace.trans (by simp [unit, flatPackedNormalizationAtUnit]; omega)
  have outputSpace : encodedListSpace
      [Encodable.encode cell.1, Encodable.encode cell.2] ≤ 3 * unit := by
    simp only [encodedListSpace_cons, encodedListSpace_nil] at xSpace ySpace ⊢
    simp [unit, flatPackedNormalizationAtUnit]
    omega
  have xCost := flatPackedTransitionCellFieldCost_le_core (0 : Fin 2)
    periodicStrip current next valid processed.length
  have yCost := flatPackedTransitionCellFieldCost_le_core (1 : Fin 2)
    periodicStrip current next valid processed.length
  change flatPackedTransitionCellFieldCost (0 : Fin 2) periodicStrip current
    next valid processed.length ≤ core at xCost
  change flatPackedTransitionCellFieldCost (1 : Fin 2) periodicStrip current
    next valid processed.length ≤ core at yCost
  have argumentsRaw := listCodePrependCost_le_of values
    [Encodable.encode cell.1] [Encodable.encode cell.2]
    (flatPackedTransitionCellFieldCost (0 : Fin 2) periodicStrip current next
      valid processed.length)
    (flatPackedTransitionCellFieldCost (1 : Fin 2) periodicStrip current next
      valid processed.length)
    (3 * unit) valuesSpace xLocal (by
      simpa only [List.headI_cons] using outputSpace)
  have overhead : 9 * unit + 2 ≤ core := by
    simp [core, flatPackedNormalizationAtCoreBound,
      unit, flatPackedNormalizationAtUnit]
    nlinarith
  have argumentsCost : prependCost values [Encodable.encode cell.1]
      [Encodable.encode cell.2]
      (flatPackedTransitionCellFieldCost (0 : Fin 2) periodicStrip current next
        valid processed.length)
      (flatPackedTransitionCellFieldCost (1 : Fin 2) periodicStrip current next
        valid processed.length) ≤ 3 * core := by
    change _ ≤ 3 * flatPackedNormalizationAtCoreBound values
    omega
  have pairCost := flatPackedTransitionPairCost_le_core periodicStrip current
    next valid processed cell remaining split
  change natPairCost (Encodable.encode cell.1) (Encodable.encode cell.2) +
      prependCost values [Encodable.encode cell.1] [Encodable.encode cell.2]
        (flatPackedTransitionCellFieldCost (0 : Fin 2) periodicStrip current
          next valid processed.length)
        (flatPackedTransitionCellFieldCost (1 : Fin 2) periodicStrip current
          next valid processed.length) ≤ 4 * core
  change natPairCost (Encodable.encode cell.1) (Encodable.encode cell.2) ≤
    core at pairCost
  omega

theorem flatPackedNormalizedCoordinateInnerCost_le_core
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    packedNormalizedAtCoordinateCost periodicStrip.period current.phase []
        column.val cell current.assignmentWord ≤
      flatPackedNormalizationAtCoreBound
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationAtUnit values
  have coordinateLocal := packedNormalizedAtCoordinateCost_le_linear
    periodicStrip.period current.phase [] column.val cell
      current.assignmentWord
  have packedLinear := packedNormalizedAtSpaceBound_le_linear
    periodicStrip.period current.phase 0 column.val (Encodable.encode cell)
      current.assignmentWord
  have input := flatPackedNormalizationPackedInputUnit_le column periodicStrip
    current next valid processed cell remaining split
  calc
    packedNormalizedAtCoordinateCost periodicStrip.period current.phase []
        column.val cell current.assignmentWord ≤
      packedNormalizedAtSpaceBound periodicStrip.period current.phase 0
        column.val (Encodable.encode cell) current.assignmentWord := by
          simpa using coordinateLocal
    _ ≤ (1000000000000000000000000000000 * 100) *
        packedNormalizedAtInputUnit periodicStrip.period current.phase 0
          column.val (Encodable.encode cell) current.assignmentWord :=
      packedLinear
    _ ≤ (1000000000000000000000000000000 * 100) *
        (15 * unit) := Nat.mul_le_mul_left _ (by simpa [unit] using input)
    _ ≤ flatPackedNormalizationAtCoreBound values := by
      simp [flatPackedNormalizationAtCoreBound,
        flatPackedNormalizationAtUnit, unit]
      nlinarith

theorem flatPackedNormalizedNoneInnerCost_le_core
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedAssignmentIsNoneCost periodicStrip.motif column.val cell
        current.assignmentWord ≤
      flatPackedNormalizationAtCoreBound
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationAtUnit values
  let native := flatPackedAssignmentLookupNativeInputSpace periodicStrip.motif
    column.val cell current.assignmentWord
  have exact := flatPackedAssignmentIsNoneCost_le_bound periodicStrip.motif
    column.val cell current.assignmentWord
  have polynomial := flatPackedAssignmentPredicateSpaceBound_le_native_quadratic
    periodicStrip.motif column.val cell current.assignmentWord
  have nativeBound := flatPackedNormalizationAssignmentNativeSpace_le column
    periodicStrip current next valid processed cell remaining split
  have nativeLocal : native ≤ 7 * unit := by
    simpa [native, unit] using nativeBound
  calc
    flatPackedAssignmentIsNoneCost periodicStrip.motif column.val cell
        current.assignmentWord ≤
      flatPackedAssignmentPredicateSpaceBound periodicStrip.motif column.val
        cell current.assignmentWord := exact
    _ ≤ 10000000000000000000000000000000000000000000000000000000000 *
        native ^ 2 := by simpa [native] using polynomial
    _ ≤ 10000000000000000000000000000000000000000000000000000000000 *
        (7 * unit) ^ 2 := by gcongr
    _ ≤ flatPackedNormalizationAtCoreBound values := by
      simp [flatPackedNormalizationAtCoreBound,
        flatPackedNormalizationAtUnit, unit]
      nlinarith

theorem flatPackedNormalizedCoordinateArgumentsCost_le_core
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedNormalizedCoordinateArgumentsCost column periodicStrip current
        next valid processed cell ≤
      15 * flatPackedNormalizationAtCoreBound
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationAtUnit values
  let core := flatPackedNormalizationAtCoreBound values
  change flatPackedNormalizedCoordinateArgumentsCost column periodicStrip
    current next valid processed cell ≤ 15 * core
  let full := [periodicStrip.period, current.phase, 0, column.val,
    Encodable.encode cell, current.assignmentWord]
  have input := flatPackedNormalizationPackedInputUnit_le column periodicStrip
    current next valid processed cell remaining split
  have inputLocal : packedNormalizedAtInputUnit periodicStrip.period
      current.phase 0 column.val (Encodable.encode cell)
      current.assignmentWord ≤ 15 * unit := by
    simpa [unit] using input
  have fullSpace : encodedListSpace full ≤ 15 * unit := by
    have inputList : encodedListSpace
        [periodicStrip.period, current.phase, 0, column.val,
          Encodable.encode cell, current.assignmentWord] + 1 ≤
        15 * unit := by
      simpa [packedNormalizedAtInputUnit] using inputLocal
    dsimp [full]
    omega
  have valuesSpace : encodedListSpace values ≤ 15 * unit := by
    simp [unit, flatPackedNormalizationAtUnit]
    omega
  have suffix1 : encodedListSpace [current.assignmentWord] ≤ 15 * unit :=
    (flatLookupEncodedListSpace_suffix_le
      [periodicStrip.period, current.phase, 0, column.val,
        Encodable.encode cell] [current.assignmentWord]).trans (by
          simpa [full] using fullSpace)
  have suffix2 : encodedListSpace
      [Encodable.encode cell, current.assignmentWord] ≤ 15 * unit :=
    (flatLookupEncodedListSpace_suffix_le
      [periodicStrip.period, current.phase, 0, column.val]
      [Encodable.encode cell, current.assignmentWord]).trans (by
        simpa [full] using fullSpace)
  have suffix3 : encodedListSpace
      [column.val, Encodable.encode cell, current.assignmentWord] ≤
      15 * unit :=
    (flatLookupEncodedListSpace_suffix_le
      [periodicStrip.period, current.phase, 0]
      [column.val, Encodable.encode cell, current.assignmentWord]).trans (by
        simpa [full] using fullSpace)
  have suffix4 : encodedListSpace
      [0, column.val, Encodable.encode cell, current.assignmentWord] ≤
      15 * unit :=
    (flatLookupEncodedListSpace_suffix_le
      [periodicStrip.period, current.phase]
      [0, column.val, Encodable.encode cell, current.assignmentWord]).trans (by
        simpa [full] using fullSpace)
  have suffix5 : encodedListSpace
      [current.phase, 0, column.val, Encodable.encode cell,
        current.assignmentWord] ≤ 15 * unit :=
    (flatLookupEncodedListSpace_suffix_le [periodicStrip.period]
      [current.phase, 0, column.val, Encodable.encode cell,
        current.assignmentWord]).trans (by simpa [full] using fullSpace)
  have cellSingleton : encodedListSpace [Encodable.encode cell] ≤
      15 * unit :=
    (flatLookupEncodedListSpace_prefix_le [Encodable.encode cell]
      [current.assignmentWord]).trans suffix2
  have columnSingleton : encodedListSpace [column.val] ≤ 15 * unit :=
    (flatLookupEncodedListSpace_prefix_le [column.val]
      [Encodable.encode cell, current.assignmentWord]).trans suffix3
  have zeroSingleton : encodedListSpace [0] ≤ 15 * unit :=
    (flatLookupEncodedListSpace_prefix_le [0]
      [column.val, Encodable.encode cell, current.assignmentWord]).trans suffix4
  have phaseSingleton : encodedListSpace [current.phase] ≤ 15 * unit :=
    (flatLookupEncodedListSpace_prefix_le [current.phase]
      [0, column.val, Encodable.encode cell,
        current.assignmentWord]).trans suffix5
  have periodSingleton : encodedListSpace [periodicStrip.period] ≤
      15 * unit :=
    (flatLookupEncodedListSpace_prefix_le [periodicStrip.period]
      [current.phase, 0, column.val, Encodable.encode cell,
        current.assignmentWord]).trans (by simpa [full] using fullSpace)
  have overhead : 45 * unit + 2 ≤ core := by
    simp [core, flatPackedNormalizationAtCoreBound,
      unit, flatPackedNormalizationAtUnit]
    nlinarith
  have cellCost := flatPackedTransitionCellCost_le_core periodicStrip current
    next valid processed cell remaining split
  have get5 := flatPackedNormalizationGetCost_le_core 5 values (by omega)
  have get6 := flatPackedNormalizationGetCost_le_core 6 values (by omega)
  have get3 := flatPackedNormalizationGetCost_le_core 3 values (by omega)
  have numeral := flatPackedNormalizationNumeralCost_le_core column values
  have zero := flatPackedNormalizationZeroCost_le_core values
  change flatPackedTransitionCellCost periodicStrip current next valid processed
    cell ≤ 4 * core at cellCost
  change getCost 5 values ≤ core at get5
  change getCost 6 values ≤ core at get6
  change getCost 3 values ≤ core at get3
  change numeralCost column.val values ≤ core at numeral
  change zeroCost values ≤ core at zero
  let cost5 := prependCost values [Encodable.encode cell]
    [current.assignmentWord]
    (flatPackedTransitionCellCost periodicStrip current next valid processed
      cell) (getCost 5 values)
  have cost5Raw := listCodePrependCost_le_of values [Encodable.encode cell]
    [current.assignmentWord]
    (flatPackedTransitionCellCost periodicStrip current next valid processed
      cell) (getCost 5 values) (15 * unit) valuesSpace cellSingleton suffix2
  have cost5Bound : cost5 ≤ 6 * core := by
    simp only [cost5]
    omega
  let costColumn := prependCost values [column.val]
    [Encodable.encode cell, current.assignmentWord]
    (numeralCost column.val values) cost5
  have costColumnRaw := listCodePrependCost_le_of values [column.val]
    [Encodable.encode cell, current.assignmentWord]
    (numeralCost column.val values) cost5 (15 * unit) valuesSpace
    columnSingleton suffix3
  have costColumnBound : costColumn ≤ 8 * core := by
    simp only [costColumn]
    omega
  let costZero := prependCost values [0]
    [column.val, Encodable.encode cell, current.assignmentWord]
    (zeroCost values) costColumn
  have costZeroRaw := listCodePrependCost_le_of values [0]
    [column.val, Encodable.encode cell, current.assignmentWord]
    (zeroCost values) costColumn (15 * unit) valuesSpace zeroSingleton suffix4
  have costZeroBound : costZero ≤ 10 * core := by
    simp only [costZero]
    omega
  let costPhase := prependCost values [current.phase]
    [0, column.val, Encodable.encode cell, current.assignmentWord]
    (getCost 6 values) costZero
  have costPhaseRaw := listCodePrependCost_le_of values [current.phase]
    [0, column.val, Encodable.encode cell, current.assignmentWord]
    (getCost 6 values) costZero (15 * unit) valuesSpace phaseSingleton suffix5
  have costPhaseBound : costPhase ≤ 12 * core := by
    simp only [costPhase]
    omega
  have finalRaw := listCodePrependCost_le_of values [periodicStrip.period]
    [current.phase, 0, column.val, Encodable.encode cell,
      current.assignmentWord]
    (getCost 3 values) costPhase (15 * unit) valuesSpace periodSingleton
    (by simpa only [List.headI_cons] using fullSpace)
  have finalBound : prependCost values [periodicStrip.period]
      [current.phase, 0, column.val, Encodable.encode cell,
        current.assignmentWord]
      (getCost 3 values) costPhase ≤ 14 * core := by omega
  have widened : prependCost values [periodicStrip.period]
      [current.phase, 0, column.val, Encodable.encode cell,
        current.assignmentWord]
      (getCost 3 values) costPhase ≤ 15 * core :=
    finalBound.trans (by omega)
  simpa only [flatPackedNormalizedCoordinateArgumentsCost, cost5,
    costColumn, costZero, costPhase] using widened

theorem flatPackedNormalizedNoneArgumentsCost_le_core
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedNormalizedNoneArgumentsCost column periodicStrip current next
        valid processed cell ≤
      12 * flatPackedNormalizationAtCoreBound
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let unit := flatPackedNormalizationAtUnit values
  let core := flatPackedNormalizationAtCoreBound values
  let coordinates := periodicStrip.motif.flatMap
    PeriodicStripFlatEncoding.cellFields
  let full := [periodicStrip.motif.length, column.val,
      Encodable.encode cell.1, Encodable.encode cell.2,
      current.assignmentWord] ++ coordinates
  change flatPackedNormalizedNoneArgumentsCost column periodicStrip current
    next valid processed cell ≤ 12 * core
  have native := flatPackedNormalizationAssignmentNativeSpace_le column
    periodicStrip current next valid processed cell remaining split
  have nativeLocal : flatPackedAssignmentLookupNativeInputSpace
      periodicStrip.motif column.val cell current.assignmentWord ≤
      7 * unit := by simpa [unit] using native
  have fullSpace : encodedListSpace full ≤ 15 * unit := by
    have inputList : encodedListSpace
        ([periodicStrip.motif.length, column.val,
            Encodable.encode cell.1, Encodable.encode cell.2,
            current.assignmentWord] ++ coordinates) + 1 ≤ 7 * unit := by
      simpa [flatPackedAssignmentLookupNativeInputSpace,
        coordinates] using nativeLocal
    have inputFull : encodedListSpace full + 1 ≤ 7 * unit := by
      simpa [full] using inputList
    omega
  have valuesSpace : encodedListSpace values ≤ 15 * unit := by
    simp [unit, flatPackedNormalizationAtUnit]
    omega
  have coordinatesSpace : encodedListSpace coordinates ≤ 15 * unit :=
    (flatLookupEncodedListSpace_suffix_le
      [periodicStrip.motif.length, column.val,
        Encodable.encode cell.1, Encodable.encode cell.2,
        current.assignmentWord] coordinates).trans (by
          simpa [full] using fullSpace)
  have suffix1 : encodedListSpace
      (current.assignmentWord :: coordinates) ≤ 15 * unit :=
    (flatLookupEncodedListSpace_suffix_le
      [periodicStrip.motif.length, column.val,
        Encodable.encode cell.1, Encodable.encode cell.2]
      (current.assignmentWord :: coordinates)).trans (by
        simpa [full] using fullSpace)
  have suffix2 : encodedListSpace
      (Encodable.encode cell.2 :: current.assignmentWord :: coordinates) ≤
      15 * unit :=
    (flatLookupEncodedListSpace_suffix_le
      [periodicStrip.motif.length, column.val, Encodable.encode cell.1]
      (Encodable.encode cell.2 :: current.assignmentWord ::
        coordinates)).trans (by simpa [full] using fullSpace)
  have suffix3 : encodedListSpace
      (Encodable.encode cell.1 :: Encodable.encode cell.2 ::
        current.assignmentWord :: coordinates) ≤ 15 * unit :=
    (flatLookupEncodedListSpace_suffix_le
      [periodicStrip.motif.length, column.val]
      (Encodable.encode cell.1 :: Encodable.encode cell.2 ::
        current.assignmentWord :: coordinates)).trans (by
          simpa [full] using fullSpace)
  have suffix4 : encodedListSpace
      (column.val :: Encodable.encode cell.1 :: Encodable.encode cell.2 ::
        current.assignmentWord :: coordinates) ≤ 15 * unit :=
    (flatLookupEncodedListSpace_suffix_le [periodicStrip.motif.length]
      (column.val :: Encodable.encode cell.1 :: Encodable.encode cell.2 ::
        current.assignmentWord :: coordinates)).trans (by
          simpa [full] using fullSpace)
  have wordSingleton : encodedListSpace [current.assignmentWord] ≤
      15 * unit :=
    (flatLookupEncodedListSpace_prefix_le [current.assignmentWord]
      coordinates).trans suffix1
  have ySingleton : encodedListSpace [Encodable.encode cell.2] ≤
      15 * unit :=
    (flatLookupEncodedListSpace_prefix_le [Encodable.encode cell.2]
      (current.assignmentWord :: coordinates)).trans suffix2
  have xSingleton : encodedListSpace [Encodable.encode cell.1] ≤
      15 * unit :=
    (flatLookupEncodedListSpace_prefix_le [Encodable.encode cell.1]
      (Encodable.encode cell.2 :: current.assignmentWord ::
        coordinates)).trans suffix3
  have columnSingleton : encodedListSpace [column.val] ≤ 15 * unit :=
    (flatLookupEncodedListSpace_prefix_le [column.val]
      (Encodable.encode cell.1 :: Encodable.encode cell.2 ::
        current.assignmentWord :: coordinates)).trans suffix4
  have lengthSingleton : encodedListSpace [periodicStrip.motif.length] ≤
      15 * unit :=
    (flatLookupEncodedListSpace_prefix_le [periodicStrip.motif.length]
      (column.val :: Encodable.encode cell.1 :: Encodable.encode cell.2 ::
        current.assignmentWord :: coordinates)).trans (by
          simpa [full] using fullSpace)
  have overhead : 45 * unit + 2 ≤ core := by
    simp [core, flatPackedNormalizationAtCoreBound,
      unit, flatPackedNormalizationAtUnit]
    nlinarith
  have get5 := flatPackedNormalizationGetCost_le_core 5 values (by omega)
  have get4 := flatPackedNormalizationGetCost_le_core 4 values (by omega)
  have drop9 := flatPackedNormalizationDropCost_le_core values
  have xCost := flatPackedTransitionCellFieldCost_le_core (0 : Fin 2)
    periodicStrip current next valid processed.length
  have yCost := flatPackedTransitionCellFieldCost_le_core (1 : Fin 2)
    periodicStrip current next valid processed.length
  have numeral := flatPackedNormalizationNumeralCost_le_core column values
  change getCost 5 values ≤ core at get5
  change getCost 4 values ≤ core at get4
  change dropCost 9 values ≤ core at drop9
  change flatPackedTransitionCellFieldCost (0 : Fin 2) periodicStrip current
    next valid processed.length ≤ core at xCost
  change flatPackedTransitionCellFieldCost (1 : Fin 2) periodicStrip current
    next valid processed.length ≤ core at yCost
  change numeralCost column.val values ≤ core at numeral
  let cost5 := prependCost values [current.assignmentWord] coordinates
    (getCost 5 values) (dropCost 9 values)
  have cost5Raw := listCodePrependCost_le_of values [current.assignmentWord]
    coordinates (getCost 5 values) (dropCost 9 values) (15 * unit)
    valuesSpace wordSingleton suffix1
  have cost5Bound : cost5 ≤ 3 * core := by
    simp only [cost5]
    omega
  let costY := prependCost values [Encodable.encode cell.2]
    (current.assignmentWord :: coordinates)
    (flatPackedTransitionCellFieldCost (1 : Fin 2) periodicStrip current next
      valid processed.length) cost5
  have costYRaw := listCodePrependCost_le_of values [Encodable.encode cell.2]
    (current.assignmentWord :: coordinates)
    (flatPackedTransitionCellFieldCost (1 : Fin 2) periodicStrip current next
      valid processed.length) cost5 (15 * unit) valuesSpace ySingleton suffix2
  have costYBound : costY ≤ 5 * core := by
    simp only [costY]
    omega
  let costX := prependCost values [Encodable.encode cell.1]
    (Encodable.encode cell.2 :: current.assignmentWord :: coordinates)
    (flatPackedTransitionCellFieldCost (0 : Fin 2) periodicStrip current next
      valid processed.length) costY
  have costXRaw := listCodePrependCost_le_of values [Encodable.encode cell.1]
    (Encodable.encode cell.2 :: current.assignmentWord :: coordinates)
    (flatPackedTransitionCellFieldCost (0 : Fin 2) periodicStrip current next
      valid processed.length) costY (15 * unit) valuesSpace xSingleton suffix3
  have costXBound : costX ≤ 7 * core := by
    simp only [costX]
    omega
  let costColumn := prependCost values [column.val]
    (Encodable.encode cell.1 :: Encodable.encode cell.2 ::
      current.assignmentWord :: coordinates)
    (numeralCost column.val values) costX
  have costColumnRaw := listCodePrependCost_le_of values [column.val]
    (Encodable.encode cell.1 :: Encodable.encode cell.2 ::
      current.assignmentWord :: coordinates)
    (numeralCost column.val values) costX (15 * unit) valuesSpace
    columnSingleton suffix4
  have costColumnBound : costColumn ≤ 9 * core := by
    simp only [costColumn]
    omega
  have finalRaw := listCodePrependCost_le_of values
    [periodicStrip.motif.length]
    (column.val :: Encodable.encode cell.1 :: Encodable.encode cell.2 ::
      current.assignmentWord :: coordinates)
    (getCost 4 values) costColumn (15 * unit) valuesSpace lengthSingleton
    (by simpa [full] using fullSpace)
  have finalBound : prependCost values [periodicStrip.motif.length]
      (column.val :: Encodable.encode cell.1 :: Encodable.encode cell.2 ::
        current.assignmentWord :: coordinates)
      (getCost 4 values) costColumn ≤ 11 * core := by omega
  have widened : prependCost values [periodicStrip.motif.length]
      (column.val :: Encodable.encode cell.1 :: Encodable.encode cell.2 ::
        current.assignmentWord :: coordinates)
      (getCost 4 values) costColumn ≤ 12 * core :=
    finalBound.trans (by omega)
  simpa only [flatPackedNormalizedNoneArgumentsCost, coordinates, cost5,
    costY, costX, costColumn] using widened

set_option maxHeartbeats 1000000 in
theorem flatPackedNormalizedAtCost_le_bound
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedNormalizedAtCost column periodicStrip current next valid
        processed cell ≤
      flatPackedNormalizedAtSpaceBound
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length) := by
  let values := Code.flatPackedTransitionScanState periodicStrip current next
    valid processed.length
  let core := flatPackedNormalizationAtCoreBound values
  let budget := 20 * core
  let coordinate :=
    (decide (cell.1 =
      ((Code.packedColumnPhaseNumerator periodicStrip.period current.phase
        column.val % periodicStrip.period : Nat) : Int))).toNat
  let assignmentNone := if (Code.packedAssignmentLookupOutcome
    periodicStrip.motif column.val cell current.assignmentWord).2.1 = 0
    then 1 else 0
  have coordinateInner := flatPackedNormalizedCoordinateInnerCost_le_core
    column periodicStrip current next valid processed cell remaining split
  have coordinateArguments :=
    flatPackedNormalizedCoordinateArgumentsCost_le_core column periodicStrip
      current next valid processed cell remaining split
  have noneInner := flatPackedNormalizedNoneInnerCost_le_core column
    periodicStrip current next valid processed cell remaining split
  have noneArguments := flatPackedNormalizedNoneArgumentsCost_le_core column
    periodicStrip current next valid processed cell remaining split
  change packedNormalizedAtCoordinateCost periodicStrip.period current.phase []
    column.val cell current.assignmentWord ≤ core at coordinateInner
  change flatPackedNormalizedCoordinateArgumentsCost column periodicStrip
    current next valid processed cell ≤ 15 * core at coordinateArguments
  change flatPackedAssignmentIsNoneCost periodicStrip.motif column.val cell
    current.assignmentWord ≤ core at noneInner
  change flatPackedNormalizedNoneArgumentsCost column periodicStrip current
    next valid processed cell ≤ 12 * core at noneArguments
  have coordinateCost : flatPackedNormalizedCoordinateCost column periodicStrip
      current next valid processed cell ≤ 16 * core := by
    simp only [flatPackedNormalizedCoordinateCost]
    omega
  have noneCost : flatPackedNormalizedNoneCost column periodicStrip current next
      valid processed cell ≤ 13 * core := by
    simp only [flatPackedNormalizedNoneCost]
    omega
  have coordinateBound : coordinate ≤ 1 := by
    exact Bool.toNat_le _
  have assignmentNoneBound : assignmentNone ≤ 1 := by
    simp only [assignmentNone]
    split <;> omega
  have valuesBound : encodedListSpace values ≤ budget := by
    simp [budget, core, flatPackedNormalizationAtCoreBound,
      flatPackedNormalizationAtUnit]
    nlinarith
  have valuesPlusBound : encodedListSpace values + 1 ≤ budget := by
    simp [budget, core, flatPackedNormalizationAtCoreBound,
      flatPackedNormalizationAtUnit]
    nlinarith
  have headSpace := listCodeEncodedListSpace_singleton_headI_le values
  have headBound : (Computability.encodeNat values.headI).length ≤ budget := by
    have localBound : (Computability.encodeNat values.headI).length ≤
        encodedListSpace values := by
      simpa [encodedListSpace_cons] using headSpace
    exact localBound.trans valuesBound
  have headSuccessor := listCodeEncodeNat_succ_length_le values.headI
  have headSuccessorBound :
      (Computability.encodeNat (values.headI + 1)).length ≤ budget := by
    have localBound :
        (Computability.encodeNat (values.headI + 1)).length ≤
          (Computability.encodeNat values.headI).length + 1 := by
      simpa [Nat.succ_eq_add_one] using headSuccessor
    have headPlusSpace :
        (Computability.encodeNat values.headI).length + 1 ≤
          encodedListSpace values + 1 := by
      simpa [encodedListSpace_cons] using headSpace
    exact localBound.trans (headPlusSpace.trans valuesPlusBound)
  have positive : 1 ≤ budget := by
    simp [budget, core, flatPackedNormalizationAtCoreBound,
      flatPackedNormalizationAtUnit]
    nlinarith
  have wrapped := boolOrCost_le_budget values coordinate assignmentNone
    (flatPackedNormalizedCoordinateCost column periodicStrip current next valid
      processed cell)
    (flatPackedNormalizedNoneCost column periodicStrip current next valid
      processed cell)
    budget coordinateBound assignmentNoneBound valuesBound headBound
      headSuccessorBound (by simp [budget]; omega) (by simp [budget]; omega)
      positive
  have exact : flatPackedNormalizedAtCost column periodicStrip current next
      valid processed cell ≤ 1000 * (budget + 1) := by
    simpa [flatPackedNormalizedAtCost, values, coordinate,
      assignmentNone] using wrapped
  calc
    flatPackedNormalizedAtCost column periodicStrip current next valid
        processed cell ≤ 1000 * (budget + 1) := exact
    _ ≤ flatPackedNormalizedAtSpaceBound values := by
      simp [budget, core, flatPackedNormalizationAtCoreBound,
        flatPackedNormalizedAtSpaceBound, flatPackedNormalizationAtUnit]
      nlinarith

theorem flatPackedNormalizedAtBounded
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    EvaluatorCodeFits (Code.flatPackedNormalizedAtCode column)
      (Code.flatPackedTransitionScanState periodicStrip current next valid
        processed.length)
      [(current.normalizedAtBool periodicStrip column cell).toNat]
      (flatPackedNormalizedAtSpaceBound
        (Code.flatPackedTransitionScanState periodicStrip current next valid
          processed.length)) :=
  (flatPackedNormalizedAt column periodicStrip current next valid processed
    cell remaining split).mono
      (flatPackedNormalizedAtCost_le_bound column periodicStrip current next
        valid processed cell remaining split)

end EvaluatorCodeFits
end PartrecToTM2
end Turing
