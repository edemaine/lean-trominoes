/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatMotifIndex
import LeanTrominoes.PartrecFlatPackedAssignmentPredicates
import LeanTrominoes.PartrecPair
import LeanTrominoes.PartrecPackedNormalizedAt

/-!
# Packed normalization at an indexed flat motif cell

All motif-wide flat transition passes share the native state

`[valid, index, width, period, motif length,
  current word, current phase, next word, next phase, coordinates...]`.

This module indexes the current cell without consuming the coordinates and
implements the normalization predicate there using the flat assignment
lookup.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

/-- Shared flat state used by the motif-wide transition passes. -/
def flatPackedTransitionScanState
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState)
    (valid : Bool) (index : Nat) : List Nat :=
  [valid.toNat, index, periodicStrip.width, periodicStrip.period,
    periodicStrip.motif.length, current.assignmentWord, current.phase,
    next.assignmentWord, next.phase] ++
      periodicStrip.motif.flatMap
        PeriodicStripFlatEncoding.cellFields

/-- The two encoded coordinates of the indexed motif cell. -/
def flatPackedTransitionCellFieldCode (field : Fin 2) : Code :=
  flatMotifCellFieldAtCode 9 1 field.val

@[simp]
theorem flatPackedTransitionCellFieldCode_eval
    (field : Fin 2) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedTransitionCellFieldCode field).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure
        [(PeriodicStripFlatEncoding.cellFields cell)[field.val]?.getD 0] := by
  rw [flatPackedTransitionCellFieldCode]
  rw [flatPackedTransitionScanState, split]
  exact flatMotifCellFieldAtCode_eval_nineHeader
    valid.toNat periodicStrip.width periodicStrip.period
    (processed ++ cell :: remaining).length
    current.assignmentWord current.phase next.assignmentWord next.phase
    field processed cell remaining

/-- Pair the indexed native coordinates only for the already verified
coordinate-phase predicate. -/
def flatPackedTransitionCellCode : Code :=
  natPairCode.comp <|
    prepend (flatPackedTransitionCellFieldCode (0 : Fin 2))
      (flatPackedTransitionCellFieldCode (1 : Fin 2))

@[simp]
theorem flatPackedTransitionCellCode_eval
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    flatPackedTransitionCellCode.eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure [Encodable.encode cell] := by
  rcases cell with ⟨x, y⟩
  have xRun := flatPackedTransitionCellFieldCode_eval
    (0 : Fin 2) periodicStrip current next valid processed (x, y)
      remaining split
  have yRun := flatPackedTransitionCellFieldCode_eval
    (1 : Fin 2) periodicStrip current next valid processed (x, y)
      remaining split
  simp [flatPackedTransitionCellCode,
    PeriodicStripFlatEncoding.cellFields, xRun, yRun]

/-- Input to the coordinate half of packed normalization.  The unused motif
code is the constant zero. -/
def flatPackedNormalizedCoordinateArgumentsCode
    (column : WindowColumn) : Code :=
  prepend (get 3) <|
    prepend (get 6) <|
      prepend zero <|
        prepend (numeral column.val) <|
          prepend flatPackedTransitionCellCode (get 5)

def flatPackedNormalizedCoordinateCode
    (column : WindowColumn) : Code :=
  packedNormalizedAtCoordinateCode.comp
    (flatPackedNormalizedCoordinateArgumentsCode column)

@[simp]
theorem flatPackedNormalizedCoordinateCode_eval
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedNormalizedCoordinateCode column).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure
        [(decide
          (cell.1 =
            ((packedColumnPhaseNumerator periodicStrip.period
              current.phase column.val % periodicStrip.period : Nat) :
              Int))).toNat] := by
  have cellRun := flatPackedTransitionCellCode_eval
    periodicStrip current next valid processed cell remaining split
  have arguments :
      (flatPackedNormalizedCoordinateArgumentsCode column).eval
          (flatPackedTransitionScanState periodicStrip current next
            valid processed.length) =
        pure
          [periodicStrip.period, current.phase, 0, column.val,
            Encodable.encode cell, current.assignmentWord] := by
    let scanState := flatPackedTransitionScanState periodicStrip
      current next valid processed.length
    simp only [flatPackedNormalizedCoordinateArgumentsCode,
      prepend_eval_eq]
    rw [show (get 3).eval scanState = pure [periodicStrip.period] by
      simp [scanState, flatPackedTransitionScanState]]
    rw [show (get 6).eval scanState = pure [current.phase] by
      simp [scanState, flatPackedTransitionScanState]]
    rw [show zero.eval scanState = pure [0] by simp]
    rw [show (numeral column.val).eval scanState = pure [column.val] by simp]
    rw [cellRun]
    rw [show (get 5).eval scanState = pure [current.assignmentWord] by
      simp [scanState, flatPackedTransitionScanState]]
    simp
  calc
    _ = packedNormalizedAtCoordinateCode.eval
        [periodicStrip.period, current.phase, 0, column.val,
          Encodable.encode cell, current.assignmentWord] := by
      simp [flatPackedNormalizedCoordinateCode, arguments]
    _ = _ := packedNormalizedAtCoordinateCode_eval _ _ _ _ _ _

/-- Input to the flat assignment-absence half of normalization. -/
def flatPackedNormalizedNoneArgumentsCode
    (column : WindowColumn) : Code :=
  prepend (get 4) <|
    prepend (numeral column.val) <|
      prepend (flatPackedTransitionCellFieldCode (0 : Fin 2)) <|
        prepend (flatPackedTransitionCellFieldCode (1 : Fin 2)) <|
          prepend (get 5) (drop 9)

def flatPackedNormalizedNoneCode
    (column : WindowColumn) : Code :=
  flatPackedAssignmentIsNoneCode.comp
    (flatPackedNormalizedNoneArgumentsCode column)

@[simp]
theorem flatPackedNormalizedNoneCode_eval
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedNormalizedNoneCode column).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure
        [if (packedAssignmentLookupOutcome periodicStrip.motif column.val
          cell current.assignmentWord).2.1 = 0 then 1 else 0] := by
  have xRun := flatPackedTransitionCellFieldCode_eval
    (0 : Fin 2) periodicStrip current next valid processed cell remaining split
  have yRun := flatPackedTransitionCellFieldCode_eval
    (1 : Fin 2) periodicStrip current next valid processed cell remaining split
  have arguments :
      (flatPackedNormalizedNoneArgumentsCode column).eval
          (flatPackedTransitionScanState periodicStrip current next
            valid processed.length) =
        pure
          ([periodicStrip.motif.length, column.val,
              Encodable.encode cell.1, Encodable.encode cell.2,
              current.assignmentWord] ++
            periodicStrip.motif.flatMap
              PeriodicStripFlatEncoding.cellFields) := by
    let scanState := flatPackedTransitionScanState periodicStrip
      current next valid processed.length
    simp only [flatPackedNormalizedNoneArgumentsCode, prepend_eval_eq]
    rw [show (get 4).eval scanState =
        pure [periodicStrip.motif.length] by
      simp [scanState, flatPackedTransitionScanState]]
    rw [show (numeral column.val).eval scanState = pure [column.val] by simp]
    rw [xRun, yRun]
    rw [show (get 5).eval scanState = pure [current.assignmentWord] by
      simp [scanState, flatPackedTransitionScanState]]
    simp [flatPackedTransitionScanState,
      PeriodicStripFlatEncoding.cellFields]
  calc
    _ = flatPackedAssignmentIsNoneCode.eval
        ([periodicStrip.motif.length, column.val,
            Encodable.encode cell.1, Encodable.encode cell.2,
            current.assignmentWord] ++
          periodicStrip.motif.flatMap
            PeriodicStripFlatEncoding.cellFields) := by
      simp [flatPackedNormalizedNoneCode, arguments]
    _ = _ := flatPackedAssignmentIsNoneCode_eval _ _ _ _

/-- Complete normalization predicate at the indexed motif cell. -/
def flatPackedNormalizedAtCode
    (column : WindowColumn) : Code :=
  boolOr (flatPackedNormalizedCoordinateCode column)
    (flatPackedNormalizedNoneCode column)

@[simp]
theorem flatPackedNormalizedAtCode_eval
    (column : WindowColumn) (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState) (valid : Bool)
    (processed : List Cell) (cell : Cell) (remaining : List Cell)
    (split : periodicStrip.motif = processed ++ cell :: remaining) :
    (flatPackedNormalizedAtCode column).eval
        (flatPackedTransitionScanState periodicStrip current next
          valid processed.length) =
      pure [(current.normalizedAtBool periodicStrip column cell).toNat] := by
  have coordinateRun := flatPackedNormalizedCoordinateCode_eval
    column periodicStrip current next valid processed cell remaining split
  have noneRun := flatPackedNormalizedNoneCode_eval
    column periodicStrip current next valid processed cell remaining split
  let coordinate :=
    (decide
      (cell.1 =
        ((packedColumnPhaseNumerator periodicStrip.period
          current.phase column.val % periodicStrip.period : Nat) : Int))).toNat
  let assignmentNone :=
    if (packedAssignmentLookupOutcome periodicStrip.motif column.val
      cell current.assignmentWord).2.1 = 0 then 1 else 0
  have combined := boolOr_eval_at
    (flatPackedNormalizedCoordinateCode column)
    (flatPackedNormalizedNoneCode column)
    (flatPackedTransitionScanState periodicStrip current next
      valid processed.length)
    coordinate assignmentNone
    (by simpa [coordinate] using coordinateRun)
    (by simpa [assignmentNone] using noneRun)
  have resultEq := packedNormalizedAtResult_eq_semantic
    periodicStrip current column cell
  calc
    _ = pure
        [packedNormalizedAtResult periodicStrip.period current.phase
          periodicStrip.motif column.val cell current.assignmentWord] := by
      simpa [flatPackedNormalizedAtCode, packedNormalizedAtResult,
        coordinate, assignmentNone] using combined
    _ = _ := by rw [resultEq]

end Turing.ToPartrec.Code
