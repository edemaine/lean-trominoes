/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecPackedNormalizationLoop

/-!
# Complete packed frontier normalization program

The one-column streaming checker is run at each of the five fixed frontier
columns and the results are conjoined without constructing a column list.
The input is `[period, phase, motifCode, assignmentWord]`.
-/

namespace Turing.ToPartrec.Code

open LeanTrominoes
open LeanTrominoes.PeriodicStrip

attribute [local simp] Part.bind_eq_bind

/-- Insert one fixed column index into the input expected by the streaming
normalization checker. -/
def packedNormalizationColumnArgumentsCode
    (column : WindowColumn) : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (get 2) <|
        prepend (numeral column.val) (get 3)

@[simp]
theorem packedNormalizationColumnArgumentsCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    (packedNormalizationColumnArgumentsCode column).eval
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif,
          packed.assignmentWord] =
      pure
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif,
          column.val, packed.assignmentWord] := by
  simp [packedNormalizationColumnArgumentsCode]

/-- Normalize one fixed column from the shared four-field input. -/
def packedNormalizationColumnAtCode
    (column : WindowColumn) : Code :=
  packedNormalizationColumnCode.comp
    (packedNormalizationColumnArgumentsCode column)

@[simp]
theorem packedNormalizationColumnAtCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) (column : WindowColumn) :
    (packedNormalizationColumnAtCode column).eval
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif,
          packed.assignmentWord] =
      pure
        [(packed.normalizedColumnBool periodicStrip column).toNat] := by
  simp [packedNormalizationColumnAtCode]

private theorem boolAnd_eval_at_bool
    (leftCode rightCode : Code) (values : List Nat)
    (left right : Bool)
    (leftEval : leftCode.eval values = pure [left.toNat])
    (rightEval : rightCode.eval values = pure [right.toNat]) :
    (boolAnd leftCode rightCode).eval values =
      pure [(left && right).toNat] := by
  have combined := boolAnd_eval_at leftCode rightCode values
    left.toNat right.toNat leftEval rightEval
  cases left <;> cases right <;> simpa using combined

/-- Complete five-column normalization conjunction. -/
def packedNormalizationAllCode : Code :=
  boolAnd (packedNormalizationColumnAtCode (0 : WindowColumn)) <|
    boolAnd (packedNormalizationColumnAtCode (1 : WindowColumn)) <|
      boolAnd (packedNormalizationColumnAtCode (2 : WindowColumn)) <|
        boolAnd (packedNormalizationColumnAtCode (3 : WindowColumn))
          (packedNormalizationColumnAtCode (4 : WindowColumn))

@[simp]
theorem packedNormalizationAllCode_eval
    (periodicStrip : PeriodicStrip)
    (packed : PackedWindowState) :
    packedNormalizationAllCode.eval
        [periodicStrip.period, packed.phase,
          Encodable.encode periodicStrip.motif,
          packed.assignmentWord] =
      pure [(packed.isNormalizedBool periodicStrip).toNat] := by
  let values :=
    [periodicStrip.period, packed.phase,
      Encodable.encode periodicStrip.motif,
      packed.assignmentWord]
  have column0 := packedNormalizationColumnAtCode_eval
    periodicStrip packed (0 : WindowColumn)
  have column1 := packedNormalizationColumnAtCode_eval
    periodicStrip packed (1 : WindowColumn)
  have column2 := packedNormalizationColumnAtCode_eval
    periodicStrip packed (2 : WindowColumn)
  have column3 := packedNormalizationColumnAtCode_eval
    periodicStrip packed (3 : WindowColumn)
  have column4 := packedNormalizationColumnAtCode_eval
    periodicStrip packed (4 : WindowColumn)
  have lastTwo' := boolAnd_eval_at_bool
    (packedNormalizationColumnAtCode (3 : WindowColumn))
    (packedNormalizationColumnAtCode (4 : WindowColumn))
    values
    (packed.normalizedColumnBool periodicStrip (3 : WindowColumn))
    (packed.normalizedColumnBool periodicStrip (4 : WindowColumn))
    column3 column4
  have lastThree := boolAnd_eval_at_bool
    (packedNormalizationColumnAtCode (2 : WindowColumn))
    (boolAnd
      (packedNormalizationColumnAtCode (3 : WindowColumn))
      (packedNormalizationColumnAtCode (4 : WindowColumn)))
    values
    (packed.normalizedColumnBool periodicStrip (2 : WindowColumn))
    (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
      packed.normalizedColumnBool periodicStrip
        (4 : WindowColumn))
    column2
    lastTwo'
  have lastFour := boolAnd_eval_at_bool
    (packedNormalizationColumnAtCode (1 : WindowColumn))
    (boolAnd
      (packedNormalizationColumnAtCode (2 : WindowColumn))
      (boolAnd
        (packedNormalizationColumnAtCode (3 : WindowColumn))
        (packedNormalizationColumnAtCode (4 : WindowColumn))))
    values
    (packed.normalizedColumnBool periodicStrip (1 : WindowColumn))
    (packed.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
      (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
        packed.normalizedColumnBool periodicStrip
          (4 : WindowColumn)))
    column1
    lastThree
  have all := boolAnd_eval_at_bool
    (packedNormalizationColumnAtCode (0 : WindowColumn))
    (boolAnd
      (packedNormalizationColumnAtCode (1 : WindowColumn))
      (boolAnd
        (packedNormalizationColumnAtCode (2 : WindowColumn))
        (boolAnd
          (packedNormalizationColumnAtCode (3 : WindowColumn))
          (packedNormalizationColumnAtCode (4 : WindowColumn)))))
    values
    (packed.normalizedColumnBool periodicStrip (0 : WindowColumn))
    (packed.normalizedColumnBool periodicStrip (1 : WindowColumn) &&
      (packed.normalizedColumnBool periodicStrip (2 : WindowColumn) &&
        (packed.normalizedColumnBool periodicStrip (3 : WindowColumn) &&
          packed.normalizedColumnBool periodicStrip
            (4 : WindowColumn))))
    column0
    lastFour
  have columns :
      (List.finRange 5 : List (Fin 5)) = [0, 1, 2, 3, 4] := by
    native_decide
  rw [PackedWindowState.isNormalizedBool, columns]
  simpa [packedNormalizationAllCode, values] using all

end Turing.ToPartrec.Code
