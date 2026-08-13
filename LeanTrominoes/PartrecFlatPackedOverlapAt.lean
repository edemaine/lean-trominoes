/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PartrecFlatPackedAssignmentPredicates
import LeanTrominoes.PartrecPackedOverlapAt

/-!
# Flat packed overlap at one motif occurrence

The four shared columns of adjacent packed windows are compared one motif
occurrence at a time.  This flat port performs the two assignment lookups and
compares their base-nine digits while retaining the complete coordinate
stream.
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

/-- Flat input for one packed overlap comparison. -/
def flatPackedOverlapAtInput
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) : List Nat :=
  [motif.length, currentColumn, nextColumn,
      Encodable.encode base.1, Encodable.encode base.2,
      currentWord, nextWord] ++
    motif.flatMap PeriodicStripFlatEncoding.cellFields

/-- Flat assignment-lookup input for the current window. -/
def flatPackedOverlapCurrentArgumentsCode : Code :=
  prepend (get 0) <|
    prepend (get 1) <|
      prepend (get 3) <|
        prepend (get 4) <|
          prepend (get 5) (drop 7)

@[simp]
theorem flatPackedOverlapCurrentArgumentsCode_eval
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedOverlapCurrentArgumentsCode.eval
        (flatPackedOverlapAtInput motif currentColumn nextColumn
          base currentWord nextWord) =
      pure
        ([motif.length, currentColumn,
            Encodable.encode base.1, Encodable.encode base.2,
            currentWord] ++
          motif.flatMap PeriodicStripFlatEncoding.cellFields) := by
  simp [flatPackedOverlapCurrentArgumentsCode,
    flatPackedOverlapAtInput]

/-- Flat assignment-lookup input for the next window. -/
def flatPackedOverlapNextArgumentsCode : Code :=
  prepend (get 0) <|
    prepend (get 2) <|
      prepend (get 3) <|
        prepend (get 4) <|
          prepend (get 6) (drop 7)

@[simp]
theorem flatPackedOverlapNextArgumentsCode_eval
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedOverlapNextArgumentsCode.eval
        (flatPackedOverlapAtInput motif currentColumn nextColumn
          base currentWord nextWord) =
      pure
        ([motif.length, nextColumn,
            Encodable.encode base.1, Encodable.encode base.2,
            nextWord] ++
          motif.flatMap PeriodicStripFlatEncoding.cellFields) := by
  simp [flatPackedOverlapNextArgumentsCode,
    flatPackedOverlapAtInput]

def flatPackedOverlapCurrentDigitCode : Code :=
  flatPackedAssignmentLookupDigitCode.comp
    flatPackedOverlapCurrentArgumentsCode

@[simp]
theorem flatPackedOverlapCurrentDigitCode_eval
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedOverlapCurrentDigitCode.eval
        (flatPackedOverlapAtInput motif currentColumn nextColumn
          base currentWord nextWord) =
      pure
        [(packedAssignmentLookupOutcome motif currentColumn
          base currentWord).2.1] := by
  have arguments := flatPackedOverlapCurrentArgumentsCode_eval
    motif currentColumn nextColumn base currentWord nextWord
  have digit := flatPackedAssignmentLookupDigitCode_eval
    motif currentColumn base currentWord
  simpa only [flatPackedOverlapCurrentDigitCode] using
    (comp_eval_pure _ _ _ _ arguments).trans digit

def flatPackedOverlapNextDigitCode : Code :=
  flatPackedAssignmentLookupDigitCode.comp
    flatPackedOverlapNextArgumentsCode

@[simp]
theorem flatPackedOverlapNextDigitCode_eval
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedOverlapNextDigitCode.eval
        (flatPackedOverlapAtInput motif currentColumn nextColumn
          base currentWord nextWord) =
      pure
        [(packedAssignmentLookupOutcome motif nextColumn
          base nextWord).2.1] := by
  have arguments := flatPackedOverlapNextArgumentsCode_eval
    motif currentColumn nextColumn base currentWord nextWord
  have digit := flatPackedAssignmentLookupDigitCode_eval
    motif nextColumn base nextWord
  simpa only [flatPackedOverlapNextDigitCode] using
    (comp_eval_pure _ _ _ _ arguments).trans digit

/-- Assemble the two flat selected base-nine digits for equality. -/
def flatPackedOverlapEqualityArgumentsCode : Code :=
  prepend flatPackedOverlapCurrentDigitCode
    flatPackedOverlapNextDigitCode

@[simp]
theorem flatPackedOverlapEqualityArgumentsCode_eval
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedOverlapEqualityArgumentsCode.eval
        (flatPackedOverlapAtInput motif currentColumn nextColumn
          base currentWord nextWord) =
      pure
        [(packedAssignmentLookupOutcome motif currentColumn
            base currentWord).2.1,
          (packedAssignmentLookupOutcome motif nextColumn
            base nextWord).2.1] := by
  simp [flatPackedOverlapEqualityArgumentsCode]

/-- Return one exactly when the two flat packed assignments agree at one
shared motif occurrence. -/
def flatPackedOverlapAtCode : Code :=
  natEqCode.comp flatPackedOverlapEqualityArgumentsCode

@[simp]
theorem flatPackedOverlapAtCode_eval
    (motif : List Cell) (currentColumn nextColumn : Nat)
    (base : Cell) (currentWord nextWord : Nat) :
    flatPackedOverlapAtCode.eval
        (flatPackedOverlapAtInput motif currentColumn nextColumn
          base currentWord nextWord) =
      pure
        [if
          (packedAssignmentLookupOutcome motif currentColumn
              base currentWord).2.1 =
            (packedAssignmentLookupOutcome motif nextColumn
              base nextWord).2.1
        then 1 else 0] := by
  simp [flatPackedOverlapAtCode]

/-- The flat arithmetic digit comparison is the semantic packed overlap test. -/
@[simp]
theorem flatPackedOverlapAtCode_eval_semantic
    (periodicStrip : PeriodicStrip)
    (current next : PackedWindowState)
    (column : Fin 4) (base : Cell) :
    flatPackedOverlapAtCode.eval
        (flatPackedOverlapAtInput periodicStrip.motif
          column.succ.val column.castSucc.val base
          current.assignmentWord next.assignmentWord) =
      pure
        [(current.overlapsAtBool periodicStrip
          next column base).toNat] := by
  rw [flatPackedOverlapAtCode_eval]
  rw [packedOverlapAtResult_eq_semantic
    periodicStrip current next column base]

end Turing.ToPartrec.Code
