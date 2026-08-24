/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedLengthWordEvaluator
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Unary fields from fixed axes and runtime activations -/

noncomputable section

namespace LeanTrominoes.FixedAxisUnaryFields

open Computability Turing

/-- An active horizontal slot carries one; every other slot carries zero. -/
def value (active horizontal : Bool) : Nat :=
  if active && horizontal then 1 else 0

/-- Unary values aligned with a runtime activation word and fixed axis word. -/
def values (axes actives : List Bool) : List Nat :=
  List.zipWith value actives axes

/-- Finite-control implementation at one fixed axis-word length. -/
def compiledFields (axes actives : List Bool) :
    List UnaryFieldEncoderMachine.Symbol :=
  FixedLengthWordEvaluator.output axes.length
    (fun stored => UnaryFieldEncoderMachine.unaryFields
      (values axes stored)) actives

/-- Exact-length activation words are converted to their canonical unary
zero-or-one fields. -/
@[simp] theorem compiledFields_eq (axes actives : List Bool)
    (lengthEq : actives.length = axes.length) :
    compiledFields axes actives =
      UnaryFieldEncoderMachine.unaryFields (values axes actives) := by
  unfold compiledFields
  rw [FixedLengthWordEvaluator.output_eq_of_length_eq _ _ _ lengthEq]

/-- For every fixed axis word, the activation-to-unary-field adapter is a
polynomial-time finite-control computation. -/
noncomputable def compiledFieldsComputableInPolyTime (axes : List Bool) :
    TM2ComputableInPolyTime id id (compiledFields axes) :=
  FixedLengthWordEvaluator.computableInPolyTime axes.length
    (fun stored => UnaryFieldEncoderMachine.unaryFields
      (values axes stored))

end LeanTrominoes.FixedAxisUnaryFields

end
