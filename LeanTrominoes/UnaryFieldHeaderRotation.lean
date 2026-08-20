/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Moving a counted unary field behind two header fields -/

namespace LeanTrominoes
namespace UnaryFieldHeaderRotation

open UnaryFieldEncoderMachine

/-- Consume one unary field.  End of input is treated as an implicit
delimiter, making the operation total on arbitrary symbol streams. -/
def consumeFieldAux : Nat → List Symbol → Nat × List Symbol
  | count, [] => (count, [])
  | count, .unit :: symbols => consumeFieldAux (count + 1) symbols
  | count, .delimiter :: symbols => (count, symbols)

def consumeField (symbols : List Symbol) : Nat × List Symbol :=
  consumeFieldAux 0 symbols

@[simp] theorem consumeFieldAux_replicate_unit
    (initial count : Nat) (symbols : List Symbol) :
    consumeFieldAux initial
        (List.replicate count .unit ++ .delimiter :: symbols) =
      (initial + count, symbols) := by
  induction count generalizing initial with
  | zero => simp [consumeFieldAux]
  | succ count induction =>
      simp only [List.replicate_succ, List.cons_append, consumeFieldAux]
      rw [induction]
      congr 1
      omega

@[simp] theorem consumeField_unaryField_append
    (count : Nat) (symbols : List Symbol) :
    consumeField (unaryField count ++ symbols) = (count, symbols) := by
  simp [consumeField, unaryField]

/-- Rotate the first unary field behind the next two.  Each of the first
three fields is normalized to a delimiter-terminated unary field; any suffix
after them is copied literally. -/
def rotateFirstFieldAfterTwo (symbols : List Symbol) : List Symbol :=
  let (first, afterFirst) := consumeField symbols
  let (second, afterSecond) := consumeField afterFirst
  let (third, suffix) := consumeField afterSecond
  unaryField second ++ unaryField third ++ unaryField first ++ suffix

@[simp] theorem rotateFirstFieldAfterTwo_unaryFields
    (first second third : Nat) (fields : List Nat) :
    rotateFirstFieldAfterTwo
        (unaryFields (first :: second :: third :: fields)) =
      unaryFields (second :: third :: first :: fields) := by
  simp only [rotateFirstFieldAfterTwo, unaryFields_cons,
    consumeField_unaryField_append]
  simp [List.append_assoc]

end UnaryFieldHeaderRotation
end LeanTrominoes
