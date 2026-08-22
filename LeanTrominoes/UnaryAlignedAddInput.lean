/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryAlignedAddMachine

/-! # Promised inputs for aligned unary addition -/

namespace LeanTrominoes
namespace UnaryAlignedAddMachine

/-- Informative evidence that the two unary-field lists are aligned. -/
inductive Valid : List Nat → List Nat → Type
  | nil : Valid [] []
  | cons {first second : Nat} {firsts seconds : List Nat}
      (rest : Valid firsts seconds) :
      Valid (first :: firsts) (second :: seconds)

structure Input where
  firsts : List Nat
  seconds : List Nat
  valid : Valid firsts seconds

def encode (input : Input) : List InputSymbol :=
  SeparatedProductEncoding.encode
    UnaryFieldEncoderMachine.unaryFields
    UnaryFieldEncoderMachine.unaryFields
    (input.firsts, input.seconds)

def outputEncoding (input : Input) : List UnarySymbol :=
  UnaryFieldEncoderMachine.unaryFields
    (sums input.firsts input.seconds)

def fieldTime (first second : Nat) : Nat :=
  2 * first + 2 * second + 3

def fieldsTime : List Nat → List Nat → Nat
  | first :: firsts, second :: seconds =>
      fieldTime first second + fieldsTime firsts seconds
  | _, _ => 0

theorem Valid.length_eq {firsts seconds : List Nat}
    (valid : Valid firsts seconds) : firsts.length = seconds.length := by
  induction valid with
  | nil => rfl
  | cons rest induction => simp [induction]

theorem Input.length_eq (input : Input) :
    input.firsts.length = input.seconds.length :=
  input.valid.length_eq

@[simp] theorem fieldsTime_nil : fieldsTime [] [] = 0 := rfl

@[simp] theorem fieldsTime_cons (first second : Nat)
    (firsts seconds : List Nat) :
    fieldsTime (first :: firsts) (second :: seconds) =
      fieldTime first second + fieldsTime firsts seconds := rfl

end UnaryAlignedAddMachine
end LeanTrominoes
