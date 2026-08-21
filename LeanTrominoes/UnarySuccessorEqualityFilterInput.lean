/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterMachine

/-! # Promised inputs for unary successor-equality filtering -/

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

/-- Informative evidence that two lists are aligned and every rank is below
its corresponding size.  Living in `Type` allows exact execution certificates
to recurse over this evidence. -/
inductive Valid : List Nat → List Nat → Type
  | nil : Valid [] []
  | cons {rank size : Nat} {ranks sizes : List Nat}
      (rank_lt_size : rank < size) (rest : Valid ranks sizes) :
      Valid (rank :: ranks) (size :: sizes)

/-- Paired unary values for which every rank is strictly below its group size. -/
structure Input where
  ranks : List Nat
  sizes : List Nat
  valid : Valid ranks sizes

/-- The separated physical representation consumed by `machine`. -/
def encode (input : Input) : List InputSymbol :=
  SeparatedProductEncoding.encode
    UnaryFieldEncoderMachine.unaryFields
    UnaryFieldEncoderMachine.unaryFields
    (input.ranks, input.sizes)

/-- The unary fields that the filter must emit. -/
def outputEncoding (input : Input) : List UnarySymbol :=
  UnaryFieldEncoderMachine.unaryFields
    (selectedValues input.ranks input.sizes)

/-- Exact cost of filtering one promised field pair. -/
def fieldTime (rank size : Nat) : Nat :=
  if size = rank + 1 then
    5 * rank + 8
  else
    4 * rank + (size - (rank + 2)) + 8

/-- Sum of the exact costs for a sequence of aligned fields. -/
def fieldsTime : List Nat → List Nat → Nat
  | rank :: ranks, size :: sizes =>
      fieldTime rank size + fieldsTime ranks sizes
  | _, _ => 0

@[simp] theorem fieldTime_successor (rank : Nat) :
    fieldTime rank (rank + 1) = 5 * rank + 8 := by
  simp [fieldTime]

@[simp] theorem fieldTime_extra (rank extraUnits : Nat) :
    fieldTime rank (rank + 2 + extraUnits) =
      4 * rank + extraUnits + 8 := by
  simp [fieldTime]
  omega

@[simp] theorem fieldsTime_nil_left (sizes : List Nat) :
    fieldsTime [] sizes = 0 := rfl

@[simp] theorem fieldsTime_nil_right (ranks : List Nat) :
    fieldsTime ranks [] = 0 := by
  cases ranks <;> rfl

@[simp] theorem fieldsTime_cons (rank size : Nat)
    (ranks sizes : List Nat) :
    fieldsTime (rank :: ranks) (size :: sizes) =
      fieldTime rank size + fieldsTime ranks sizes := rfl

theorem Valid.length_eq {ranks sizes : List Nat}
    (valid : Valid ranks sizes) : ranks.length = sizes.length := by
  induction valid with
  | nil => rfl
  | cons _ _ induction => simp [induction]

theorem Input.length_eq (input : Input) :
    input.ranks.length = input.sizes.length :=
  input.valid.length_eq

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
