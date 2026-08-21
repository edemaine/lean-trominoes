/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnarySuccessorEqualityFilterMachine

/-! # Promised inputs for unary successor-equality filtering -/

namespace LeanTrominoes
namespace UnarySuccessorEqualityFilterMachine

/-- Paired unary values for which every rank is strictly below its group size. -/
structure Input where
  ranks : List Nat
  sizes : List Nat
  ranks_lt_sizes : List.Forall₂ (fun rank size => rank < size) ranks sizes

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

theorem Input.length_eq (input : Input) :
    input.ranks.length = input.sizes.length :=
  input.ranks_lt_sizes.length_eq

end UnarySuccessorEqualityFilterMachine
end LeanTrominoes
