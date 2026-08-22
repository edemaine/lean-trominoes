/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnaryRotatedRanksMachine
import LeanTrominoes.UnarySuccessorEqualityFilterInput

/-! # Promised inputs for unary rotated ranks -/

namespace LeanTrominoes
namespace UnaryRotatedRanksMachine

abbrev Valid := UnarySuccessorEqualityFilterMachine.Valid

structure Input where
  ranks : List Nat
  sizes : List Nat
  valid : Valid ranks sizes

def encode (input : Input) : List InputSymbol :=
  SeparatedProductEncoding.encode
    UnaryFieldEncoderMachine.unaryFields
    UnaryFieldEncoderMachine.unaryFields
    (input.ranks, input.sizes)

def outputEncoding (input : Input) : List UnarySymbol :=
  UnaryFieldEncoderMachine.unaryFields
    (rotatedRanks input.ranks input.sizes)

def fieldTime (rank size : Nat) : Nat :=
  if rank = 0 then 2 * size + 2 else 2 * rank + size + 2

def fieldsTime : List Nat → List Nat → Nat
  | rank :: ranks, size :: sizes =>
      fieldTime rank size + fieldsTime ranks sizes
  | _, _ => 0

@[simp] theorem fieldTime_zero (size : Nat) :
    fieldTime 0 size = 2 * size + 2 := by
  simp [fieldTime]

@[simp] theorem fieldTime_positive (rank size : Nat) (rankPos : 0 < rank) :
    fieldTime rank size = 2 * rank + size + 2 := by
  simp [fieldTime, Nat.ne_of_gt rankPos]

@[simp] theorem fieldsTime_nil_left (sizes : List Nat) :
    fieldsTime [] sizes = 0 := rfl

@[simp] theorem fieldsTime_nil_right (ranks : List Nat) :
    fieldsTime ranks [] = 0 := by
  cases ranks <;> rfl

@[simp] theorem fieldsTime_cons (rank size : Nat)
    (ranks sizes : List Nat) :
    fieldsTime (rank :: ranks) (size :: sizes) =
      fieldTime rank size + fieldsTime ranks sizes := rfl

end UnaryRotatedRanksMachine
end LeanTrominoes
