/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PrefixSums
import LeanTrominoes.UnaryBlockRightRotationMachine

/-! # Promised inputs for unary block right rotation -/

namespace LeanTrominoes.UnaryBlockRightRotationMachine

/-- Informative evidence that each group size has one block start. -/
inductive Valid : List Nat → List Nat → Type
  | nil : Valid [] []
  | cons {groupSize blockStart : Nat} {groupSizes blockStarts : List Nat}
      (rest : Valid groupSizes blockStarts) :
      Valid (groupSize :: groupSizes) (blockStart :: blockStarts)

structure Input where
  groupSizes : List Nat
  blockStarts : List Nat
  valid : Valid groupSizes blockStarts

def encode (input : Input) : List InputSymbol :=
  SeparatedProductEncoding.encode
    UnaryFieldEncoderMachine.unaryFields
    UnaryFieldEncoderMachine.unaryFields
    (input.groupSizes, input.blockStarts)

def outputEncoding (input : Input) : List UnarySymbol :=
  UnaryFieldEncoderMachine.unaryFields
    (rotatedBlocks input.groupSizes input.blockStarts)

theorem Valid.length_eq {groupSizes blockStarts : List Nat}
    (valid : Valid groupSizes blockStarts) :
    groupSizes.length = blockStarts.length := by
  induction valid with
  | nil => rfl
  | cons rest induction => simp [induction]

theorem Input.length_eq (input : Input) :
    input.groupSizes.length = input.blockStarts.length :=
  input.valid.length_eq

/-- Prefix starts from any initial index are aligned with their group sizes. -/
def Valid.prefixStartsAux (blockStart : Nat) : (groupSizes : List Nat) →
    Valid groupSizes (PrefixSums.startsAux blockStart groupSizes)
  | [] => .nil
  | groupSize :: groupSizes =>
      .cons (prefixStartsAux (blockStart + groupSize) groupSizes)

/-- Prefix starts are aligned with their source group sizes. -/
def Valid.prefixStarts (groupSizes : List Nat) :
    Valid groupSizes (PrefixSums.starts groupSizes) :=
  prefixStartsAux 0 groupSizes

end LeanTrominoes.UnaryBlockRightRotationMachine
