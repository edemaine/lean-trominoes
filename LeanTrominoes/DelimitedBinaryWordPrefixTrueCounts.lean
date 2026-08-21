/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/

import LeanTrominoes.DelimitedBinaryWords

/-! # True counts in successively longer row prefixes -/

namespace LeanTrominoes
namespace DelimitedBinaryWordPrefixTrueCounts

/-- Number of true bits before the current row's diagonal position. -/
def count (rowIndex : Nat) (row : List Bool) : Nat :=
  (row.take rowIndex).count true

def countsAux : Nat → List (List Bool) → List Nat
  | _, [] => []
  | rowIndex, row :: rows =>
      count rowIndex row :: countsAux (rowIndex + 1) rows

/-- Prefix-true count of every row, starting with an empty prefix. -/
def counts (input : DelimitedBinaryWords.Input) : List Nat :=
  countsAux 0 input.words

@[simp] theorem countsAux_nil (rowIndex : Nat) :
    countsAux rowIndex [] = [] := rfl

@[simp] theorem countsAux_cons (rowIndex : Nat) (row : List Bool)
    (rows : List (List Bool)) :
    countsAux rowIndex (row :: rows) =
      count rowIndex row :: countsAux (rowIndex + 1) rows := rfl

@[simp] theorem countsAux_length (rowIndex : Nat)
    (rows : List (List Bool)) :
    (countsAux rowIndex rows).length = rows.length := by
  induction rows generalizing rowIndex with
  | nil => rfl
  | cons row rows induction =>
      simp [countsAux, induction]

@[simp] theorem counts_length (input : DelimitedBinaryWords.Input) :
    (counts input).length = input.words.length := by
  simp [counts]

end DelimitedBinaryWordPrefixTrueCounts
end LeanTrominoes
