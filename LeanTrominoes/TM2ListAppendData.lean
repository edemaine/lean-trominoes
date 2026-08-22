/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.SeparatedProductEncoding

/-! # Concatenating two separated list outputs -/

namespace LeanTrominoes
namespace TM2ListAppend

abbrev PairSymbol (Symbol : Type) :=
  SeparatedProductEncoding.Token Symbol Symbol

def mergeBlock {Symbol : Type} : PairSymbol Symbol → List Symbol
  | .left symbol => [symbol]
  | .separator => []
  | .right symbol => [symbol]

def merge {Symbol : Type} (tokens : List (PairSymbol Symbol)) :
    List Symbol :=
  tokens.flatMap mergeBlock

def appendPair {Symbol : Type} (pair : List Symbol × List Symbol) :
    List Symbol :=
  pair.1 ++ pair.2

@[simp] theorem merge_separated {Symbol : Type}
    (first second : List Symbol) :
    merge (SeparatedProductEncoding.encode id id (first, second)) =
      appendPair (first, second) := by
  simp [merge, mergeBlock, appendPair,
    SeparatedProductEncoding.encode, List.flatMap_map]

end TM2ListAppend
end LeanTrominoes
