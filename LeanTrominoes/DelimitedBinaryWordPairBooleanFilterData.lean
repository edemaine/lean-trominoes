/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairs
import LeanTrominoes.SeparatedProductEncoding

/-! # Boolean filtering of delimited binary-word pairs -/

namespace LeanTrominoes.DelimitedBinaryWordPairBooleanFilter

/-- Retain each pair exactly when its aligned Boolean control is true.
Extra controls and extra pairs are both ignored. -/
def selectedPairs :
    List Bool → List (List Bool × List Bool) →
      List (List Bool × List Bool)
  | active :: controls, pair :: pairs =>
      (if active then [pair] else []) ++ selectedPairs controls pairs
  | _, _ => []

structure Input where
  controls : List Bool
  pairs : List (List Bool × List Bool)
  aligned : controls.length = pairs.length

def output (input : Input) :
    DelimitedBinaryWordPairs.Input :=
  ⟨selectedPairs input.controls input.pairs⟩

abbrev InputToken :=
  SeparatedProductEncoding.Token Bool DelimitedBinaryWordPairs.Token

def encodeInput (input : Input) :
    List InputToken :=
  SeparatedProductEncoding.encode id DelimitedBinaryWordPairs.encode
    (input.controls, ⟨input.pairs⟩)

end LeanTrominoes.DelimitedBinaryWordPairBooleanFilter
