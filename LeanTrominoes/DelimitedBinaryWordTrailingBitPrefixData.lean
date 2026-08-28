/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteStateTransducerData

/-! # Moving a trailing word bit behind a fixed prefix

On words of the form `payload ++ [constructor]`, this transformation emits
`false :: constructor :: payload`.  Reversing the complete token stream
makes the trailing bit locally available to a finite-state pass; a second
reversal restores both word order and bit order.
-/

namespace LeanTrominoes.DelimitedBinaryWordTrailingBitPrefix

open DelimitedBinaryWords

inductive Control
  | between
  | trailing
  | body (trailingBit : Bool)
  deriving DecidableEq, Fintype, Inhabited

/-- Process the reversal of a canonical nonempty word token stream. -/
def reverseTransition : Control → Token → Control × List Token
  | .between, .wordEnd => (.trailing, [.wordEnd])
  | .between, _ => (.between, [])
  | .trailing, .bit bit => (.body bit, [])
  | .trailing, .wordStart =>
      (.between, [.bit false, .bit false, .wordStart])
  | .trailing, .wordEnd => (.trailing, [])
  | .body trailingBit, .wordStart =>
      (.between, [.bit trailingBit, .bit false, .wordStart])
  | .body trailingBit, token => (.body trailingBit, [token])

def finish (_ : Control) : List Token := []

def reversePass (source : List Token) : List Token :=
  FiniteStateTransducer.output .between reverseTransition finish source

/-- Reverse, perform the locally reversed-word pass, and reverse again. -/
def tokens (source : List Token) : List Token :=
  (reversePass source.reverse).reverse

/-- Semantic input words, each annotated by its final bit. -/
def trailingWords (items : List (List Bool × Bool)) :
    DelimitedBinaryWords.Input :=
  ⟨items.map fun item => item.1 ++ [item.2]⟩

/-- Semantic output words with the fixed first constructor bit. -/
def prefixedWords (items : List (List Bool × Bool)) :
    DelimitedBinaryWords.Input :=
  ⟨items.map fun item => false :: item.2 :: item.1⟩

end LeanTrominoes.DelimitedBinaryWordTrailingBitPrefix
