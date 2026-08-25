/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordGuardedPairMergeData
import LeanTrominoes.FiniteStateTransducerData

/-! # Selecting one word from each adjacent binary-word pair -/

namespace LeanTrominoes.DelimitedBinaryWordPairSelector

open DelimitedBinaryWords

inductive Side
  | first
  | second
  deriving DecidableEq, Fintype

inductive Control
  | first
  | second
  deriving DecidableEq, Fintype

def selected : Side → Control → Bool
  | .first, .first => true
  | .second, .second => true
  | _, _ => false

def advance : Control → Token → Control
  | .first, .wordEnd => .second
  | .second, .wordEnd => .first
  | control, _ => control

def transition (side : Side) (control : Control) (token : Token) :
    Control × List Token :=
  (advance control token,
    if selected side control then [token] else [])

def finish (_ : Control) : List Token := []

/-- Retain exactly the selected member of every adjacent word pair. -/
def tokens (side : Side) (source : List Token) : List Token :=
  FiniteStateTransducer.output .first (transition side) finish source

def select (side : Side) (pair : List Bool × List Bool) : List Bool :=
  match side with
  | .first => pair.1
  | .second => pair.2

def selectedWords (side : Side)
    (pairs : List (List Bool × List Bool)) : DelimitedBinaryWords.Input :=
  ⟨pairs.map (select side)⟩

end LeanTrominoes.DelimitedBinaryWordPairSelector
