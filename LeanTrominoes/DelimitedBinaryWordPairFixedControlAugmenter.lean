/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairs
import LeanTrominoes.FiniteStateTransducerTime
import LeanTrominoes.FixedLengthWordEvaluator
import LeanTrominoes.SeparatedProductEncoding

/-! # Fixed-control augmentation of delimited word pairs -/

noncomputable section

namespace LeanTrominoes
namespace DelimitedBinaryWordPairFixedControlAugmenter

open Computability Turing
open DelimitedBinaryWordPairs

abbrev InputToken :=
  SeparatedProductEncoding.Token Bool DelimitedBinaryWordPairs.Token

structure State (controlCount : Nat) where
  controls : List.Vector Bool controlCount
  readingControls : Bool
  deriving DecidableEq, Fintype

def initialState (controlCount : Nat) : State controlCount :=
  ⟨List.Vector.replicate controlCount false, true⟩

instance (controlCount : Nat) : Inhabited (State controlCount) :=
  ⟨initialState controlCount⟩

def currentControl {controlCount : Nat}
    (state : State controlCount) : Bool :=
  state.controls.toList.headD false

def advance {controlCount : Nat} (state : State controlCount) :
    State controlCount :=
  { state with controls :=
      FixedLengthWordEvaluator.shiftAppend state.controls false }

def transition (amount controlCount : Nat) :
    State controlCount → InputToken →
      State controlCount × List DelimitedBinaryWordPairs.Token
  | state, .left control =>
      if state.readingControls then
        ({ state with controls :=
            FixedLengthWordEvaluator.shiftAppend state.controls control }, [])
      else
        (state, [])
  | state, .separator => ({ state with readingControls := false }, [])
  | state, .right .pairStart =>
      if state.readingControls then
        (state, [])
      else
        (state, [.pairStart] ++
          if currentControl state then
            List.replicate amount (.firstBit false)
          else [])
  | state, .right .pairEnd =>
      if state.readingControls then
        (state, [])
      else
        (advance state, [.pairEnd])
  | state, .right token =>
      if state.readingControls then (state, []) else (state, [token])

def finish {controlCount : Nat} (_ : State controlCount) :
    List DelimitedBinaryWordPairs.Token :=
  []

def output (amount controlCount : Nat) (input : List InputToken) :
    List DelimitedBinaryWordPairs.Token :=
  FiniteStateTransducer.output (initialState controlCount)
    (transition amount controlCount) finish input

/-- A fixed control count and fixed inserted magnitude define a finite-state,
linear-time physical transduction. -/
noncomputable def computableInPolyTime (amount controlCount : Nat) :
    TM2ComputableInPolyTime id id (output amount controlCount) := by
  change TM2ComputableInPolyTime id id
    (FiniteStateTransducer.output (initialState controlCount)
      (transition amount controlCount) finish)
  exact FiniteStateTransducer.computableInPolyTime
    (initialState controlCount) (transition amount controlCount) finish

end DelimitedBinaryWordPairFixedControlAugmenter
end LeanTrominoes

end
