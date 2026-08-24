/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.FiniteStateTransducerFunctionData

/-! # Merging adjacent guarded binary words -/

namespace LeanTrominoes.DelimitedBinaryWordGuardedPairMerge

open DelimitedBinaryWords

inductive Control
  | firstStart
  | firstBit
  | firstBody (active : Bool)
  | secondStart (active : Bool)
  | secondBody (active : Bool)
  deriving DecidableEq, Fintype, Inhabited

/-- Copy the first word of each pair.  Copy the second body only when the
first word begins with the active guard `true`; suppress the two inner word
delimiters in either case. -/
def transition : Control → Token → Control × List Token
  | .firstStart, .wordStart => (.firstBit, [.wordStart])
  | .firstStart, _ => (.firstStart, [])
  | .firstBit, .bit bit => (.firstBody bit, [.bit bit])
  | .firstBit, .wordEnd => (.secondStart false, [])
  | .firstBit, .wordStart => (.firstBit, [])
  | .firstBody active, .bit bit => (.firstBody active, [.bit bit])
  | .firstBody active, .wordEnd => (.secondStart active, [])
  | .firstBody active, .wordStart => (.firstBody active, [])
  | .secondStart active, .wordStart => (.secondBody active, [])
  | .secondStart active, _ => (.secondStart active, [])
  | .secondBody active, .bit bit =>
      (.secondBody active, if active then [.bit bit] else [])
  | .secondBody _, .wordEnd => (.firstStart, [.wordEnd])
  | .secondBody active, .wordStart => (.secondBody active, [])

/-- An odd final first word is already open in the output and is closed at
end of input.  Canonical encoded inputs cannot finish in a body state. -/
def finish : Control → List Token
  | .firstStart => []
  | _ => [.wordEnd]

def tokens (source : List Token) : List Token :=
  LightweightFiniteStateTransducer.output
    .firstStart transition finish source

/-- Merge one semantic pair.  A `true` first guard retains the second word;
an inactive or empty first word suppresses it. -/
def mergePair (first second : List Bool) : List Bool :=
  match first with
  | true :: _ => first ++ second
  | _ => first

/-- Merge adjacent words left-to-right, preserving an odd final word. -/
def mergeWords : List (List Bool) → List (List Bool)
  | first :: second :: words =>
      mergePair first second :: mergeWords words
  | [first] => [first]
  | [] => []

def output (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨mergeWords input.words⟩

/-- Flatten an explicit list of word pairs to the adjacent component stream
consumed by the physical merger. -/
def componentWords (pairs : List (List Bool × List Bool)) :
    DelimitedBinaryWords.Input :=
  ⟨pairs.flatMap fun pair => [pair.1, pair.2]⟩

/-- The corresponding semantic stream after merging every adjacent pair. -/
def mergedWords (pairs : List (List Bool × List Bool)) :
    DelimitedBinaryWords.Input :=
  ⟨pairs.map fun pair => mergePair pair.1 pair.2⟩

end LeanTrominoes.DelimitedBinaryWordGuardedPairMerge
