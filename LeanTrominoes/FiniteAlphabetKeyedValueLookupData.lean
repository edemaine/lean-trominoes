/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordBooleanFilterCompiler
import LeanTrominoes.DelimitedBinaryWordEqualitySquareData
import LeanTrominoes.DelimitedBinaryWordPairProductMachine
import LeanTrominoes.FiniteIndexSlotUnaryDecoderCompiler
import LeanTrominoes.UnaryFieldBinaryWordCompiler
import LeanTrominoes.UnaryFieldPairPresenceCompiler

/-! # Keyed selection of values from a finite alphabet -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetKeyedValueLookup

variable {Value : Type} [Fintype Value] [Nonempty Value]

instance valueCardNeZero : NeZero (Fintype.card Value) :=
  ⟨Fintype.card_ne_zero⟩

/-- Reserve slot one of the generic eight-slot finite decoder for every
finite value.  Thus all candidate metadata words are nonempty, while query
metadata words can be the empty word. -/
def valueCode (value : Value) : Nat :=
  8 * (Fintype.equivFin Value value).val + 1

def valueCodes (candidateValues : List Value) : List Nat :=
  candidateValues.map valueCode

/-- Query entries carry zero; candidate entries carry their positive finite
value codes. -/
def metadata (queries : List Nat) (candidateValues : List Value) : List Nat :=
  queries.map (fun _ => 0) ++ valueCodes candidateValues

/-- Query keys precede the key attached to every candidate value. -/
def combinedKeys (queries candidateKeys : List Nat) : List Nat :=
  queries ++ candidateKeys

def keyWords (queries candidateKeys : List Nat) :
    DelimitedBinaryWords.Input :=
  UnaryFieldBinaryWords.words (combinedKeys queries candidateKeys)

def metadataWords (queries : List Nat) (candidateValues : List Value) :
    DelimitedBinaryWords.Input :=
  UnaryFieldBinaryWords.words (metadata queries candidateValues)

def metadataPairs (queries : List Nat) (candidateValues : List Value) :
    DelimitedBinaryWordPairs.Input :=
  DelimitedBinaryWordPairProductMachine.pairs
    (metadataWords queries candidateValues)

/-- True exactly on square positions whose row belongs to the zero-coded
query prefix and whose column belongs to the positive-coded candidate
suffix. -/
def roleBits (queries : List Nat) (candidateValues : List Value) : List Bool :=
  List.zipWith (fun first second => first && second)
    ((UnaryFieldPairPresence.bits .first
      (metadataPairs queries candidateValues)).map (!·))
    (UnaryFieldPairPresence.bits .second
      (metadataPairs queries candidateValues))

@[simp] theorem roleBits_length (queries : List Nat)
    (candidateValues : List Value) :
    (roleBits queries candidateValues).length =
      (queries.length + candidateValues.length) ^ 2 := by
  calc
    (roleBits queries candidateValues).length =
        (metadataPairs queries candidateValues).pairs.length := by
      simp [roleBits, UnaryFieldPairPresence.bits]
    _ = (metadataWords queries candidateValues).words.length ^ 2 := by
      simp [metadataPairs, DelimitedBinaryWordPairProductMachine.pairs,
        pow_two]
    _ = (queries.length + candidateValues.length) ^ 2 := by
      simp [metadataWords, metadata, valueCodes,
        UnaryFieldBinaryWords.words]

/-- Equality restricted to query-row/candidate-column positions. -/
def controls (queries candidateKeys : List Nat)
    (candidateValues : List Value) : List Bool :=
  List.zipWith (fun first second => first && second)
    (DelimitedBinaryWordEqualitySquare.equalityBits
      (keyWords queries candidateKeys))
    (roleBits queries candidateValues)

/-- The second metadata word at every row-major square position, recovered by
its unary length. -/
def repeatedCodes (queries : List Nat)
    (candidateValues : List Value) : List Nat :=
  (metadataPairs queries candidateValues).pairs.map fun pair => pair.2.length

/-- Codes at precisely the equal-key query/candidate positions. -/
def selectedCodes (queries candidateKeys : List Nat)
    (candidateValues : List Value) : List Nat :=
  DelimitedBinaryWordBooleanFilter.selected
    (controls queries candidateKeys candidateValues)
    (repeatedCodes queries candidateValues)

abbrev DecodedPair (Value : Type) [Fintype Value] :=
  FiniteIndexSlotUnaryDecoder.Pair (Fintype.card Value)

def decodedPairs (queries candidateKeys : List Nat)
    (candidateValues : List Value) : List (DecodedPair Value) :=
  FiniteIndexSlotUnaryDecoder.pairs (Fintype.card Value)
    (selectedCodes queries candidateKeys candidateValues)

def pairValue (pair : DecodedPair Value) : Value :=
  (Fintype.equivFin Value).symm pair.1

/-- Candidate values selected once for every equal query key, in query-major
and candidate-minor order. -/
def values (queries candidateKeys : List Nat)
    (candidateValues : List Value) : List Value :=
  (decodedPairs queries candidateKeys candidateValues).map pairValue

/-- Direct relational specification of the keyed selection. -/
def expected (queries candidateKeys : List Nat)
    (candidateValues : List Value) : List Value :=
  queries.flatMap fun query =>
    (candidateKeys.zip candidateValues).flatMap fun candidate =>
      if query = candidate.1 then [candidate.2] else []

end LeanTrominoes.FiniteAlphabetKeyedValueLookup

end
