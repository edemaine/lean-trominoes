/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookupCompiler
import LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookupData

/-! # Compiler for arbitrarily keyed finite-alphabet blocks -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookup

open Computability Turing

variable {Alphabet : Type} [Fintype Alphabet]

/-- Broadcast compiled block keys across every token of an independently
compiled delimited block stream. -/
noncomputable def broadcastKeysComputableInPolyTimeOf
    {Source SourceSymbol : Type}
    [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (encodeSource : Source → List SourceSymbol)
    (blockKeys : Source → List Nat)
    (tokens : Source → List (Token Alphabet))
    (blockKeyCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields blockKeys)
    (tokenCompiler : TM2ComputableInPolyTime encodeSource id tokens) :
    TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields
      (fun source => broadcastKeys
        (blockKeys source) (tokens source)) := by
  let ordinalCompiler := TM2CompositionMachine.computableInPolyTime
    tokenCompiler
    (FiniteAlphabetIndexedDelimitedBlockLookup.candidateKeysComputableInPolyTime
      (Alphabet := Alphabet))
  unfold broadcastKeys
  exact UnaryIndexedValueLookup.valuesComputableInPolyTime
    encodeSource
    (fun source =>
      FiniteAlphabetIndexedDelimitedBlockLookup.candidateKeys
        (tokens source))
    blockKeys ordinalCompiler blockKeyCompiler

/-- Repeated arbitrary keys can select and reorder complete delimited blocks
from a keyed finite-alphabet stream in polynomial time. -/
noncomputable def selectedComputableInPolyTimeOf
    {Source SourceSymbol : Type}
    [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (encodeSource : Source → List SourceSymbol)
    (queries blockKeys : Source → List Nat)
    (tokens : Source → List (Token Alphabet))
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (blockKeyCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields blockKeys)
    (tokenCompiler : TM2ComputableInPolyTime encodeSource id tokens) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => selected (queries source)
        (blockKeys source) (tokens source)) := by
  let broadcastCompiler := broadcastKeysComputableInPolyTimeOf
    (Alphabet := Alphabet) encodeSource blockKeys tokens
    blockKeyCompiler tokenCompiler
  unfold selected
  exact FiniteAlphabetKeyedValueLookup.valuesComputableInPolyTime
    encodeSource queries
    (fun source => broadcastKeys (blockKeys source) (tokens source))
    tokens
    (fun source => broadcastKeys_length
      (blockKeys source) (tokens source))
    queryCompiler broadcastCompiler tokenCompiler

end LeanTrominoes.FiniteAlphabetKeyedDelimitedBlockLookup

end
