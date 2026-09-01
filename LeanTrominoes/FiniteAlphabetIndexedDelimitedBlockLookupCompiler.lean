/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookupData
import LeanTrominoes.FiniteAlphabetKeyedValueLookupCompiler
import LeanTrominoes.FiniteUnaryFieldMapCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryPrefixSumsTime

/-! # Compiler for indexed finite-alphabet delimited-block lookup -/

noncomputable section

namespace LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookup

open Computability Turing

variable {Alphabet : Type} [Fintype Alphabet]

noncomputable def incrementsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (increments (Alphabet := Alphabet)) :=
  FiniteUnaryFieldMap.computableInPolyTime increment

noncomputable def candidateKeysComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      (candidateKeys (Alphabet := Alphabet)) := by
  unfold candidateKeys
  exact TM2CompositionMachine.computableInPolyTime
    (incrementsComputableInPolyTime (Alphabet := Alphabet))
    UnaryPrefixSumsMachine.computableInPolyTime

/-- Repeated unary ordinals can select and reorder arbitrary complete
finite-alphabet blocks from a polynomial-time delimited token stream. -/
noncomputable def selectedComputableInPolyTimeOf
    {Source SourceSymbol : Type}
    [Fintype SourceSymbol] [Inhabited SourceSymbol]
    (encodeSource : Source → List SourceSymbol)
    (queries : Source → List Nat)
    (tokens : Source → List (Token Alphabet))
    (queryCompiler : TM2ComputableInPolyTime encodeSource
      UnaryFieldEncoderMachine.unaryFields queries)
    (tokenCompiler : TM2ComputableInPolyTime encodeSource id tokens) :
    TM2ComputableInPolyTime encodeSource id
      (fun source => selected (queries source) (tokens source)) := by
  let keyCompiler := TM2CompositionMachine.computableInPolyTime
    tokenCompiler
    (candidateKeysComputableInPolyTime (Alphabet := Alphabet))
  unfold selected
  exact FiniteAlphabetKeyedValueLookup.valuesComputableInPolyTime
    encodeSource queries (fun source => candidateKeys (tokens source))
    tokens (fun source => candidateKeys_length (tokens source))
    queryCompiler keyCompiler tokenCompiler

end LeanTrominoes.FiniteAlphabetIndexedDelimitedBlockLookup

end
