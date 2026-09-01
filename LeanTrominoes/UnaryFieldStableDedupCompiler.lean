/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordRepresentativeValueLookupCompiler
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.UnaryFieldBinaryWordCompiler

/-! # Stable deduplication of unary fields -/

noncomputable section

namespace LeanTrominoes.UnaryFieldStableDedup

open Computability Turing

/-- Keep the first presentation of every unary natural, preserving source
order.  Length-coded binary words let the generic representative selector
compare arbitrary unary values. -/
def values (source : List Nat) : List Nat :=
  DelimitedBinaryWordRepresentativeValueLookup.selectedValues
    (UnaryFieldBinaryWords.words source) source

/-- Stable unary-field deduplication preserves polynomial time for every
polynomial-time compiled unary column. -/
noncomputable def valuesComputableInPolyTime
    {Input InputSymbol : Type}
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (sourceValues : Input → List Nat)
    (sourceCompiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields sourceValues) :
    TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields
      (fun input => values (sourceValues input)) := by
  let wordCompiler := TM2CompositionMachine.computableInPolyTime
    sourceCompiler UnaryFieldBinaryWords.wordsComputableInPolyTime
  unfold values
  exact
    DelimitedBinaryWordRepresentativeValueLookup.selectedValuesComputableInPolyTime
      encodeInput
      (fun input => UnaryFieldBinaryWords.words (sourceValues input))
      sourceValues
      (fun input => by simp [UnaryFieldBinaryWords.words])
      wordCompiler sourceCompiler

end LeanTrominoes.UnaryFieldStableDedup

end
