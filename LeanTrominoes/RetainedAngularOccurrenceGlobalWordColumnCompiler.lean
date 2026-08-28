/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordEqualitySquareCompiler
import LeanTrominoes.RetainedAngularOccurrenceGlobalAtomWordSemantics
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankComponentCompiler
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateComponentCompiler

/-! # Stable-rank compilation from structural atom words -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing
open TerminalCoordinateComponents

/-- An exact injective atom-word stream compiles the semantic same-atom
comparison square. -/
noncomputable def
    retainedOccurrenceGlobalAtomEqualityBitsComputableInPolyTimeOfWords
    {Input InputSymbol Variable : Type}
    [DecidableEq Variable]
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (source : Input → PeriodicCNF Variable)
    (atomWord : Input → Variable → List Bool)
    (atomWordInjective : ∀ input,
      Function.Injective (atomWord input))
    (atomWordCompiler : @TM2ComputableInPolyTime
      Input DelimitedBinaryWords.Input InputSymbol DelimitedBinaryWords.Token
      encodeInput DelimitedBinaryWords.finEncoding.encode
      (fun input => retainedOccurrenceGlobalAtomWords
        (source input) (atomWord input))) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => retainedOccurrenceGlobalAtomEqualityBits
        (source input)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (DelimitedBinaryWordEqualitySquare.equalityBitsComputableInPolyTime
      encodeInput
      (fun input => retainedOccurrenceGlobalAtomWords
        (source input) (atomWord input))
      atomWordCompiler)
    (fun input =>
      (retainedOccurrenceGlobalAtomEqualityBits_eq_words
        (source input) (atomWord input)
        (atomWordInjective input)).symm)

/-- Structural atom words, terminal direction ranks, and terminal radial
lengths suffice to compile the complete semantic stable-rank stream. -/
noncomputable def
    retainedOccurrenceGlobalStableTerminalRanksComputableInPolyTimeOfWordColumns
    {Input InputSymbol Variable : Type}
    [DecidableEq Variable]
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (source : Input → PeriodicCNF Variable)
    (routes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (atomWord : Input → Variable → List Bool)
    (atomWordInjective : ∀ input,
      Function.Injective (atomWord input))
    (atomWordCompiler : @TM2ComputableInPolyTime
      Input DelimitedBinaryWords.Input InputSymbol DelimitedBinaryWords.Token
      encodeInput DelimitedBinaryWords.finEncoding.encode
      (fun input => retainedOccurrenceGlobalAtomWords
        (source input) (atomWord input)))
    (directionRankCompiler : @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => directionRanks
        (coordinates (source input) (routes input))))
    (radialLengthCompiler : @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => radialLengths
        (coordinates (source input) (routes input)))) :
    @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => retainedOccurrenceGlobalStableTerminalRanks
        (source input) (routes input)) := by
  let atomEquality :=
    retainedOccurrenceGlobalAtomEqualityBitsComputableInPolyTimeOfWords
      encodeInput source atomWord atomWordInjective atomWordCompiler
  let terminalStrictLower :=
    retainedOccurrenceGlobalTerminalStrictLowerBitsComputableInPolyTimeOf
      encodeInput source routes directionRankCompiler radialLengthCompiler
  let terminalEquality :=
    retainedOccurrenceGlobalTerminalEqualityBitsComputableInPolyTimeOf
      encodeInput source routes directionRankCompiler radialLengthCompiler
  exact
    retainedOccurrenceGlobalStableTerminalRanksComputableInPolyTimeOfComponents
      encodeInput source routes atomEquality
      terminalStrictLower terminalEquality

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
