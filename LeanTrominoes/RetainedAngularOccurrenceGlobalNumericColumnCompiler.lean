/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalAtomCodeSemantics
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankComponentCompiler
import LeanTrominoes.RetainedAngularOccurrenceTerminalCoordinateComponentCompiler

/-! # Stable-rank compilation from three numeric occurrence columns -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing
open TerminalCoordinateComponents

/-- An exact unary stream of injective atom codes compiles the semantic
same-atom comparison square. -/
noncomputable def
    retainedOccurrenceGlobalAtomEqualityBitsComputableInPolyTimeOfCodes
    {Input InputSymbol Variable : Type}
    [DecidableEq Variable]
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (source : Input → PeriodicCNF Variable)
    (atomCode : Input → Variable → Nat)
    (atomCodeInjective : ∀ input,
      Function.Injective (atomCode input))
    (atomCodeCompiler : @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => retainedOccurrenceGlobalAtomCodes
        (source input) (atomCode input))) :
    @TM2ComputableInPolyTime
      Input (List Bool) InputSymbol Bool encodeInput id
      (fun input => retainedOccurrenceGlobalAtomEqualityBits
        (source input)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (UnaryFieldEqualityRows.equalityBitsComputableInPolyTime
      encodeInput
      (fun input => retainedOccurrenceGlobalAtomCodes
        (source input) (atomCode input))
      atomCodeCompiler)
    (fun input =>
      (retainedOccurrenceGlobalAtomEqualityBits_eq_codes
        (source input) (atomCode input)
        (atomCodeInjective input)).symm)

/-- Exact unary atom IDs, terminal direction ranks, and terminal radial
lengths suffice to compile the complete semantic global stable-rank stream. -/
noncomputable def
    retainedOccurrenceGlobalStableTerminalRanksComputableInPolyTimeOfNumericColumns
    {Input InputSymbol Variable : Type}
    [DecidableEq Variable]
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (source : Input → PeriodicCNF Variable)
    (routes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (atomCode : Input → Variable → Nat)
    (atomCodeInjective : ∀ input,
      Function.Injective (atomCode input))
    (atomCodeCompiler : @TM2ComputableInPolyTime
      Input (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => retainedOccurrenceGlobalAtomCodes
        (source input) (atomCode input)))
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
    retainedOccurrenceGlobalAtomEqualityBitsComputableInPolyTimeOfCodes
      encodeInput source atomCode atomCodeInjective atomCodeCompiler
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
