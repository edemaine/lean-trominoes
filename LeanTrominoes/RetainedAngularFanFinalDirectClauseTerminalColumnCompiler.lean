/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteBlockTransducer
import LeanTrominoes.RetainedAngularFanFinalDirectClauseTerminalColumn
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderMachine

/-! # Compiling terminal columns from final direct-clause queries -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit
namespace RetainedFinalDirectTerminalColumns

open Computability Turing

/-- Fixed unary direction block carried by one finite clause query. -/
def directionBlock
    (query : RetainedFinalCopiedClauseQuery) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields
    ((retainedFinalDirectClauseTerminalCoordinates query).map Prod.fst)

/-- Fixed unary radial block carried by one finite clause query. -/
def radialBlock
    (query : RetainedFinalCopiedClauseQuery) :
    List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields
    ((retainedFinalDirectClauseTerminalCoordinates query).map Prod.snd)

/-- Physical direction-token stream of a finite query list. -/
def directionTokens
    (queries : List RetainedFinalCopiedClauseQuery) :
    List UnaryFieldEncoderMachine.Symbol :=
  queries.flatMap directionBlock

/-- Physical radial-token stream of a finite query list. -/
def radialTokens
    (queries : List RetainedFinalCopiedClauseQuery) :
    List UnaryFieldEncoderMachine.Symbol :=
  queries.flatMap radialBlock

theorem directionTokens_eq_unaryFields
    (queries : List RetainedFinalCopiedClauseQuery) :
    directionTokens queries =
      UnaryFieldEncoderMachine.unaryFields
        (retainedFinalDirectTerminalDirectionRanks queries) := by
  unfold directionTokens directionBlock
    retainedFinalDirectTerminalDirectionRanks
    retainedFinalDirectTerminalCoordinates
    UnaryFieldEncoderMachine.unaryFields
  rw [List.map_flatMap, List.flatMap_assoc]

theorem radialTokens_eq_unaryFields
    (queries : List RetainedFinalCopiedClauseQuery) :
    radialTokens queries =
      UnaryFieldEncoderMachine.unaryFields
        (retainedFinalDirectTerminalRadialLengths queries) := by
  unfold radialTokens radialBlock
    retainedFinalDirectTerminalRadialLengths
    retainedFinalDirectTerminalCoordinates
    UnaryFieldEncoderMachine.unaryFields
  rw [List.map_flatMap, List.flatMap_assoc]

/-- Finite direct clause queries compile to their exact angular-rank column. -/
noncomputable def directionRanksComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      retainedFinalDirectTerminalDirectionRanks := by
  let physical : TM2ComputableInPolyTime id id directionTokens :=
    FiniteBlockTransducer.computableInPolyTime directionBlock
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := UnaryFieldEncoderMachine.unaryFields)
    (function₂ := retainedFinalDirectTerminalDirectionRanks)
    physical directionTokens_eq_unaryFields

/-- Finite direct clause queries compile to their exact radial-length column. -/
noncomputable def radialLengthsComputableInPolyTime :
    TM2ComputableInPolyTime id UnaryFieldEncoderMachine.unaryFields
      retainedFinalDirectTerminalRadialLengths := by
  let physical : TM2ComputableInPolyTime id id radialTokens :=
    FiniteBlockTransducer.computableInPolyTime radialBlock
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := UnaryFieldEncoderMachine.unaryFields)
    (function₂ := retainedFinalDirectTerminalRadialLengths)
    physical radialTokens_eq_unaryFields

/-- Any exact finite clause-query producer composes with the fixed direction
projection. -/
noncomputable def directionRanksComputableInPolyTimeOf
    {Source InputSymbol : Type}
    (encodeInput : Source → List InputSymbol)
    (queries : Source → List RetainedFinalCopiedClauseQuery)
    (compiler : @TM2ComputableInPolyTime
      Source (List RetainedFinalCopiedClauseQuery)
      InputSymbol RetainedFinalCopiedClauseQuery encodeInput id queries) :
    @TM2ComputableInPolyTime
      Source (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => retainedFinalDirectTerminalDirectionRanks
        (queries input)) :=
  TM2CompositionMachine.computableInPolyTime compiler
    directionRanksComputableInPolyTime

/-- Any exact finite clause-query producer composes with the fixed radial
projection. -/
noncomputable def radialLengthsComputableInPolyTimeOf
    {Source InputSymbol : Type}
    (encodeInput : Source → List InputSymbol)
    (queries : Source → List RetainedFinalCopiedClauseQuery)
    (compiler : @TM2ComputableInPolyTime
      Source (List RetainedFinalCopiedClauseQuery)
      InputSymbol RetainedFinalCopiedClauseQuery encodeInput id queries) :
    @TM2ComputableInPolyTime
      Source (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input => retainedFinalDirectTerminalRadialLengths
        (queries input)) :=
  TM2CompositionMachine.computableInPolyTime compiler
    radialLengthsComputableInPolyTime

end RetainedFinalDirectTerminalColumns
end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
