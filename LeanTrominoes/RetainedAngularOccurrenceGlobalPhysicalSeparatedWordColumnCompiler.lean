/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalSeparatedWordColumnCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Stable ranks from physical separating-word token streams -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing
open TerminalCoordinateComponents

/-- A physical delimited-word token producer may be used directly by the
separating-word stable-rank compiler once its output is identified with the
semantic occurrence-word column.  This keeps large source-specific token
compilers behind their existing opaque machine boundaries. -/
noncomputable def
    retainedOccurrenceGlobalStableTerminalRanksComputableInPolyTimeOfPhysicalSeparatingWordColumns
    {Input InputSymbol Variable : Type}
    [DecidableEq Variable]
    [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Input → List InputSymbol)
    (source : Input → PeriodicCNF Variable)
    (routes : Input → PositionedPeriodicCNF.IncidenceRoutes)
    (atomWord : Input → Variable → List Bool)
    (separates : ∀ input,
      OccurrenceAtomWordsSeparate (source input) (atomWord input))
    (physicalAtomWordTokens :
      Input → List DelimitedBinaryWords.Token)
    (physicalAtomWordTokenCompiler : @TM2ComputableInPolyTime
      Input (List DelimitedBinaryWords.Token)
      InputSymbol DelimitedBinaryWords.Token
      encodeInput id physicalAtomWordTokens)
    (physicalAtomWordTokensEq : ∀ input,
      physicalAtomWordTokens input =
        DelimitedBinaryWords.encode
          (retainedOccurrenceGlobalAtomWords
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
  let atomWordCompiler : @TM2ComputableInPolyTime
      Input DelimitedBinaryWords.Input
      InputSymbol DelimitedBinaryWords.Token
      encodeInput DelimitedBinaryWords.finEncoding.encode
      (fun input => retainedOccurrenceGlobalAtomWords
        (source input) (atomWord input)) :=
    TM2PolyTimeOutputEncodingTransport.of_identity_output_eq
      physicalAtomWordTokenCompiler physicalAtomWordTokensEq
  exact
    retainedOccurrenceGlobalStableTerminalRanksComputableInPolyTimeOfSeparatingWordColumns
      encodeInput source routes atomWord separates atomWordCompiler
      directionRankCompiler radialLengthCompiler

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
