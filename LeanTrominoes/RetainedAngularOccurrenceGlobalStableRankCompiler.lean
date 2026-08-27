/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankCountCompiler
import LeanTrominoes.RetainedAngularOccurrenceGlobalStableRankPipelineSemantics
import LeanTrominoes.TM2ForkMachineTime
import LeanTrominoes.UnaryAlignedAddTime

/-! # Polynomial compiler boundary for global occurrence stable ranks -/

noncomputable section

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open Computability Turing

/-- Polynomial-time producers for the two comparison squares compose to the
complete square-count stable-rank pipeline. -/
opaque retainedOccurrenceGlobalStableRankPipelineComputableInPolyTimeOf
    {Source InputSymbol Variable : Type}
    [DecidableEq Variable] [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Source → List InputSymbol)
    (source : Source → PeriodicCNF Variable)
    (routes : Source → PositionedPeriodicCNF.IncidenceRoutes)
    (lowerBitsCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input =>
        retainedOccurrenceGlobalStableLowerBits
          (source input) (routes input)))
    (tieBitsCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input =>
        retainedOccurrenceGlobalStableTieBits
          (source input) (routes input))) :
    @TM2ComputableInPolyTime
      Source (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input =>
        retainedOccurrenceGlobalStableRankPipeline
          (source input) (routes input)) := by
  let lowerCounts :=
    retainedOccurrenceGlobalStableLowerCountsComputableInPolyTimeOf
      encodeInput source routes lowerBitsCompiler
  let tieCounts :=
    retainedOccurrenceGlobalStableTieCountsComputableInPolyTimeOf
      encodeInput source routes tieBitsCompiler
  let paired := TM2ForkMachine.computableInPolyTime lowerCounts tieCounts
  let additionInputCompiler : @TM2ComputableInPolyTime
      Source UnaryAlignedAddMachine.Input InputSymbol
      UnaryAlignedAddMachine.InputSymbol encodeInput
      UnaryAlignedAddMachine.encode
      (fun input =>
        retainedOccurrenceGlobalStableRankAdditionInput
          (source input) (routes input)) :=
    TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq paired
      (fun input => by
        simp only [UnaryAlignedAddMachine.encode,
          retainedOccurrenceGlobalStableRankAdditionInput])
  let added := TM2CompositionMachine.computableInPolyTime
    additionInputCompiler UnaryAlignedAddMachine.computableInPolyTime
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (encodeOutput₂ := UnaryFieldEncoderMachine.unaryFields)
    (function₂ := fun input =>
      retainedOccurrenceGlobalStableRankPipeline
        (source input) (routes input)) added (fun input => by
      rfl)

/-- Consequently, once the two comparison squares are compiled, the exact
semantic global stable-terminal-rank stream is polynomial-time computable. -/
noncomputable def
    retainedOccurrenceGlobalStableTerminalRanksComputableInPolyTimeOf
    {Source InputSymbol Variable : Type}
    [DecidableEq Variable] [Fintype InputSymbol] [Inhabited InputSymbol]
    (encodeInput : Source → List InputSymbol)
    (source : Source → PeriodicCNF Variable)
    (routes : Source → PositionedPeriodicCNF.IncidenceRoutes)
    (lowerBitsCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input =>
        retainedOccurrenceGlobalStableLowerBits
          (source input) (routes input)))
    (tieBitsCompiler : @TM2ComputableInPolyTime
      Source (List Bool) InputSymbol Bool encodeInput id
      (fun input =>
        retainedOccurrenceGlobalStableTieBits
          (source input) (routes input))) :
    @TM2ComputableInPolyTime
      Source (List Nat) InputSymbol UnaryFieldEncoderMachine.Symbol
      encodeInput UnaryFieldEncoderMachine.unaryFields
      (fun input =>
        retainedOccurrenceGlobalStableTerminalRanks
          (source input) (routes input)) :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    (retainedOccurrenceGlobalStableRankPipelineComputableInPolyTimeOf
      encodeInput source routes lowerBitsCompiler tieBitsCompiler)
    (fun input => by
      rw [retainedOccurrenceGlobalStableRankPipeline_eq])

end PeriodicEightOccurrenceSplit
end LeanTrominoes

end
