/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterCompiledOutput
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamCompiler
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport

/-! # Semantic delimited-word output of the complete recipe stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeStream

open Computability Turing

def terminalOutput
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    DelimitedBinaryWords.Input :=
  ⟨(TM2EndDelimitedBlockMap.blocks
      RouteDescriptorPairFieldTags.isPairEnd tokens).flatMap fun block =>
    (CarrierKeyRecipeEmitterMachine.compiledOutput
      TerminalCarrierKeyRecipeEmitter.recipes
      (TerminalCarrierKeyRecipeEmitter.preparedInput block)).words⟩

def crossingOutput
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    DelimitedBinaryWords.Input :=
  ⟨(TM2EndDelimitedBlockMap.blocks
      RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd tokens).flatMap
    fun block =>
      (CarrierKeyRecipeEmitterMachine.compiledOutput
        CrossingCarrierKeyRecipeEmitter.recipes
        (CrossingCarrierKeyRecipeEmitter.preparedInput block)).words⟩

def output (input : DelimitedBinaryWords.Input) :
    DelimitedBinaryWords.Input :=
  ⟨(terminalOutput (terminalTags input)).words ++
    (crossingOutput (crossingTags input)).words⟩

theorem terminalStream_eq_encode
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    TerminalCarrierKeyRecipeStream.emittedStream tokens =
      DelimitedBinaryWords.encode (terminalOutput tokens) := by
  unfold TerminalCarrierKeyRecipeStream.emittedStream
    TM2EndDelimitedBlockMap.mappedOutput terminalOutput
    TerminalCarrierKeyRecipeEmitter.emittedTokens
  simp only [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_encode_compiledOutput]
  unfold DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

theorem crossingStream_eq_encode
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    CrossingCarrierKeyRecipeStream.emittedStream tokens =
      DelimitedBinaryWords.encode (crossingOutput tokens) := by
  unfold CrossingCarrierKeyRecipeStream.emittedStream
    TM2EndDelimitedBlockMap.mappedOutput crossingOutput
    CrossingCarrierKeyRecipeEmitter.emittedTokens
  simp only [CarrierKeyRecipeEmitterMachine.compiledTokens_eq_encode_compiledOutput]
  unfold DelimitedBinaryWords.encode
  rw [List.flatMap_assoc]

@[simp] theorem emittedTokens_eq_encode_output
    (input : DelimitedBinaryWords.Input) :
    emittedTokens input = DelimitedBinaryWords.encode (output input) := by
  unfold emittedTokens terminalTokens crossingTokens output
  rw [terminalStream_eq_encode, crossingStream_eq_encode]
  simp [DelimitedBinaryWords.encode, List.flatMap_append]

/-- The complete recipe-stream compiler can be consumed through the semantic
delimiter encoding on every input, including malformed word streams. -/
noncomputable def outputComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode
      DelimitedBinaryWords.finEncoding.encode output :=
  TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    emittedTokensComputableInPolyTime emittedTokens_eq_encode_output

end CarrierKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing

end
