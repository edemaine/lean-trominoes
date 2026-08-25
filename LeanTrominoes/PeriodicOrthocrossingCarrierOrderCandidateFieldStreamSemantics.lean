/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineCrossingFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderCandidateFieldStreamCompiler
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Semantics of the carrier order-coordinate candidate-field stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierOrderCandidateFieldStream

open Computability Turing
open RouteDescriptorOccurrenceSlotBinaryWords

def values (keepPositive : Bool)
    (descriptors : List RouteDescriptor) : List Nat :=
  ((descriptors ×ˢ descriptors).flatMap fun pair =>
    RouteDescriptorPairAffine.terminalDirectionalOrderFields keepPositive
      (RouteDescriptorPairFieldTags.descriptorPairTokens pair)) ++
  ((taggedDescriptors descriptors ×ˢ
    taggedDescriptors descriptors).flatMap fun pair =>
      RouteDescriptorOccurrenceSlotCrossing.crossingOrderFields keepPositive
        (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
          pair))

def valuesWithSentinel (keepPositive : Bool)
    (descriptors : List RouteDescriptor) : List Nat :=
  values keepPositive descriptors ++ [0]

@[simp] theorem terminalFields_descriptorWords
    (keepPositive : Bool) (descriptors : List RouteDescriptor) :
    terminalFields keepPositive
        (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        ((descriptors ×ˢ descriptors).flatMap fun pair =>
          RouteDescriptorPairAffine.terminalDirectionalOrderFields
            keepPositive
            (RouteDescriptorPairFieldTags.descriptorPairTokens pair)) := by
  unfold terminalFields
  rw [CarrierKeyRecipeStream.terminalTags_descriptorWords,
    TerminalDirectionalOrderFieldStream.emittedFields_encodeDescriptorPairs]

@[simp] theorem crossingFields_descriptorWords
    (keepPositive : Bool) (descriptors : List RouteDescriptor) :
    crossingFields keepPositive
        (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        ((taggedDescriptors descriptors ×ˢ
          taggedDescriptors descriptors).flatMap fun pair =>
          RouteDescriptorOccurrenceSlotCrossing.crossingOrderFields
            keepPositive
            (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
              pair)) := by
  unfold crossingFields
  rw [CarrierKeyRecipeStream.crossingTags_descriptorWords,
    CrossingOrderFieldStream.emittedFields_encodeDescriptorSlotPairs]

@[simp] theorem emittedFields_descriptorWords
    (keepPositive : Bool) (descriptors : List RouteDescriptor) :
    emittedFields keepPositive
        (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        (values keepPositive descriptors) := by
  rw [emittedFields, terminalFields_descriptorWords,
    crossingFields_descriptorWords]
  simp only [values, UnaryFieldEncoderMachine.unaryFields_append]

@[simp] theorem emittedFieldsWithSentinel_descriptorWords
    (keepPositive : Bool) (descriptors : List RouteDescriptor) :
    emittedFieldsWithSentinel keepPositive
        (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        (valuesWithSentinel keepPositive descriptors) := by
  rw [emittedFieldsWithSentinel, emittedFields_descriptorWords]
  simp [valuesWithSentinel, UnaryFieldEncoderMachine.unaryField]

def valuesWithSentinelComputableInPolyTime (keepPositive : Bool) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (valuesWithSentinel keepPositive) := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words
    (emittedFieldsWithSentinelComputableInPolyTime keepPositive)
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    (emittedFieldsWithSentinel_descriptorWords keepPositive)

end CarrierOrderCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
