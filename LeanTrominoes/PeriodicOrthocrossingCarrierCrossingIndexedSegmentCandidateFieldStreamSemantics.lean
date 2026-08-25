/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceTerminalPipelineSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentCandidateFieldStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingIndexedSegmentFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeStreamSemantics
import LeanTrominoes.TM2PolyTimeInputEncodingTransport
import LeanTrominoes.TM2PolyTimeOutputEncodingTransport
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Semantics of indexed crossing-segment candidate field streams -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingIndexedSegmentCandidateFieldStream

open Computability Turing
open CarrierCrossingIndexedSegmentField
open RouteDescriptorOccurrenceSlotBinaryWords

def terminalValues (descriptors : List RouteDescriptor) : List Nat :=
  (CarrierBoundaryPresenceField.terminalKeys descriptors).map
    (GuardedPresenceFieldProjector.value false)

def crossingValues (field : Field)
    (descriptors : List RouteDescriptor) : List Nat :=
  (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors).flatMap
    fun pair =>
      RouteDescriptorOccurrenceSlotCrossing.crossingIndexedSegmentFields
        field
        (RouteDescriptorOccurrenceSlotPairFieldTags.descriptorSlotPairTokens
          pair)

def values (field : Field) (descriptors : List RouteDescriptor) : List Nat :=
  terminalValues descriptors ++ crossingValues field descriptors

def valuesWithSentinel (field : Field)
    (descriptors : List RouteDescriptor) : List Nat :=
  values field descriptors ++ [0]

@[simp] theorem terminalFields_descriptorWords
    (descriptors : List RouteDescriptor) :
    terminalFields (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        (terminalValues descriptors) := by
  exact CarrierBoundaryPresencePipeline.terminalFields_descriptorWords
    descriptors

@[simp] theorem crossingFields_descriptorWords
    (field : Field) (descriptors : List RouteDescriptor) :
    crossingFields field (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        (crossingValues field descriptors) := by
  unfold crossingFields
  rw [CarrierKeyRecipeStream.crossingTags_descriptorWords,
    CrossingIndexedSegmentFieldStream.emittedFields_encodeDescriptorSlotPairs]
  rfl

@[simp] theorem emittedFields_descriptorWords
    (field : Field) (descriptors : List RouteDescriptor) :
    emittedFields field (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields (values field descriptors) := by
  rw [emittedFields, terminalFields_descriptorWords,
    crossingFields_descriptorWords]
  exact (UnaryFieldEncoderMachine.unaryFields_append _ _).symm

@[simp] theorem emittedFieldsWithSentinel_descriptorWords
    (field : Field) (descriptors : List RouteDescriptor) :
    emittedFieldsWithSentinel field
        (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        (valuesWithSentinel field descriptors) := by
  rw [emittedFieldsWithSentinel, emittedFields_descriptorWords]
  simp [valuesWithSentinel, UnaryFieldEncoderMachine.unaryField]

def valuesWithSentinelComputableInPolyTime (field : Field) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode
          (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields
      (valuesWithSentinel field) := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words
    (emittedFieldsWithSentinelComputableInPolyTime field)
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    (emittedFieldsWithSentinel_descriptorWords field)

end CarrierCrossingIndexedSegmentCandidateFieldStream
end LeanTrominoes.PeriodicOrthocrossing

end
