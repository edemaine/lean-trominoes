/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierCanonicalCrossingCoordinateCandidateSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointCandidateFieldStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingPointCandidateFieldLength
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceTerminalCandidateSemantics

/-! # Canonical crossing columns in the complete padded carrier stream -/

noncomputable section
namespace LeanTrominoes.PeriodicOrthocrossing.CarrierCanonicalCrossingCoordinates
open Computability Turing CarrierCrossingPointField
open RouteDescriptorOccurrenceSlotCrossing RouteDescriptorOccurrenceSlotBinaryWords
open RouteDescriptorOccurrenceSlotPairFieldTags
open PaddedSupportedLastRepresentativeEqualityRows

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ := ⟨DelimitedBinaryWords.Token.wordStart⟩

def crossingValues (offset : CrossingSide → Cell) (field : Field)
    (descriptors : List RouteDescriptor) : List Nat :=
  (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors).flatMap fun pair =>
    fields offset field (descriptorSlotPairTokens pair)

def values (offset : CrossingSide → Cell) (field : Field)
    (descriptors : List RouteDescriptor) : List Nat :=
  CarrierCrossingPointCandidateFieldStream.terminalValues descriptors ++ crossingValues offset field descriptors

def valuesWithSentinel (offset : CrossingSide → Cell) (field : Field)
    (descriptors : List RouteDescriptor) : List Nat := values offset field descriptors ++ [0]

private def blockFields (offset : CrossingSide → Cell) (field : Field)
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) : List UnaryFieldEncoderMachine.Symbol :=
  UnaryFieldEncoderMachine.unaryFields (fields offset field tokens)

private opaque encodedOutputCompiler
    {Domain InputSymbol : Type}
    (encodeInput : Domain → List InputSymbol)
    (function : Domain → List Nat)
    (compiler : TM2ComputableInPolyTime encodeInput
      UnaryFieldEncoderMachine.unaryFields function) :
    TM2ComputableInPolyTime encodeInput id
      (fun input => UnaryFieldEncoderMachine.unaryFields (function input)) := by
  exact @TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq
    Domain (List Nat) (List UnaryFieldEncoderMachine.Symbol)
    InputSymbol UnaryFieldEncoderMachine.Symbol encodeInput
    UnaryFieldEncoderMachine.unaryFields id function
    (fun input => UnaryFieldEncoderMachine.unaryFields (function input))
    compiler (fun _ => rfl)

private noncomputable def blockFieldsComputableInPolyTime (offset : CrossingSide → Cell) (field : Field) :
    TM2ComputableInPolyTime id id (blockFields offset field) :=
  encodedOutputCompiler id (fields offset field) (fieldsComputableInPolyTime offset field)

private def crossingFields (offset : CrossingSide → Cell) (field : Field)
    (input : DelimitedBinaryWords.Input) : List UnaryFieldEncoderMachine.Symbol :=
  TM2EndDelimitedBlockMap.mappedOutput isPairEnd (blockFields offset field)
    (CarrierKeyRecipeStream.crossingTags input)

private noncomputable def crossingFieldsComputableInPolyTime (offset : CrossingSide → Cell) (field : Field) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id (crossingFields offset field) := by
  unfold crossingFields
  exact TM2CompositionMachine.computableInPolyTime
    CarrierKeyRecipeStream.crossingTagsComputableInPolyTime
    (TM2EndDelimitedBlockMap.computableInPolyTime (blockFieldsComputableInPolyTime offset field) isPairEnd)

private theorem crossingFields_descriptorWords (offset : CrossingSide → Cell) (field : Field)
    (descriptors : List RouteDescriptor) :
    crossingFields offset field (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields (crossingValues offset field descriptors) := by
  unfold crossingFields crossingValues
  rw [CarrierKeyRecipeStream.crossingTags_descriptorWords, mappedOutput_encodeDescriptorSlotPairs]
  unfold blockFields
  rw [← List.flatMap_map]
  exact (UnaryFieldEncoderMachine.unaryFields_flatten _).symm

private def emittedFieldsWithSentinel (offset : CrossingSide → Cell) (field : Field)
    (input : DelimitedBinaryWords.Input) : List UnaryFieldEncoderMachine.Symbol :=
  (CarrierCrossingPointCandidateFieldStream.terminalFields input ++ crossingFields offset field input) ++ [.delimiter]

private noncomputable def emittedFieldsWithSentinelComputableInPolyTime (offset : CrossingSide → Cell) (field : Field) :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id (emittedFieldsWithSentinel offset field) := by
  let joined := TM2ListAppend.computableInPolyTime
    CarrierCrossingPointCandidateFieldStream.terminalFieldsComputableInPolyTime
    (crossingFieldsComputableInPolyTime offset field)
  let compiled := TM2CompositionMachine.computableInPolyTime joined
    (TM2ListAppend.appendFixedComputableInPolyTime [UnaryFieldEncoderMachine.Symbol.delimiter])
  unfold emittedFieldsWithSentinel
  exact compiled

private theorem emittedFieldsWithSentinel_descriptorWords (offset : CrossingSide → Cell) (field : Field)
    (descriptors : List RouteDescriptor) :
    emittedFieldsWithSentinel offset field (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields (valuesWithSentinel offset field descriptors) := by
  unfold emittedFieldsWithSentinel
  rw [CarrierCrossingPointCandidateFieldStream.terminalFields_descriptorWords, crossingFields_descriptorWords]
  simp [valuesWithSentinel, values, UnaryFieldEncoderMachine.unaryField]

noncomputable def valuesWithSentinelComputableInPolyTime (offset : CrossingSide → Cell) (field : Field) :
    TM2ComputableInPolyTime
      (fun descriptors : List RouteDescriptor =>
        DelimitedBinaryWords.encode (RouteDescriptorBinaryWords.words descriptors))
      UnaryFieldEncoderMachine.unaryFields (valuesWithSentinel offset field) := by
  let prepared := TM2PolyTimeInputEncodingTransport.of_prepare
    RouteDescriptorBinaryWords.words (emittedFieldsWithSentinelComputableInPolyTime offset field)
    (fun _ => rfl) (fun _ => rfl)
  exact TM2PolyTimeOutputEncodingTransport.of_encoded_output_eq prepared
    (emittedFieldsWithSentinel_descriptorWords offset field)

private theorem occurrenceBlock_length (offset : CrossingSide → Cell) (field : Field)
    (occurrences : RouteDescriptorPairAffine.Occurrence × RouteDescriptorPairAffine.Occurrence) :
    (occurrenceBlock offset field occurrences).length =
      (RouteDescriptorPairAffine.occurrencePairCrossingPointExpressionBlock field occurrences).length := by
  unfold occurrenceBlock RouteDescriptorPairAffine.occurrencePairCrossingPointExpressionBlock
  induction carrierCrossingRetentionShifts with
  | nil => rfl
  | cons shift shifts induction =>
      simp only [List.flatMap_cons, List.length_append]
      exact congrArg (fun length : Nat => 4 + length) induction

private theorem expressions_length (offset : CrossingSide → Cell) (field : Field) :
    (expressions offset field).length = (crossingPointExpressions field).length := by
  unfold expressions crossingPointExpressions crossingPointExpressionBlocks
  induction crossingSlots with
  | nil => rfl
  | cons slot slots induction =>
      simp only [List.map_cons, List.flatten_cons, List.length_append]
      exact congrArg₂ (fun first second : Nat => first + second)
        (occurrenceBlock_length offset field slot.occurrences) induction

private theorem fields_length (offset : CrossingSide → Cell) (field : Field)
    (pair : TaggedDescriptor × TaggedDescriptor) :
    (fields offset field (descriptorSlotPairTokens pair)).length =
      (crossingPointFields field (descriptorSlotPairTokens pair)).length := by
  rw [fields_descriptorSlotPairTokens, crossingPointFields_descriptorSlotPairTokens,
    List.length_map, List.length_map]
  exact expressions_length offset field

private theorem flatMap_length_congr {Index First Second : Type}
    (indices : List Index) (first : Index → List First) (second : Index → List Second)
    (lengthEq : ∀ index, (first index).length = (second index).length) :
    (indices.flatMap first).length = (indices.flatMap second).length := by
  induction indices with
  | nil => rfl
  | cons index indices induction =>
      simp only [List.flatMap_cons, List.length_append]
      exact congrArg₂ (fun a b : Nat => a + b) (lengthEq index) induction

private theorem crossingValues_length (offset : CrossingSide → Cell) (field : Field)
    (descriptors : List RouteDescriptor) :
    (crossingValues offset field descriptors).length =
      (CarrierCrossingPointCandidateFieldStream.crossingValues field descriptors).length := by
  unfold crossingValues CarrierCrossingPointCandidateFieldStream.crossingValues
  exact flatMap_length_congr
    (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)
    (fun pair => fields offset field (descriptorSlotPairTokens pair))
    (fun pair => crossingPointFields field (descriptorSlotPairTokens pair))
    (fields_length offset field)

theorem valuesWithSentinel_length (offset : CrossingSide → Cell) (field : Field)
    (descriptors : List RouteDescriptor) :
    (valuesWithSentinel offset field descriptors).length =
      (paddedCarrierSourceKeyCandidateStream descriptors).length + 1 := by
  calc
    (valuesWithSentinel offset field descriptors).length =
        (CarrierCrossingPointCandidateFieldStream.valuesWithSentinel field descriptors).length := by
      change ((CarrierCrossingPointCandidateFieldStream.terminalValues descriptors ++
        crossingValues offset field descriptors) ++ [0]).length =
        ((CarrierCrossingPointCandidateFieldStream.terminalValues descriptors ++
          CarrierCrossingPointCandidateFieldStream.crossingValues field descriptors) ++ [0]).length
      simp only [List.length_append, List.length_singleton]
      exact congrArg (fun length =>
        (CarrierCrossingPointCandidateFieldStream.terminalValues descriptors).length + length + 1)
        (crossingValues_length offset field descriptors)
    _ = _ := CarrierCrossingPointCandidateFieldStream.valuesWithSentinel_length_sourceKeyCandidates field descriptors

/-- All active values agree with their physical node at the shared period. -/
theorem values_forall₂ (offset : CrossingSide → Cell) (field : Field) (period : Nat)
    (descriptors : List RouteDescriptor)
    (periodEq : ∀ descriptor ∈ descriptors, descriptor.gridSize = period) :
    List.Forall₂
      (fun candidate value => ∀ node, candidate.value = some node → value = nodeValue offset field period node)
      (paddedCarrierNodeCandidateStream descriptors) (values offset field descriptors) := by
  unfold paddedCarrierNodeCandidateStream values crossingValues
  apply List.Forall₂.append
  · have terminalAligned := CarrierCrossingPointCandidateFieldStream.terminalValues_forall₂ field descriptors
    apply List.forall₂_iff_zip.mpr
    refine ⟨terminalAligned.length_eq, ?_⟩
    intro candidate value member node nodeEq
    have original := List.forall₂_zip terminalAligned member node nodeEq
    have candidateMap := List.map_inj_left.mp
      (RouteDescriptorPairAffine.map_boundaryPresence_paddedTerminalCarrierNodeCandidateStream descriptors)
      candidate (List.of_mem_zip member).1
    have presenceZero := congrArg Candidate.value candidateMap
    simp only [Candidate.mapValue, nodeEq, Option.map_some, Option.some.injEq] at presenceZero
    cases node with
    | terminal terminal => simpa [nodeValue, nodePoint, pointValue,
        CarrierCrossingPointField.nodeValue] using original
    | boundary boundary => simp [CarrierBoundaryPresenceField.nodeValue] at presenceZero
  · exact stream_forall₂ offset field period descriptors periodEq

end LeanTrominoes.PeriodicOrthocrossing.CarrierCanonicalCrossingCoordinates
end
