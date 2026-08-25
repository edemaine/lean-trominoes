/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierBoundaryPresenceTerminalPipelineSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldPipelineData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorNatStreamSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorSignedWordCorrect
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyPairSelectionSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyCrossingTokenSemantics
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyCandidateStreamPairSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Semantics of source-key crossing-record field pipelines -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierCrossingRecordSourceField

theorem keyFieldWordCorrect (field : Field) :
    CarrierKeyFieldProjector.WordCorrect (keyField field) := by
  cases field <;>
    first
    | exact CarrierKeyFieldProjector.wordCorrect_route
    | exact CarrierKeyFieldProjector.wordCorrect_horizontalPositive
    | exact CarrierKeyFieldProjector.wordCorrect_horizontalNegative
    | exact CarrierKeyFieldProjector.wordCorrect_verticalPositive
    | exact CarrierKeyFieldProjector.wordCorrect_verticalNegative
    | exact CarrierKeyFieldProjector.wordCorrect_segment

end CarrierCrossingRecordSourceField

namespace CarrierCrossingRecordSourceFieldPipeline

open CarrierCrossingRecordSourceField

theorem selectedCrossingTokens_descriptorWords
    (field : Field) (descriptors : List RouteDescriptor) :
    selectedCrossingTokens field
        (RouteDescriptorBinaryWords.words descriptors) =
      DelimitedBinaryWords.encode
        ⟨(crossingKeys field descriptors).map
          CarrierKeyFieldProjector.semanticWord⟩ := by
  unfold selectedCrossingTokens crossingKeys
  rw [CarrierSourceKeyComponentStream.crossingTokens_descriptorWords]
  rw [← RouteDescriptorOccurrenceSlotCrossing.componentWords_paddedCrossingCarrierNodeCandidateStream]
  rw [DelimitedBinaryWordPairSelector.tokens_encode_componentWords]
  rw [CarrierNodeSourceKeyCandidateWords.selectedWords_componentPairs]
  simp [List.map_map, Function.comp_def]

theorem crossingFields_descriptorWords
    (field : Field) (descriptors : List RouteDescriptor) :
    crossingFields field
        (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        ((crossingKeys field descriptors).map
          (CarrierKeyFieldProjector.value (keyField field)) ++ [0]) := by
  unfold crossingFields
  rw [selectedCrossingTokens_descriptorWords]
  exact CarrierKeyFieldProjector.output_encode_semanticWords
    (keyField field) (keyFieldWordCorrect field)
      (crossingKeys field descriptors)

theorem fields_descriptorWords
    (field : Field) (descriptors : List RouteDescriptor) :
    fields field (RouteDescriptorBinaryWords.words descriptors) =
      UnaryFieldEncoderMachine.unaryFields
        (alignedValuesWithSentinel field descriptors) := by
  unfold fields alignedValuesWithSentinel
  rw [CarrierBoundaryPresencePipeline.terminalFields_descriptorWords,
    crossingFields_descriptorWords]
  unfold CarrierBoundaryPresenceField.terminalKeys terminalKeys
  rw [List.append_assoc]
  exact (UnaryFieldEncoderMachine.unaryFields_append _ _).symm

end CarrierCrossingRecordSourceFieldPipeline
end LeanTrominoes.PeriodicOrthocrossing

end
