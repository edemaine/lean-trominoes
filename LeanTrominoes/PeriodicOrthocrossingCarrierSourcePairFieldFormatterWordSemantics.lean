/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourcePairFieldFormatterIntSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # One-word semantics of the source-pair field formatter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourcePairFieldFormatter

theorem scan_firstKey (key : CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan transition .begin
        (UnaryFieldEncoderMachine.unaryFields
          (CarrierKeyAllFieldProjector.keyFields (some key))) =
      (.nat .second .route,
        [.wordStart, .bit true] ++
          (CarrierKeyWords.word key).map DelimitedBinaryWords.Token.bit ++
          [.bit true]) := by
  rcases key with ⟨routeIndex, segmentIndex, ⟨horizontal, vertical⟩⟩
  simp only [CarrierKeyAllFieldProjector.keyFields,
    UnaryFieldEncoderMachine.unaryFields_cons,
    UnaryFieldEncoderMachine.unaryFields_nil, List.append_nil]
  rw [FiniteStateTransducer.scan_append, scan_beginRouteField]
  dsimp
  rw [FiniteStateTransducer.scan_append, scan_segmentField]
  dsimp
  rw [← List.append_assoc, FiniteStateTransducer.scan_append, scan_intFields]
  simp only [afterCoordinate, coordinateSuffix, List.append_nil]
  rw [scan_intFields]
  simp [afterCoordinate, coordinateSuffix, CarrierKeyWords.word,
    List.map_append, List.append_assoc]

theorem scan_secondKey (key : CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan transition (.nat .second .route)
        (UnaryFieldEncoderMachine.unaryFields
          (CarrierKeyAllFieldProjector.keyFields (some key))) =
      (.begin,
        (CarrierKeyWords.word key).map DelimitedBinaryWords.Token.bit ++
          [.wordEnd]) := by
  rcases key with ⟨routeIndex, segmentIndex, ⟨horizontal, vertical⟩⟩
  simp only [CarrierKeyAllFieldProjector.keyFields,
    UnaryFieldEncoderMachine.unaryFields_cons,
    UnaryFieldEncoderMachine.unaryFields_nil, List.append_nil]
  rw [FiniteStateTransducer.scan_append, scan_routeField]
  dsimp
  rw [FiniteStateTransducer.scan_append, scan_segmentField]
  dsimp
  rw [← List.append_assoc, FiniteStateTransducer.scan_append, scan_intFields]
  simp only [afterCoordinate, coordinateSuffix, List.append_nil]
  rw [scan_intFields]
  simp [afterCoordinate, coordinateSuffix, CarrierKeyWords.word,
    List.map_append, List.append_assoc]

/-- Twelve canonical source-pair fields reconstruct one complete guarded
source-pair word and return to the record boundary. -/
theorem scan_sourcePair
    (sourcePair : CarrierNodeSourceKeys.SourceKeyPair) :
    FiniteStateTransducer.scan transition .begin
        (UnaryFieldEncoderMachine.unaryFields
          (CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup.sourcePairFields
            (some sourcePair))) =
      (.begin,
        DelimitedBinaryWords.wordTokens
          (true :: CarrierNodeSourceKeys.word sourcePair)) := by
  unfold CanonicalCrossingShiftLeftSourceKeyRepresentativeFieldLookup.sourcePairFields
  rw [UnaryFieldEncoderMachine.unaryFields_append,
    FiniteStateTransducer.scan_append, scan_firstKey]
  dsimp
  rw [scan_secondKey]
  simp [CarrierNodeSourceKeys.word, DelimitedBinaryWords.wordTokens,
    List.map_append, List.append_assoc]

end CarrierSourcePairFieldFormatter
end LeanTrominoes.PeriodicOrthocrossing
