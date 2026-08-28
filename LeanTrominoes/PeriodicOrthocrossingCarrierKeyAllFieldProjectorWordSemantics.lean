/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorIntSemantics

/-! # One-word semantics of the all-field carrier-key projector -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAllFieldProjector

theorem scan_keyWord (key : CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan transition (.nat .route)
        ((CarrierKeyWords.word key).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      (.outside, UnaryFieldEncoderMachine.unaryFields (keyFields (some key))) := by
  rcases key with ⟨routeIndex, segmentIndex, ⟨horizontal, vertical⟩⟩
  unfold CarrierKeyWords.word
  simp only [List.map_append, List.append_assoc]
  rw [FiniteStateTransducer.scan_append, scan_natField_route]
  dsimp
  rw [FiniteStateTransducer.scan_append, scan_natField_segment]
  dsimp
  rw [FiniteStateTransducer.scan_append, scan_intField]
  simp only [nextCoordinate]
  rw [FiniteStateTransducer.scan_append, scan_intField]
  simp [FiniteStateTransducer.scan, transition, nextCoordinate, keyFields,
    UnaryFieldEncoderMachine.unaryFields,
    UnaryFieldEncoderMachine.unaryField, List.append_assoc]

/-- Every guarded carrier-key word becomes exactly its six ordered unary
fields. -/
theorem scan_semanticWord
    (key : Option CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan transition .outside
        (DelimitedBinaryWords.wordTokens
          (CarrierKeyFieldProjector.semanticWord key)) =
      (.outside, UnaryFieldEncoderMachine.unaryFields (keyFields key)) := by
  cases key with
  | none =>
      simp [CarrierKeyFieldProjector.semanticWord,
        DelimitedBinaryWords.wordTokens, FiniteStateTransducer.scan,
        transition, keyFields, UnaryFieldEncoderMachine.unaryFields,
        UnaryFieldEncoderMachine.unaryField, List.replicate_succ]
  | some key =>
      simp only [CarrierKeyFieldProjector.semanticWord,
        DelimitedBinaryWords.wordTokens, List.map_cons,
        FiniteStateTransducer.scan, transition, List.nil_append]
      exact scan_keyWord key

end CarrierKeyAllFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
