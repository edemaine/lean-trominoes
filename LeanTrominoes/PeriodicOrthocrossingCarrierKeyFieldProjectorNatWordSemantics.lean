/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorNatSemantics

/-! # Guarded-word semantics of natural carrier-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

theorem scan_semanticWord_route
    (key : Option CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan (transition .route) .outside
        (DelimitedBinaryWords.wordTokens (semanticWord key)) =
      (.outside, UnaryFieldEncoderMachine.unaryField (value .route key)) := by
  cases key with
  | none => rfl
  | some key =>
      rcases key with ⟨routeIndex, segmentIndex,
        ⟨horizontal, vertical⟩⟩
      simp only [semanticWord, DelimitedBinaryWords.wordTokens,
        CarrierKeyWords.word, List.map_cons, value, keyValue]
      rw [scan_outside_wordStart]
      simp only [List.cons_append]
      rw [scan_guard_true]
      simpa only [List.append_assoc] using
        scan_routeNatField routeIndex
          (CarrierKeyWords.natField segmentIndex ++
            CarrierKeyWords.intField horizontal ++
            CarrierKeyWords.intField vertical)

theorem scan_semanticWord_segment
    (key : Option CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan (transition .segment) .outside
        (DelimitedBinaryWords.wordTokens (semanticWord key)) =
      (.outside,
        UnaryFieldEncoderMachine.unaryField (value .segment key)) := by
  cases key with
  | none => rfl
  | some key =>
      rcases key with ⟨routeIndex, segmentIndex,
        ⟨horizontal, vertical⟩⟩
      simp only [semanticWord, DelimitedBinaryWords.wordTokens,
        CarrierKeyWords.word, List.map_cons, value, keyValue]
      rw [scan_outside_wordStart]
      simp only [List.cons_append]
      rw [scan_guard_true]
      calc
        _ = FiniteStateTransducer.scan (transition .segment)
            (.nat .segment)
            ((CarrierKeyWords.natField segmentIndex ++
                CarrierKeyWords.intField horizontal ++
                CarrierKeyWords.intField vertical).map
              DelimitedBinaryWords.Token.bit ++
              [DelimitedBinaryWords.Token.wordEnd]) := by
          simpa only [List.append_assoc] using
            scan_routeNatField_to_segment routeIndex
              (CarrierKeyWords.natField segmentIndex ++
                CarrierKeyWords.intField horizontal ++
                CarrierKeyWords.intField vertical)
        _ = (.outside,
            UnaryFieldEncoderMachine.unaryField segmentIndex) := by
          simpa only [List.append_assoc] using
            scan_segmentNatField segmentIndex
              (CarrierKeyWords.intField horizontal ++
                CarrierKeyWords.intField vertical)

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
