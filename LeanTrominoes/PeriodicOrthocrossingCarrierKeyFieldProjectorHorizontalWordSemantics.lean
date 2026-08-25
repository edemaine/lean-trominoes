/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorHorizontalIntSemantics

/-! # Guarded-word semantics of horizontal carrier-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

theorem scan_semanticWord_horizontalPositive
    (key : Option CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan (transition .horizontalPositive) .outside
        (DelimitedBinaryWords.wordTokens (semanticWord key)) =
      (.outside,
        UnaryFieldEncoderMachine.unaryField
          (value .horizontalPositive key)) := by
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
        _ = FiniteStateTransducer.scan (transition .horizontalPositive)
            (.intSign .horizontal)
            ((CarrierKeyWords.intField horizontal ++
                CarrierKeyWords.intField vertical).map
              DelimitedBinaryWords.Token.bit ++
              [DelimitedBinaryWords.Token.wordEnd]) := by
          simpa only [List.append_assoc] using
            scan_natPrefix_to_horizontalSign .horizontalPositive rfl rfl
              routeIndex segmentIndex
              (CarrierKeyWords.intField horizontal ++
                CarrierKeyWords.intField vertical)
        _ = (.outside,
            UnaryFieldEncoderMachine.unaryField horizontal.toNat) := by
          simpa only [List.append_assoc] using
            scan_horizontalPositiveIntField horizontal
              (CarrierKeyWords.intField vertical)

theorem scan_semanticWord_horizontalNegative
    (key : Option CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan (transition .horizontalNegative) .outside
        (DelimitedBinaryWords.wordTokens (semanticWord key)) =
      (.outside,
        UnaryFieldEncoderMachine.unaryField
          (value .horizontalNegative key)) := by
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
        _ = FiniteStateTransducer.scan (transition .horizontalNegative)
            (.intSign .horizontal)
            ((CarrierKeyWords.intField horizontal ++
                CarrierKeyWords.intField vertical).map
              DelimitedBinaryWords.Token.bit ++
              [DelimitedBinaryWords.Token.wordEnd]) := by
          simpa only [List.append_assoc] using
            scan_natPrefix_to_horizontalSign .horizontalNegative rfl rfl
              routeIndex segmentIndex
              (CarrierKeyWords.intField horizontal ++
                CarrierKeyWords.intField vertical)
        _ = (.outside,
            UnaryFieldEncoderMachine.unaryField (-horizontal).toNat) := by
          simpa only [List.append_assoc] using
            scan_horizontalNegativeIntField horizontal
              (CarrierKeyWords.intField vertical)

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
