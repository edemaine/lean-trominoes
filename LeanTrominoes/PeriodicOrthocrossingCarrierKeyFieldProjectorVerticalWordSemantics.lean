/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorVerticalIntSemantics

/-! # Guarded-word semantics of vertical carrier-key fields -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

theorem scan_semanticWord_verticalPositive
    (key : Option CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan (transition .verticalPositive) .outside
        (DelimitedBinaryWords.wordTokens (semanticWord key)) =
      (.outside,
        UnaryFieldEncoderMachine.unaryField
          (value .verticalPositive key)) := by
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
        _ = FiniteStateTransducer.scan (transition .verticalPositive)
            (.intSign .horizontal)
            ((CarrierKeyWords.intField horizontal ++
                CarrierKeyWords.intField vertical).map
              DelimitedBinaryWords.Token.bit ++
              [DelimitedBinaryWords.Token.wordEnd]) := by
          simpa only [List.append_assoc] using
            scan_natPrefix_to_horizontalSign .verticalPositive rfl rfl
              routeIndex segmentIndex
              (CarrierKeyWords.intField horizontal ++
                CarrierKeyWords.intField vertical)
        _ = FiniteStateTransducer.scan (transition .verticalPositive)
            (.intSign .vertical)
            ((CarrierKeyWords.intField vertical).map
              DelimitedBinaryWords.Token.bit ++
              [DelimitedBinaryWords.Token.wordEnd]) := by
          simpa only [List.append_assoc] using
            scan_horizontalIntField_to_verticalPositive horizontal
              (CarrierKeyWords.intField vertical)
        _ = (.outside,
            UnaryFieldEncoderMachine.unaryField vertical.toNat) := by
          simpa using scan_verticalPositiveIntField vertical []

theorem scan_semanticWord_verticalNegative
    (key : Option CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan (transition .verticalNegative) .outside
        (DelimitedBinaryWords.wordTokens (semanticWord key)) =
      (.outside,
        UnaryFieldEncoderMachine.unaryField
          (value .verticalNegative key)) := by
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
        _ = FiniteStateTransducer.scan (transition .verticalNegative)
            (.intSign .horizontal)
            ((CarrierKeyWords.intField horizontal ++
                CarrierKeyWords.intField vertical).map
              DelimitedBinaryWords.Token.bit ++
              [DelimitedBinaryWords.Token.wordEnd]) := by
          simpa only [List.append_assoc] using
            scan_natPrefix_to_horizontalSign .verticalNegative rfl rfl
              routeIndex segmentIndex
              (CarrierKeyWords.intField horizontal ++
                CarrierKeyWords.intField vertical)
        _ = FiniteStateTransducer.scan (transition .verticalNegative)
            (.intSign .vertical)
            ((CarrierKeyWords.intField vertical).map
              DelimitedBinaryWords.Token.bit ++
              [DelimitedBinaryWords.Token.wordEnd]) := by
          simpa only [List.append_assoc] using
            scan_horizontalIntField_to_verticalNegative horizontal
              (CarrierKeyWords.intField vertical)
        _ = (.outside,
            UnaryFieldEncoderMachine.unaryField (-vertical).toNat) := by
          simpa using scan_verticalNegativeIntField vertical []

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
