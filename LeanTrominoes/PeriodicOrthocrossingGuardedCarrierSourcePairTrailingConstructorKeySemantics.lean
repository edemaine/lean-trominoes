/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairTrailingConstructorNatSemantics

/-! # Carrier-key scan semantics for delayed constructor classification -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedCarrierSourcePairTrailingConstructor

open DelimitedBinaryWords

theorem scan_horizontalUnits (boundary : Bool) (number : Nat) :
    FiniteStateTransducer.scan transition (.horizontal boundary)
        (List.replicate number (.bit false)) =
      (.horizontal boundary, List.replicate number (.bit false)) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ]
      simp only [FiniteStateTransducer.scan, transition, induction,
        List.cons_append, List.nil_append]

theorem scan_horizontalField (boundary : Bool) (number : Nat) :
    FiniteStateTransducer.scan transition (.horizontal boundary)
        ((CarrierKeyWords.natField number).map Token.bit) =
      (.verticalSign boundary,
        (CarrierKeyWords.natField number).map Token.bit) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_singleton]
  rw [FiniteStateTransducer.scan_append, scan_horizontalUnits]
  cases boundary <;>
    simp [FiniteStateTransducer.scan, transition]

theorem scan_verticalUnits (boundary : Bool) (number : Nat) :
    FiniteStateTransducer.scan transition (.vertical boundary)
        (List.replicate number (.bit false)) =
      (.vertical boundary, List.replicate number (.bit false)) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ]
      simp only [FiniteStateTransducer.scan, transition, induction,
        List.cons_append, List.nil_append]

theorem scan_verticalField (boundary : Bool) (number : Nat) :
    FiniteStateTransducer.scan transition (.vertical boundary)
        ((CarrierKeyWords.natField number).map Token.bit) =
      (.separator boundary,
        (CarrierKeyWords.natField number).map Token.bit) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_singleton]
  rw [FiniteStateTransducer.scan_append, scan_verticalUnits]
  cases boundary <;>
    simp [FiniteStateTransducer.scan, transition]

theorem scan_horizontalIntField (boundary : Bool) (integer : Int) :
    FiniteStateTransducer.scan transition (.horizontalSign boundary)
        ((CarrierKeyWords.intField integer).map Token.bit) =
      (.verticalSign boundary,
        (CarrierKeyWords.intField integer).map Token.bit) := by
  cases integer <;>
    simp [CarrierKeyWords.intField, FiniteStateTransducer.scan,
      transition, scan_horizontalField]

theorem scan_verticalIntField (boundary : Bool) (integer : Int) :
    FiniteStateTransducer.scan transition (.verticalSign boundary)
        ((CarrierKeyWords.intField integer).map Token.bit) =
      (.separator boundary,
        (CarrierKeyWords.intField integer).map Token.bit) := by
  cases integer <;>
    simp [CarrierKeyWords.intField, FiniteStateTransducer.scan,
      transition, scan_verticalField]

/-- Scanning a tagged first key recovers its low-three-bit tag and otherwise
copies the key verbatim. -/
theorem scan_taggedKey
    (key : CarrierKeyWords.CarrierKey) (tag : Nat) :
    FiniteStateTransducer.scan transition .route
        ((CarrierKeyWords.word
          (CarrierNodeSourceKeys.taggedKey key tag)).map Token.bit) =
      (.separator
        (TagRemainder.advance .zero tag).isBoundary,
        (CarrierKeyWords.word
          (CarrierNodeSourceKeys.taggedKey key tag)).map Token.bit) := by
  rcases key with ⟨routeIndex, segmentIndex, horizontal, vertical⟩
  unfold CarrierKeyWords.word CarrierNodeSourceKeys.taggedKey
  simp only [List.map_append, List.append_assoc]
  rw [FiniteStateTransducer.scan_append, scan_routeField]
  simp only
  rw [FiniteStateTransducer.scan_append, scan_taggedSegmentField]
  simp only
  rw [FiniteStateTransducer.scan_append, scan_horizontalIntField]
  simp only
  rw [scan_verticalIntField]

theorem scan_secondBits (boundary : Bool) (bits : List Bool) :
    FiniteStateTransducer.scan transition (.second boundary)
        (bits.map Token.bit) =
      (.second boundary,
        if boundary then bits.map Token.bit else []) := by
  induction bits with
  | nil => cases boundary <;> rfl
  | cons bit bits induction =>
      cases boundary <;>
        simp [FiniteStateTransducer.scan, transition, induction]

theorem scan_secondKey_wordEnd (boundary : Bool)
    (key : CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan transition (.second boundary)
        ((CarrierKeyWords.word key).map Token.bit ++ [.wordEnd]) =
      (.between,
        (if boundary then
          (CarrierKeyWords.word key).map Token.bit
        else []) ++ [.bit boundary, .wordEnd]) := by
  rw [FiniteStateTransducer.scan_append, scan_secondBits]
  cases boundary <;>
    simp [FiniteStateTransducer.scan, transition]

end GuardedCarrierSourcePairTrailingConstructor
end LeanTrominoes.PeriodicOrthocrossing
