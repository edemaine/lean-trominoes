/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicOrthocrossingGuardedCarrierSourcePairTrailingConstructorData

/-! # Natural-field classification for guarded carrier source pairs -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedCarrierSourcePairTrailingConstructor

open DelimitedBinaryWords

@[simp] theorem TagRemainder.advance_add
    (remainder : TagRemainder) (first second : Nat) :
    remainder.advance (first + second) =
      (remainder.advance first).advance second := by
  induction first generalizing remainder with
  | zero => simp [TagRemainder.advance]
  | succ first induction =>
      simp only [Nat.succ_add, TagRemainder.advance]
      exact induction remainder.next

@[simp] theorem TagRemainder.advance_eight
    (remainder : TagRemainder) :
    remainder.advance 8 = remainder := by
  cases remainder <;> rfl

@[simp] theorem TagRemainder.advance_eight_mul
    (remainder : TagRemainder) (number : Nat) :
    remainder.advance (8 * number) = remainder := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [Nat.mul_succ, show 8 * number + 8 = 8 + 8 * number by omega,
        TagRemainder.advance_add, TagRemainder.advance_eight, induction]

theorem scan_routeUnits (number : Nat) :
    FiniteStateTransducer.scan transition .route
        (List.replicate number (.bit false)) =
      (.route, List.replicate number (.bit false)) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ]
      simp only [FiniteStateTransducer.scan, transition, induction,
        List.cons_append, List.nil_append]

theorem scan_routeField (number : Nat) :
    FiniteStateTransducer.scan transition .route
        ((CarrierKeyWords.natField number).map Token.bit) =
      (.segment .zero,
        (CarrierKeyWords.natField number).map Token.bit) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_singleton]
  rw [FiniteStateTransducer.scan_append]
  simp [scan_routeUnits, FiniteStateTransducer.scan, transition]

theorem scan_segmentUnits (remainder : TagRemainder) (number : Nat) :
    FiniteStateTransducer.scan transition (.segment remainder)
        (List.replicate number (.bit false)) =
      (.segment (remainder.advance number),
        List.replicate number (.bit false)) := by
  induction number generalizing remainder with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ]
      simp only [FiniteStateTransducer.scan, transition, induction,
        List.cons_append, List.nil_append, TagRemainder.advance]

theorem scan_segmentField (remainder : TagRemainder) (number : Nat) :
    FiniteStateTransducer.scan transition (.segment remainder)
        ((CarrierKeyWords.natField number).map Token.bit) =
      (.horizontalSign (remainder.advance number).isBoundary,
        (CarrierKeyWords.natField number).map Token.bit) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_singleton]
  rw [FiniteStateTransducer.scan_append,
    scan_segmentUnits]
  simp [FiniteStateTransducer.scan, transition]

theorem scan_taggedSegmentField (segmentIndex tag : Nat) :
    FiniteStateTransducer.scan transition (.segment .zero)
        ((CarrierKeyWords.natField (8 * segmentIndex + tag)).map
          Token.bit) =
      (.horizontalSign (TagRemainder.advance .zero tag).isBoundary,
        (CarrierKeyWords.natField (8 * segmentIndex + tag)).map
          Token.bit) := by
  rw [scan_segmentField, TagRemainder.advance_add,
    TagRemainder.advance_eight_mul]

end GuardedCarrierSourcePairTrailingConstructor
end LeanTrominoes.PeriodicOrthocrossing
