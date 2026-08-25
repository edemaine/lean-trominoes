/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorData

/-! # Natural-field semantics of carrier-key projection -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

@[simp] theorem scan_outside_wordStart (field : Field)
    (tokens : List DelimitedBinaryWords.Token) :
    FiniteStateTransducer.scan (transition field) .outside
        (DelimitedBinaryWords.Token.wordStart :: tokens) =
      FiniteStateTransducer.scan (transition field) .guard tokens := by
  simp [FiniteStateTransducer.scan, transition]

@[simp] theorem scan_guard_true (field : Field)
    (tokens : List DelimitedBinaryWords.Token) :
    FiniteStateTransducer.scan (transition field) .guard
        (DelimitedBinaryWords.Token.bit true :: tokens) =
      FiniteStateTransducer.scan (transition field) (.nat .route) tokens := by
  simp [FiniteStateTransducer.scan, transition]

theorem scan_natUnits_selected (field : Field) (part : NatPart)
    (selected : selectsNat field part = true) (number : Nat) :
    FiniteStateTransducer.scan (transition field) (.nat part)
        (List.replicate number
          (DelimitedBinaryWords.Token.bit false)) =
      (.nat part, List.replicate number
        UnaryFieldEncoderMachine.Symbol.unit) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ, List.replicate_succ]
      simp only [FiniteStateTransducer.scan, transition, selected,
        if_true]
      rw [induction]
      rfl

theorem scan_natUnits_unselected (field : Field) (part : NatPart)
    (unselected : selectsNat field part = false) (number : Nat) :
    FiniteStateTransducer.scan (transition field) (.nat part)
        (List.replicate number
          (DelimitedBinaryWords.Token.bit false)) =
      (.nat part, []) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ]
      simp only [FiniteStateTransducer.scan, transition, unselected]
      exact induction

theorem scan_skipBits (field : Field) (bits : List Bool) :
    FiniteStateTransducer.scan (transition field) .skip
        (bits.map DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      (.outside, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, transition]
      exact induction

theorem scan_routeNatField (number : Nat) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition .route) (.nat .route)
        ((CarrierKeyWords.natField number ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      (.outside, UnaryFieldEncoderMachine.unaryField number) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.nil_append, List.append_assoc, List.cons_append]
  rw [FiniteStateTransducer.scan_append,
    scan_natUnits_selected .route .route rfl]
  dsimp
  simp only [FiniteStateTransducer.scan, transition, selectsNat, if_true]
  rw [scan_skipBits]
  simp [UnaryFieldEncoderMachine.unaryField]

theorem scan_segmentNatField (number : Nat) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition .segment) (.nat .segment)
        ((CarrierKeyWords.natField number ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      (.outside, UnaryFieldEncoderMachine.unaryField number) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.nil_append, List.append_assoc, List.cons_append]
  rw [FiniteStateTransducer.scan_append,
    scan_natUnits_selected .segment .segment rfl]
  dsimp
  simp only [FiniteStateTransducer.scan, transition, selectsNat, if_true]
  rw [scan_skipBits]
  simp [UnaryFieldEncoderMachine.unaryField]

theorem scan_routeNatField_to_segment
    (number : Nat) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition .segment) (.nat .route)
        ((CarrierKeyWords.natField number ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      FiniteStateTransducer.scan (transition .segment) (.nat .segment)
        (suffix.map DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.nil_append, List.append_assoc, List.cons_append]
  rw [FiniteStateTransducer.scan_append,
    scan_natUnits_unselected .segment .route rfl]
  rfl

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
