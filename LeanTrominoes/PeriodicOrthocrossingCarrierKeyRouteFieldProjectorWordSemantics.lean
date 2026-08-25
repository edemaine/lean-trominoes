/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRouteFieldProjectorData

/-! # One-word semantics of carrier-key route projection -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRouteFieldProjector

def value : Option CarrierKeyWords.CarrierKey → Nat
  | none => 0
  | some key => key.1

def semanticWord : Option CarrierKeyWords.CarrierKey → List Bool
  | none => [false]
  | some key => true :: CarrierKeyWords.word key

@[simp] theorem scan_outside_wordStart
    (tokens : List DelimitedBinaryWords.Token) :
    FiniteStateTransducer.scan transition .outside
        (DelimitedBinaryWords.Token.wordStart :: tokens) =
      FiniteStateTransducer.scan transition .guard tokens := by
  simp [FiniteStateTransducer.scan, transition]

@[simp] theorem scan_guard_true
    (tokens : List DelimitedBinaryWords.Token) :
    FiniteStateTransducer.scan transition .guard
        (DelimitedBinaryWords.Token.bit true :: tokens) =
      FiniteStateTransducer.scan transition .route tokens := by
  simp [FiniteStateTransducer.scan, transition]

theorem scan_routeUnits (number : Nat) :
    FiniteStateTransducer.scan transition .route
        (List.replicate number
          (DelimitedBinaryWords.Token.bit false)) =
      (.route, List.replicate number
        UnaryFieldEncoderMachine.Symbol.unit) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ, List.replicate_succ]
      simp only [FiniteStateTransducer.scan, transition]
      rw [induction]
      rfl

theorem scan_skipBits (bits : List Bool) :
    FiniteStateTransducer.scan transition .skip
        (bits.map DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      (.outside, []) := by
  induction bits with
  | nil => rfl
  | cons bit bits induction =>
      simp only [List.map_cons, List.cons_append,
        FiniteStateTransducer.scan, transition]
      exact induction

theorem scan_routeField_suffix (number : Nat) (suffix : List Bool) :
    FiniteStateTransducer.scan transition .route
        (List.replicate number
            (DelimitedBinaryWords.Token.bit false) ++
          DelimitedBinaryWords.Token.bit true ::
            (suffix.map DelimitedBinaryWords.Token.bit ++
              [DelimitedBinaryWords.Token.wordEnd])) =
      (.outside, UnaryFieldEncoderMachine.unaryField number) := by
  rw [FiniteStateTransducer.scan_append, scan_routeUnits]
  dsimp
  simp only [FiniteStateTransducer.scan, transition]
  rw [scan_skipBits]
  simp [UnaryFieldEncoderMachine.unaryField]

theorem scan_natField_suffix (number : Nat) (suffix : List Bool) :
    FiniteStateTransducer.scan transition .route
        ((CarrierKeyWords.natField number ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      (.outside, UnaryFieldEncoderMachine.unaryField number) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.nil_append, List.append_assoc, List.cons_append]
  exact scan_routeField_suffix number suffix

theorem scan_semanticWord
    (key : Option CarrierKeyWords.CarrierKey) :
    FiniteStateTransducer.scan transition .outside
        (DelimitedBinaryWords.wordTokens (semanticWord key)) =
      (.outside, UnaryFieldEncoderMachine.unaryField (value key)) := by
  cases key with
  | none => rfl
  | some key =>
      rcases key with ⟨routeIndex, segmentIndex, ⟨horizontal, vertical⟩⟩
      simp only [semanticWord, DelimitedBinaryWords.wordTokens,
        CarrierKeyWords.word, List.map_cons, value]
      rw [scan_outside_wordStart]
      simp only [List.cons_append]
      rw [scan_guard_true]
      simpa only [List.append_assoc] using
        scan_natField_suffix routeIndex
          (CarrierKeyWords.natField segmentIndex ++
            CarrierKeyWords.intField horizontal ++
            CarrierKeyWords.intField vertical)

end CarrierKeyRouteFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
