/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourcePairFieldFormatterNatSemantics

/-! # Signed-field semantics of the source-pair formatter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourcePairFieldFormatter

theorem scan_negativeSeenUnits (side : Side) (coordinate : Coordinate)
    (number : Nat) :
    FiniteStateTransducer.scan transition (.negative side coordinate true)
        (List.replicate number UnaryFieldEncoderMachine.Symbol.unit) =
      (.negative side coordinate true,
        List.replicate number (DelimitedBinaryWords.Token.bit false)) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ, List.replicate_succ]
      cases side <;> cases coordinate <;>
        simp only [FiniteStateTransducer.scan, transition, induction,
          List.cons_append, List.nil_append]

theorem scan_positiveUnits (side : Side) (coordinate : Coordinate)
    (enabled : Bool) (number : Nat) :
    FiniteStateTransducer.scan transition (.positive side coordinate enabled)
        (List.replicate number UnaryFieldEncoderMachine.Symbol.unit) =
      (.positive side coordinate enabled,
        if enabled then
          List.replicate number (DelimitedBinaryWords.Token.bit false)
        else []) := by
  induction number with
  | zero => cases enabled <;> rfl
  | succ number induction =>
      rw [List.replicate_succ]
      cases side <;> cases coordinate <;> cases enabled <;>
        simp [FiniteStateTransducer.scan, transition, induction,
          List.replicate_succ]

theorem scan_positiveField (side : Side) (coordinate : Coordinate)
    (enabled : Bool) (number : Nat) :
    FiniteStateTransducer.scan transition (.positive side coordinate enabled)
        (UnaryFieldEncoderMachine.unaryField number) =
      (afterCoordinate side coordinate,
        (if enabled then
          (CarrierKeyWords.natField number).map
            DelimitedBinaryWords.Token.bit
        else []) ++ coordinateSuffix side coordinate) := by
  unfold UnaryFieldEncoderMachine.unaryField CarrierKeyWords.natField
  rw [FiniteStateTransducer.scan_append,
    scan_positiveUnits side coordinate enabled number]
  cases side <;> cases coordinate <;> cases enabled <;>
    simp [FiniteStateTransducer.scan, transition, afterCoordinate,
      coordinateSuffix, List.map_append, List.append_assoc]

theorem scan_negativeZero (side : Side) (coordinate : Coordinate) :
    FiniteStateTransducer.scan transition (.negative side coordinate false)
        (UnaryFieldEncoderMachine.unaryField 0) =
      (.positive side coordinate true,
        [DelimitedBinaryWords.Token.bit false]) := by
  cases side <;> cases coordinate <;> rfl

theorem scan_negativeSucc (side : Side) (coordinate : Coordinate)
    (number : Nat) :
    FiniteStateTransducer.scan transition (.negative side coordinate false)
        (UnaryFieldEncoderMachine.unaryField (number + 1)) =
      (.positive side coordinate false,
        (CarrierKeyWords.intField (.negSucc number)).map
          DelimitedBinaryWords.Token.bit) := by
  rw [show UnaryFieldEncoderMachine.unaryField (number + 1) =
    .unit ::
      (List.replicate number UnaryFieldEncoderMachine.Symbol.unit ++
        [.delimiter]) by
      simp [UnaryFieldEncoderMachine.unaryField, List.replicate_succ]]
  simp only [FiniteStateTransducer.scan, transition]
  rw [FiniteStateTransducer.scan_append,
    scan_negativeSeenUnits side coordinate number]
  cases side <;> cases coordinate <;>
    simp [FiniteStateTransducer.scan, transition, CarrierKeyWords.intField,
      CarrierKeyWords.natField, List.map_append]

/-- Canonical negative/positive magnitudes reconstruct the signed unary word
and advance to the next coordinate or source-key component. -/
theorem scan_intFields (side : Side) (coordinate : Coordinate)
    (integer : Int) :
    FiniteStateTransducer.scan transition (.negative side coordinate false)
        (UnaryFieldEncoderMachine.unaryField (-integer).toNat ++
          UnaryFieldEncoderMachine.unaryField integer.toNat) =
      (afterCoordinate side coordinate,
        (CarrierKeyWords.intField integer).map
            DelimitedBinaryWords.Token.bit ++
          coordinateSuffix side coordinate) := by
  cases integer with
  | ofNat number =>
      have negativeZero : (-Int.ofNat number).toNat = 0 := by simp
      have positiveValue : (Int.ofNat number).toNat = number := rfl
      rw [FiniteStateTransducer.scan_append]
      rw [negativeZero, positiveValue, scan_negativeZero]
      dsimp
      rw [scan_positiveField]
      simp [CarrierKeyWords.intField, CarrierKeyWords.natField,
        List.map_append, List.append_assoc]
  | negSucc number =>
      rw [FiniteStateTransducer.scan_append]
      simp only [Int.toNat_negSucc]
      rw [show (-Int.negSucc number).toNat = number + 1 by
        simp [Int.negSucc_eq]]
      rw [scan_negativeSucc, scan_positiveField]
      simp

end CarrierSourcePairFieldFormatter
end LeanTrominoes.PeriodicOrthocrossing
