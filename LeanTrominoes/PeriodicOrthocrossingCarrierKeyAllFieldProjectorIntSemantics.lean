/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorNatSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Signed-field semantics of the all-field carrier-key projector -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAllFieldProjector

theorem scan_intUnits (coordinate : Coordinate) (negative : Bool)
    (number : Nat) :
    FiniteStateTransducer.scan transition (.intBody coordinate negative)
        (List.replicate number
          (DelimitedBinaryWords.Token.bit false)) =
      (.intBody coordinate negative, List.replicate number
        UnaryFieldEncoderMachine.Symbol.unit) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ, List.replicate_succ]
      cases coordinate <;> cases negative <;>
        simp only [FiniteStateTransducer.scan, transition, induction,
          List.cons_append, List.nil_append]

theorem scan_positiveIntBody (coordinate : Coordinate) (number : Nat) :
    FiniteStateTransducer.scan transition (.intBody coordinate false)
        ((CarrierKeyWords.natField number).map
          DelimitedBinaryWords.Token.bit) =
      (nextCoordinate coordinate,
        UnaryFieldEncoderMachine.unaryField number) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.map_nil]
  rw [FiniteStateTransducer.scan_append, scan_intUnits]
  cases coordinate <;>
    simp [FiniteStateTransducer.scan, transition, nextCoordinate,
      UnaryFieldEncoderMachine.unaryField]

theorem scan_negativeIntBody (coordinate : Coordinate) (number : Nat) :
    FiniteStateTransducer.scan transition (.intBody coordinate true)
        ((CarrierKeyWords.natField number).map
          DelimitedBinaryWords.Token.bit) =
      (nextCoordinate coordinate,
        List.replicate number UnaryFieldEncoderMachine.Symbol.unit ++
          [.delimiter, .delimiter]) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.map_nil]
  rw [FiniteStateTransducer.scan_append, scan_intUnits]
  cases coordinate <;>
    simp [FiniteStateTransducer.scan, transition, nextCoordinate]

/-- A canonical signed field becomes its negative magnitude followed by its
positive magnitude. -/
theorem scan_intField (coordinate : Coordinate) (integer : Int) :
    FiniteStateTransducer.scan transition (.intSign coordinate)
        ((CarrierKeyWords.intField integer).map
          DelimitedBinaryWords.Token.bit) =
      (nextCoordinate coordinate,
        UnaryFieldEncoderMachine.unaryFields
          [(-integer).toNat, integer.toNat]) := by
  cases integer with
  | ofNat number =>
      simp only [CarrierKeyWords.intField, List.map_cons,
        FiniteStateTransducer.scan, transition]
      rw [scan_positiveIntBody]
      simp [UnaryFieldEncoderMachine.unaryFields,
        UnaryFieldEncoderMachine.unaryField]
  | negSucc number =>
      simp only [CarrierKeyWords.intField, List.map_cons,
        FiniteStateTransducer.scan, transition]
      rw [scan_negativeIntBody]
      simp [UnaryFieldEncoderMachine.unaryFields,
        UnaryFieldEncoderMachine.unaryField, List.replicate_succ,
        Int.negSucc_eq, List.append_assoc]

end CarrierKeyAllFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
