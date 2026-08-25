/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorSignedPrefixSemantics

/-! # Signed-magnitude body semantics of carrier-key projection -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

theorem scan_intUnits_units (field : Field) (coordinate : Coordinate)
    (number : Nat) :
    FiniteStateTransducer.scan (transition field)
        (.intBody coordinate .units)
        (List.replicate number
          (DelimitedBinaryWords.Token.bit false)) =
      (.intBody coordinate .units,
        List.replicate number UnaryFieldEncoderMachine.Symbol.unit) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ, List.replicate_succ]
      simp only [FiniteStateTransducer.scan, transition]
      rw [induction]
      rfl

theorem scan_intUnits_zero (field : Field) (coordinate : Coordinate)
    (number : Nat) :
    FiniteStateTransducer.scan (transition field)
        (.intBody coordinate .zero)
        (List.replicate number
          (DelimitedBinaryWords.Token.bit false)) =
      (.intBody coordinate .zero, []) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ]
      simp only [FiniteStateTransducer.scan, transition]
      exact induction

theorem scan_intUnits_skip (field : Field) (coordinate : Coordinate)
    (number : Nat) :
    FiniteStateTransducer.scan (transition field)
        (.intBody coordinate .skip)
        (List.replicate number
          (DelimitedBinaryWords.Token.bit false)) =
      (.intBody coordinate .skip, []) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ]
      simp only [FiniteStateTransducer.scan, transition]
      exact induction

theorem scan_intBody_units (field : Field) (coordinate : Coordinate)
    (number : Nat) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition field)
        (.intBody coordinate .units)
        ((CarrierKeyWords.natField number ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      (.outside, UnaryFieldEncoderMachine.unaryField number) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.nil_append, List.append_assoc, List.cons_append]
  rw [FiniteStateTransducer.scan_append,
    scan_intUnits_units field coordinate]
  dsimp
  cases coordinate <;> simp only [FiniteStateTransducer.scan, transition]
  all_goals
    rw [scan_skipBits]
    simp [UnaryFieldEncoderMachine.unaryField]

theorem scan_intBody_zero (field : Field) (coordinate : Coordinate)
    (number : Nat) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition field)
        (.intBody coordinate .zero)
        ((CarrierKeyWords.natField number ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      (.outside, UnaryFieldEncoderMachine.unaryField 0) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.nil_append, List.append_assoc, List.cons_append]
  rw [FiniteStateTransducer.scan_append,
    scan_intUnits_zero field coordinate]
  dsimp
  cases coordinate <;> simp only [FiniteStateTransducer.scan, transition]
  all_goals
    rw [scan_skipBits]
    rfl

theorem scan_intBody_skip_horizontal_to_vertical
    (field : Field) (number : Nat) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition field)
        (.intBody .horizontal .skip)
        ((CarrierKeyWords.natField number ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      FiniteStateTransducer.scan (transition field) (.intSign .vertical)
        (suffix.map DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.nil_append, List.append_assoc, List.cons_append]
  rw [FiniteStateTransducer.scan_append,
    scan_intUnits_skip field .horizontal]
  rfl

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
