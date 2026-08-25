/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorSignedBodySemantics

/-! # Vertical signed-field semantics of carrier-key projection -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

theorem scan_horizontalIntField_to_verticalPositive
    (integer : Int) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition .verticalPositive)
        (.intSign .horizontal)
        ((CarrierKeyWords.intField integer ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      FiniteStateTransducer.scan (transition .verticalPositive)
        (.intSign .vertical)
        (suffix.map DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) := by
  cases integer with
  | ofNat number =>
      simp only [CarrierKeyWords.intField, List.cons_append,
        List.map_cons, FiniteStateTransducer.scan, transition,
        intMode, selectsSigned, selectsCoordinate]
      exact scan_intBody_skip_horizontal_to_vertical
        .verticalPositive number suffix
  | negSucc number =>
      simp only [CarrierKeyWords.intField, List.cons_append,
        List.map_cons, FiniteStateTransducer.scan, transition,
        intMode, selectsSigned, selectsCoordinate]
      exact scan_intBody_skip_horizontal_to_vertical
        .verticalPositive number suffix

theorem scan_horizontalIntField_to_verticalNegative
    (integer : Int) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition .verticalNegative)
        (.intSign .horizontal)
        ((CarrierKeyWords.intField integer ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      FiniteStateTransducer.scan (transition .verticalNegative)
        (.intSign .vertical)
        (suffix.map DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) := by
  cases integer with
  | ofNat number =>
      simp only [CarrierKeyWords.intField, List.cons_append,
        List.map_cons, FiniteStateTransducer.scan, transition,
        intMode, selectsSigned, selectsCoordinate]
      exact scan_intBody_skip_horizontal_to_vertical
        .verticalNegative number suffix
  | negSucc number =>
      simp only [CarrierKeyWords.intField, List.cons_append,
        List.map_cons, FiniteStateTransducer.scan, transition,
        intMode, selectsSigned, selectsCoordinate]
      exact scan_intBody_skip_horizontal_to_vertical
        .verticalNegative number suffix

theorem scan_verticalPositiveIntField
    (integer : Int) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition .verticalPositive)
        (.intSign .vertical)
        ((CarrierKeyWords.intField integer ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      (.outside, UnaryFieldEncoderMachine.unaryField integer.toNat) := by
  cases integer with
  | ofNat number =>
      simp only [CarrierKeyWords.intField, List.cons_append,
        List.map_cons, FiniteStateTransducer.scan, transition,
        intMode, selectsSigned, selectsCoordinate, if_true]
      exact scan_intBody_units .verticalPositive .vertical number suffix
  | negSucc number =>
      simp only [CarrierKeyWords.intField, List.cons_append,
        List.map_cons, FiniteStateTransducer.scan, transition,
        intMode, selectsSigned, selectsCoordinate, if_true,
        Int.toNat_negSucc]
      exact scan_intBody_zero .verticalPositive .vertical number suffix

theorem scan_verticalNegativeIntField
    (integer : Int) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition .verticalNegative)
        (.intSign .vertical)
        ((CarrierKeyWords.intField integer ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      (.outside, UnaryFieldEncoderMachine.unaryField (-integer).toNat) := by
  cases integer with
  | ofNat number =>
      simp only [CarrierKeyWords.intField, List.cons_append,
        List.map_cons, FiniteStateTransducer.scan, transition,
        intMode, selectsSigned, selectsCoordinate, if_true]
      simpa using
        scan_intBody_zero .verticalNegative .vertical number suffix
  | negSucc number =>
      simp only [CarrierKeyWords.intField, List.cons_append,
        List.map_cons, FiniteStateTransducer.scan, transition,
        intMode, selectsSigned, selectsCoordinate, if_true]
      rw [scan_intBody_units]
      simp [UnaryFieldEncoderMachine.unaryField, List.replicate_succ]

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
