/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorSignedBodySemantics

/-! # Horizontal signed-field semantics of carrier-key projection -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

theorem scan_horizontalPositiveIntField
    (integer : Int) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition .horizontalPositive)
        (.intSign .horizontal)
        ((CarrierKeyWords.intField integer ++ suffix).map
            DelimitedBinaryWords.Token.bit ++
          [DelimitedBinaryWords.Token.wordEnd]) =
      (.outside, UnaryFieldEncoderMachine.unaryField integer.toNat) := by
  cases integer with
  | ofNat number =>
      simp only [CarrierKeyWords.intField, List.cons_append,
        List.map_cons, FiniteStateTransducer.scan, transition,
        intMode, selectsSigned, selectsCoordinate, if_true]
      exact scan_intBody_units .horizontalPositive .horizontal number suffix
  | negSucc number =>
      simp only [CarrierKeyWords.intField, List.cons_append,
        List.map_cons, FiniteStateTransducer.scan, transition,
        intMode, selectsSigned, selectsCoordinate, if_true,
        Int.toNat_negSucc]
      exact scan_intBody_zero .horizontalPositive .horizontal number suffix

theorem scan_horizontalNegativeIntField
    (integer : Int) (suffix : List Bool) :
    FiniteStateTransducer.scan (transition .horizontalNegative)
        (.intSign .horizontal)
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
        scan_intBody_zero .horizontalNegative .horizontal number suffix
  | negSucc number =>
      simp only [CarrierKeyWords.intField, List.cons_append,
        List.map_cons, FiniteStateTransducer.scan, transition,
        intMode, selectsSigned, selectsCoordinate, if_true]
      rw [scan_intBody_units]
      simp [UnaryFieldEncoderMachine.unaryField, List.replicate_succ]

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
