/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorData

/-! # Natural-field semantics of the all-field carrier-key projector -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAllFieldProjector

theorem scan_natUnits (part : NatPart) (number : Nat) :
    FiniteStateTransducer.scan transition (.nat part)
        (List.replicate number
          (DelimitedBinaryWords.Token.bit false)) =
      (.nat part, List.replicate number
        UnaryFieldEncoderMachine.Symbol.unit) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ, List.replicate_succ]
      cases part <;>
        simp only [FiniteStateTransducer.scan, transition, induction,
          List.cons_append, List.nil_append]

theorem scan_natField_route (number : Nat) :
    FiniteStateTransducer.scan transition (.nat .route)
        ((CarrierKeyWords.natField number).map
          DelimitedBinaryWords.Token.bit) =
      (.nat .segment, UnaryFieldEncoderMachine.unaryField number) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.map_nil]
  rw [FiniteStateTransducer.scan_append, scan_natUnits]
  simp [FiniteStateTransducer.scan, transition,
    UnaryFieldEncoderMachine.unaryField]

theorem scan_natField_segment (number : Nat) :
    FiniteStateTransducer.scan transition (.nat .segment)
        ((CarrierKeyWords.natField number).map
          DelimitedBinaryWords.Token.bit) =
      (.intSign .horizontal,
        UnaryFieldEncoderMachine.unaryField number) := by
  unfold CarrierKeyWords.natField
  simp only [List.map_append, List.map_replicate, List.map_cons,
    List.map_nil]
  rw [FiniteStateTransducer.scan_append, scan_natUnits]
  simp [FiniteStateTransducer.scan, transition,
    UnaryFieldEncoderMachine.unaryField]

end CarrierKeyAllFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
