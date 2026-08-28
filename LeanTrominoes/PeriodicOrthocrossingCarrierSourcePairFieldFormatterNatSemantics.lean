/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierSourcePairFieldFormatterData

/-! # Natural-field semantics of the source-pair formatter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourcePairFieldFormatter

theorem scan_natUnits (side : Side) (part : NatPart) (number : Nat) :
    FiniteStateTransducer.scan transition (.nat side part)
        (List.replicate number UnaryFieldEncoderMachine.Symbol.unit) =
      (.nat side part,
        List.replicate number (DelimitedBinaryWords.Token.bit false)) := by
  induction number with
  | zero => rfl
  | succ number induction =>
      rw [List.replicate_succ, List.replicate_succ]
      cases side <;> cases part <;>
        simp only [FiniteStateTransducer.scan, transition, induction,
          List.cons_append, List.nil_append]

theorem scan_routeField (side : Side) (number : Nat) :
    FiniteStateTransducer.scan transition (.nat side .route)
        (UnaryFieldEncoderMachine.unaryField number) =
      (.nat side .segment,
        (CarrierKeyWords.natField number).map
          DelimitedBinaryWords.Token.bit) := by
  unfold UnaryFieldEncoderMachine.unaryField CarrierKeyWords.natField
  rw [FiniteStateTransducer.scan_append, scan_natUnits]
  cases side <;>
    simp [FiniteStateTransducer.scan, transition, List.map_append]

theorem scan_segmentField (side : Side) (number : Nat) :
    FiniteStateTransducer.scan transition (.nat side .segment)
        (UnaryFieldEncoderMachine.unaryField number) =
      (.negative side .horizontal false,
        (CarrierKeyWords.natField number).map
          DelimitedBinaryWords.Token.bit) := by
  unfold UnaryFieldEncoderMachine.unaryField CarrierKeyWords.natField
  rw [FiniteStateTransducer.scan_append, scan_natUnits]
  cases side <;>
    simp [FiniteStateTransducer.scan, transition, List.map_append]

theorem scan_beginRouteField (number : Nat) :
    FiniteStateTransducer.scan transition .begin
        (UnaryFieldEncoderMachine.unaryField number) =
      (.nat .first .segment,
        [.wordStart, .bit true] ++
          (CarrierKeyWords.natField number).map
            DelimitedBinaryWords.Token.bit) := by
  cases number with
  | zero => rfl
  | succ number =>
      rw [show UnaryFieldEncoderMachine.unaryField (number + 1) =
        .unit :: UnaryFieldEncoderMachine.unaryField number by
          simp [UnaryFieldEncoderMachine.unaryField,
            List.replicate_succ]]
      simp only [FiniteStateTransducer.scan, transition]
      rw [scan_routeField]
      simp [CarrierKeyWords.natField, List.replicate_succ,
        List.map_append]

end CarrierSourcePairFieldFormatter
end LeanTrominoes.PeriodicOrthocrossing
