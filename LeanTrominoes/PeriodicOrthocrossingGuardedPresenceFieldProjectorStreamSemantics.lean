/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingGuardedPresenceFieldProjectorWordSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Stream semantics of guarded presence projection -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace GuardedPresenceFieldProjector

theorem scan_encode_semanticWords (activeValue : Bool)
    (keys : List (Option CarrierKeyWords.CarrierKey)) :
    FiniteStateTransducer.scan (transition activeValue) .outside
        (DelimitedBinaryWords.encode ⟨keys.map semanticWord⟩) =
      (.outside,
        UnaryFieldEncoderMachine.unaryFields
          (keys.map (value activeValue))) := by
  induction keys with
  | nil => rfl
  | cons key keys induction =>
      unfold DelimitedBinaryWords.encode
      rw [List.map_cons, List.flatMap_cons,
        FiniteStateTransducer.scan_append,
        scan_semanticWord activeValue key]
      dsimp
      unfold DelimitedBinaryWords.encode at induction
      rw [induction]

theorem output_encode_semanticWords (activeValue : Bool)
    (keys : List (Option CarrierKeyWords.CarrierKey)) :
    output activeValue
        (DelimitedBinaryWords.encode ⟨keys.map semanticWord⟩) =
      UnaryFieldEncoderMachine.unaryFields
        (keys.map (value activeValue)) := by
  unfold output FiniteStateTransducer.output
  rw [scan_encode_semanticWords]
  simp [finish]

end GuardedPresenceFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
