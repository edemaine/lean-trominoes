/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRouteFieldProjectorWordSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Stream semantics of carrier-key route projection -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRouteFieldProjector

theorem scan_encode_semanticWords
    (keys : List (Option CarrierKeyWords.CarrierKey)) :
    FiniteStateTransducer.scan transition .outside
        (DelimitedBinaryWords.encode ⟨keys.map semanticWord⟩) =
      (.outside, UnaryFieldEncoderMachine.unaryFields (keys.map value)) := by
  induction keys with
  | nil => rfl
  | cons key keys induction =>
      unfold DelimitedBinaryWords.encode
      rw [List.map_cons, List.flatMap_cons,
        FiniteStateTransducer.scan_append, scan_semanticWord]
      dsimp
      unfold DelimitedBinaryWords.encode at induction
      rw [induction]

/-- Projecting a canonical semantic key-word stream yields one route-index
field per word followed by the unary-zero lookup sentinel. -/
theorem output_encode_semanticWords
    (keys : List (Option CarrierKeyWords.CarrierKey)) :
    output (DelimitedBinaryWords.encode ⟨keys.map semanticWord⟩) =
      UnaryFieldEncoderMachine.unaryFields (keys.map value ++ [0]) := by
  unfold output FiniteStateTransducer.output
  rw [scan_encode_semanticWords]
  simp [finish, UnaryFieldEncoderMachine.unaryField]

end CarrierKeyRouteFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
