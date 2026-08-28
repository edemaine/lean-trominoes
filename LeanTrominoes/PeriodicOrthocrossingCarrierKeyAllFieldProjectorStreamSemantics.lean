/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyAllFieldProjectorWordSemantics
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Stream semantics of the all-field carrier-key projector -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAllFieldProjector

theorem scan_encode_semanticWords
    (keys : List (Option CarrierKeyWords.CarrierKey)) :
    FiniteStateTransducer.scan transition .outside
        (DelimitedBinaryWords.encode
          ⟨keys.map CarrierKeyFieldProjector.semanticWord⟩) =
      (.outside,
        UnaryFieldEncoderMachine.unaryFields (keys.flatMap keyFields)) := by
  induction keys with
  | nil => rfl
  | cons key keys induction =>
      unfold DelimitedBinaryWords.encode
      rw [List.map_cons, List.flatMap_cons,
        FiniteStateTransducer.scan_append, scan_semanticWord]
      dsimp
      unfold DelimitedBinaryWords.encode at induction
      rw [induction]
      simp [UnaryFieldEncoderMachine.unaryFields_append]

/-- The complete stream contains six fields per component word and finishes
with the twelve zero fields of one rejected source-pair sentinel. -/
@[simp] theorem output_encode_semanticWords
    (keys : List (Option CarrierKeyWords.CarrierKey)) :
    output
        (DelimitedBinaryWords.encode
          ⟨keys.map CarrierKeyFieldProjector.semanticWord⟩) =
      UnaryFieldEncoderMachine.unaryFields (valuesWithSentinel keys) := by
  unfold output FiniteStateTransducer.output valuesWithSentinel
  rw [scan_encode_semanticWords]
  simp [finish, UnaryFieldEncoderMachine.unaryFields,
    UnaryFieldEncoderMachine.unaryField, List.replicate_succ]

end CarrierKeyAllFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
