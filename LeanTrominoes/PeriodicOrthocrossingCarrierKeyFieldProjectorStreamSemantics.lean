/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FiniteStateTransducerSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorData
import LeanTrominoes.UnaryFieldEncoderFlatMapSemantics

/-! # Generic stream semantics of carrier-key field projection -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyFieldProjector

/-- Exact one-word behavior required to lift a fixed key column over a
delimiter-separated stream. -/
def WordCorrect (field : Field) : Prop :=
  ∀ key : Option CarrierKeyWords.CarrierKey,
    FiniteStateTransducer.scan (transition field) .outside
        (DelimitedBinaryWords.wordTokens (semanticWord key)) =
      (.outside, UnaryFieldEncoderMachine.unaryField (value field key))

theorem scan_encode_semanticWords (field : Field)
    (wordCorrect : WordCorrect field)
    (keys : List (Option CarrierKeyWords.CarrierKey)) :
    FiniteStateTransducer.scan (transition field) .outside
        (DelimitedBinaryWords.encode ⟨keys.map semanticWord⟩) =
      (.outside,
        UnaryFieldEncoderMachine.unaryFields (keys.map (value field))) := by
  induction keys with
  | nil => rfl
  | cons key keys induction =>
      unfold DelimitedBinaryWords.encode
      rw [List.map_cons, List.flatMap_cons,
        FiniteStateTransducer.scan_append, wordCorrect key]
      dsimp
      unfold DelimitedBinaryWords.encode at induction
      rw [induction]

/-- Every word contributes one selected unary field, and `finish` contributes
the final unary-zero representative-lookup sentinel. -/
theorem output_encode_semanticWords (field : Field)
    (wordCorrect : WordCorrect field)
    (keys : List (Option CarrierKeyWords.CarrierKey)) :
    output field (DelimitedBinaryWords.encode ⟨keys.map semanticWord⟩) =
      UnaryFieldEncoderMachine.unaryFields
        (keys.map (value field) ++ [0]) := by
  unfold output FiniteStateTransducer.output
  rw [scan_encode_semanticWords field wordCorrect]
  simp [finish, UnaryFieldEncoderMachine.unaryField]

end CarrierKeyFieldProjector
end LeanTrominoes.PeriodicOrthocrossing
