/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyFieldSemanticWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyFieldProjectorStreamSemantics

/-! # Generic carrier-key field projection of the active key stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

/-- Any carrier-key field with proved one-word behavior projects from the
active key emitter to its exact aligned unary values plus one sentinel. -/
theorem CarrierActiveKeyRecipeStream.keyFieldOutput_descriptorWords
    (field : CarrierKeyFieldProjector.Field)
    (wordCorrect : CarrierKeyFieldProjector.WordCorrect field)
    (descriptors : List RouteDescriptor) :
    CarrierKeyFieldProjector.output field
        (CarrierActiveKeyRecipeStream.emittedTokens
          (RouteDescriptorBinaryWords.words descriptors)) =
      UnaryFieldEncoderMachine.unaryFields
        ((CarrierActiveKeyRecipeStream.semanticKeys descriptors).map
          (CarrierKeyFieldProjector.value field) ++ [0]) := by
  rw [CarrierActiveKeyRecipeStream.emittedTokens_descriptorWords,
    CarrierActiveKeyRecipeStream.guardedWords_eq_keyFieldSemanticWords]
  exact CarrierKeyFieldProjector.output_encode_semanticWords
    field wordCorrect (CarrierActiveKeyRecipeStream.semanticKeys descriptors)

end LeanTrominoes.PeriodicOrthocrossing

end
