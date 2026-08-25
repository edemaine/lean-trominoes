/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyCandidateWordSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeySemanticKeyData
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRouteFieldProjectorWordSemantics

/-! # Canonical semantic words of the active carrier-key stream -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing

open PaddedSupportedCandidateWords
open PaddedSupportedLastRepresentativeEqualityRows

@[simp] theorem guardedWord_mapActiveValue_carrierKey
    (candidate : Candidate CarrierNode) :
    guardedWord CarrierKeyWords.word
        (candidate.mapActiveValue CarrierNode.carrierKey) =
      CarrierKeyRouteFieldProjector.semanticWord
        (candidate.value.map CarrierNode.carrierKey) := by
  rcases candidate with ⟨value, supported⟩
  cases value <;> rfl

/-- Every compiled active carrier-key word is the projector's canonical
semantic word for the corresponding optional padded carrier node. -/
theorem CarrierActiveKeyRecipeStream.guardedWords_eq_semanticWords
    (descriptors : List RouteDescriptor) :
    CarrierActiveKeyRecipeStream.guardedWords descriptors =
      (CarrierActiveKeyRecipeStream.semanticKeys descriptors).map
        CarrierKeyRouteFieldProjector.semanticWord := by
  rw [CarrierActiveKeyRecipeStream.guardedWords_eq_paddedCarrierNodes]
  simp [CarrierActiveKeyRecipeStream.semanticKeys, values, List.map_map]

end LeanTrominoes.PeriodicOrthocrossing

end
