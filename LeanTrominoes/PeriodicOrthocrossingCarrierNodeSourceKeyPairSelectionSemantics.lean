/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordPairSelectorSemantics
import LeanTrominoes.PeriodicOrthocrossingCarrierCrossingRecordSourceFieldData

/-! # Selecting compact source-key components of padded carrier nodes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNodeSourceKeyCandidateWords

open PaddedSupportedLastRepresentativeEqualityRows

/-- Pair selection turns the two guarded component words of every padded
node into the guarded word of its selected optional source key. -/
theorem selectedWords_componentPairs
    (side : DelimitedBinaryWordPairSelector.Side)
    (candidates : List (Candidate CarrierNode)) :
    DelimitedBinaryWordPairSelector.selectedWords side
        (componentPairs candidates) =
      ⟨(values candidates).map (fun node =>
        CarrierKeyFieldProjector.semanticWord
          (node.map
            (CarrierCrossingRecordSourceField.sourceKey side)))⟩ := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold componentPairs PaddedSupportedLastRepresentativeEqualityRows.values
  induction candidates with
  | nil => rfl
  | cons candidate candidates induction =>
      rcases candidate with ⟨value, supported⟩
      cases value <;> cases side <;>
        simp [DelimitedBinaryWordPairSelector.select, componentPair,
          PaddedSupportedCandidateWords.sentinelWord,
          CarrierCrossingRecordSourceField.sourceKey,
          CarrierKeyFieldProjector.semanticWord, induction]

end CarrierNodeSourceKeyCandidateWords
end LeanTrominoes.PeriodicOrthocrossing
