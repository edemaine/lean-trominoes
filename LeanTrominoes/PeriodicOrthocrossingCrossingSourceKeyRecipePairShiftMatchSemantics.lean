/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairMatchSemantics

/-! # Alignment of one shifted crossing source-key recipe-pair block -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs
open RouteDescriptorPairFieldTags

theorem occurrencePairCrossingSourceKeyShiftRecipePairBlock_matchesNode
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    List.Forall₂ (MatchesNode (descriptorPairTokens pair))
      (occurrencePairCrossingSourceKeyShiftRecipePairBlock
        occurrences shift)
      (occurrencePairCrossingCarrierNodeShiftTemplateBlock
        pair occurrences shift) := by
  unfold occurrencePairCrossingSourceKeyShiftRecipePairBlock
    occurrencePairCrossingCarrierNodeShiftTemplateBlock
  dsimp only
  exact List.Forall₂.cons
    (occurrencePairCrossingSourceKeyRecipePair_matchesNode
      pair occurrences shift .left
      (occurrences.1.carrierKeyAtShiftSupported shift))
    (List.Forall₂.cons
      (occurrencePairCrossingSourceKeyRecipePair_matchesNode
        pair occurrences shift .right
        (occurrences.1.carrierKeyAtShiftSupported shift))
      (List.Forall₂.cons
        (occurrencePairCrossingSourceKeyRecipePair_matchesNode
          pair occurrences shift .top
          (occurrences.2.carrierKeyAtShiftSupported shift))
        (List.Forall₂.cons
          (occurrencePairCrossingSourceKeyRecipePair_matchesNode
            pair occurrences shift .bottom
            (occurrences.2.carrierKeyAtShiftSupported shift))
          List.Forall₂.nil)))

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
