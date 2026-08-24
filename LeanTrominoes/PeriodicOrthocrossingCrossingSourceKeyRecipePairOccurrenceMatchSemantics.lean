/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListForall2Append
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipePairShiftMatchSemantics

/-! # Alignment of one occurrence pair's crossing source-key recipes -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RouteDescriptorPairAffine

open RouteDescriptorPairSourceKeyRecipePairs
open RouteDescriptorPairFieldTags

theorem occurrencePairCrossingSourceKeyRecipePairBlock_matchesNode
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) :
    List.Forall₂ (MatchesNode (descriptorPairTokens pair))
      (occurrencePairCrossingSourceKeyRecipePairBlock occurrences)
      (occurrencePairCrossingCarrierNodeTemplateBlock pair occurrences) := by
  unfold occurrencePairCrossingSourceKeyRecipePairBlock
    occurrencePairCrossingCarrierNodeTemplateBlock
  induction carrierCrossingRetentionShifts with
  | nil => simp
  | cons shift shifts induction =>
      rw [List.flatMap_cons, List.flatMap_cons]
      exact
        (occurrencePairCrossingSourceKeyShiftRecipePairBlock_matchesNode
          pair occurrences shift).append induction

end RouteDescriptorPairAffine
end LeanTrominoes.PeriodicOrthocrossing
