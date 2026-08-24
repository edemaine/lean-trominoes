/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingCarrierNodeKeyShiftTemplateSemantics

/-! # Carrier-key projection of crossing-node occurrence blocks -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

@[simp] theorem map_carrierKey_occurrencePairCrossingCarrierNodeTemplateBlock
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) :
    (occurrencePairCrossingCarrierNodeTemplateBlock
        pair occurrences).map
        (Template.mapValue CarrierNode.carrierKey) =
      occurrencePairCrossingCarrierKeyTemplateBlock
        pair occurrences := by
  unfold occurrencePairCrossingCarrierNodeTemplateBlock
    occurrencePairCrossingCarrierKeyTemplateBlock
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro shift _shiftMember
  exact map_carrierKey_occurrencePairCrossingCarrierNodeShiftTemplateBlock
    pair occurrences shift

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
