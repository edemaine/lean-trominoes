/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineCrossingCarrierKeySlotData

/-! # Crossing carrier-key template values -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

/-- The values of one fixed retention-shift template are its exact graph-free
four-key occurrence-pair block. -/
theorem occurrencePairCrossingCarrierKeyShiftTemplateBlock_values
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) (shift : Cell) :
    (occurrencePairCrossingCarrierKeyShiftTemplateBlock
        pair occurrences shift).map Template.value =
      occurrencePairCarrierKeyShiftBlock
        (occurrences.1.evalPair .first pair,
          occurrences.2.evalPair .second pair) shift := by
  rfl

/-- Flattening all retention-shift template values for one fixed affine
occurrence pair gives its exact graph-free retained carrier-key block. -/
theorem occurrencePairCrossingCarrierKeyTemplateBlock_values
    (pair : RouteDescriptor × RouteDescriptor)
    (occurrences : Occurrence × Occurrence) :
    (occurrencePairCrossingCarrierKeyTemplateBlock
        pair occurrences).map Template.value =
      occurrencePairCarrierKeyBlock
        (occurrences.1.evalPair .first pair,
          occurrences.2.evalPair .second pair) := by
  unfold occurrencePairCrossingCarrierKeyTemplateBlock
    occurrencePairCarrierKeyBlock
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro shift _shiftMember
  exact occurrencePairCrossingCarrierKeyShiftTemplateBlock_values
    pair occurrences shift

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
