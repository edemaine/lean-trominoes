/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingOccurrencePairCarrierKeyOrderData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeySlotData

/-! # Terminal carrier-key template values -/

namespace LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine

open PaddedSupportedCandidateBlocks

/-- The values in one fixed terminal template block are exactly the two
semantic terminal-key copies of each neighboring occurrence. -/
theorem Segment.terminalCarrierKeyTemplateBlock_values
    (pair : RouteDescriptor × RouteDescriptor)
    (segmentIndex : Nat) (segment : Segment) :
    (segment.terminalCarrierKeyTemplateBlock
        pair segmentIndex).map Template.value =
      occurrenceTerminalCarrierKeys
        (neighborTranslations.map fun translate =>
          ((⟨pair.1.edgeIndex, segmentIndex,
              segment.evalPair pair⟩ : IndexedGridSegment), translate)) := by
  unfold Segment.terminalCarrierKeyTemplateBlock
    occurrenceTerminalCarrierKeys
  rw [List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro translate _translateMember
  rfl

end LeanTrominoes.PeriodicOrthocrossing.RouteDescriptorPairAffine
