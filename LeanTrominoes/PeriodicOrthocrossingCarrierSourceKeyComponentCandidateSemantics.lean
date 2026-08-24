/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamSemanticData
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyCandidateStreamPairSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyCandidateStreamPairSemantics

/-! # Complete source-key components as padded node candidates -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyComponentStream

theorem componentWords_paddedCarrierNodeCandidateStream
    (descriptors : List RouteDescriptor) :
    DelimitedBinaryWordGuardedPairMerge.componentWords
        (CarrierNodeSourceKeyCandidateWords.componentPairs
          (paddedCarrierNodeCandidateStream descriptors)) =
      ⟨guardedWords descriptors⟩ := by
  apply congrArg DelimitedBinaryWords.Input.mk
  unfold paddedCarrierNodeCandidateStream guardedWords
    CarrierNodeSourceKeyCandidateWords.componentPairs
  rw [List.map_append, List.flatMap_append]
  exact congrArg₂ (fun first second => first ++ second)
    (congrArg DelimitedBinaryWords.Input.words
      (RouteDescriptorPairAffine.componentWords_paddedTerminalCarrierNodeCandidateStream
        descriptors))
    (congrArg DelimitedBinaryWords.Input.words
      (RouteDescriptorOccurrenceSlotCrossing.componentWords_paddedCrossingCarrierNodeCandidateStream
        descriptors))

end CarrierSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
