/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNodeSourceKeyCandidateWordData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorCarrierNodeCandidateStreamData

/-! # Semantic descriptor-list output of the merged source-key stream -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyMergedStream

def descriptorOutput (descriptors : List RouteDescriptor) :
    DelimitedBinaryWords.Input :=
  CarrierNodeSourceKeyCandidateWords.mergedWords
    (paddedCarrierNodeCandidateStream descriptors)

end CarrierSourceKeyMergedStream
end LeanTrominoes.PeriodicOrthocrossing
