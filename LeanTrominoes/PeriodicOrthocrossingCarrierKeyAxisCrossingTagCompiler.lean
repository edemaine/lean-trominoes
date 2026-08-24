/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotPairProductCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagCompiler
import LeanTrominoes.TM2CompositionMachine

/-! # Crossing-slot-pair tags for the carrier-key axis compiler -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyAxisCrossingTags

open Computability Turing

def tags (input : DelimitedBinaryWords.Input) :
    List RouteDescriptorOccurrenceSlotPairFieldTags.Token :=
  RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens
    (DelimitedBinaryWordOccurrenceSlotTags.expandedPairs input)

noncomputable def tagsComputableInPolyTime :
    TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
      tags := by
  change TM2ComputableInPolyTime DelimitedBinaryWords.finEncoding.encode id
    (fun input => RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens
      (DelimitedBinaryWordOccurrenceSlotTags.expandedPairs input))
  exact TM2CompositionMachine.computableInPolyTime
    DelimitedBinaryWordOccurrenceSlotTags.expandedPairsComputableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.inputTokensComputableInPolyTime

end CarrierKeyAxisCrossingTags
end LeanTrominoes.PeriodicOrthocrossing

end
