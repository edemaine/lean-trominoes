/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCrossingActiveCarrierKeyRecipeEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Pair-stream compiler for activity-supported crossing keys -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingActiveCarrierKeyRecipeStream

open Computability Turing

def emittedStream
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd
    CrossingActiveCarrierKeyRecipeEmitter.emittedTokens tokens

noncomputable def emittedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    CrossingActiveCarrierKeyRecipeEmitter.emittedTokensComputableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd

end CrossingActiveCarrierKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing

end
