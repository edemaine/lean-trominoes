/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Normalized.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipeCompiler
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairBlockMapSemantics
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorPairDelimiterData
import LeanTrominoes.Computation.TM2.TM2EndDelimitedBlockMapCompiler

/-! # Pair-stream compilers for normalized carrier source-key recipes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRecipeStream

open Computability Turing

def terminalEmittedStream
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorPairFieldTags.isPairEnd
    CarrierNormalizedSourceKeyRecipes.terminalEmittedTokens tokens

noncomputable def terminalEmittedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id terminalEmittedStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    CarrierNormalizedSourceKeyRecipes.terminalEmittedTokensComputableInPolyTime
    RouteDescriptorPairFieldTags.isPairEnd

def crossingEmittedStream
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd
    CarrierNormalizedSourceKeyRecipes.crossingEmittedTokens tokens

noncomputable def crossingEmittedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id crossingEmittedStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    CarrierNormalizedSourceKeyRecipes.crossingEmittedTokensComputableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.isPairEnd

end CarrierNormalizedSourceKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing

end
