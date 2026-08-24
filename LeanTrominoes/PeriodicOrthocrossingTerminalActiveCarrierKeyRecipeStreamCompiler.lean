/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterData
import LeanTrominoes.PeriodicOrthocrossingTerminalActiveCarrierKeyRecipeEmitterCompiler
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Pair-stream compiler for activity-supported terminal keys -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalActiveCarrierKeyRecipeStream

open Computability Turing

def emittedStream (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorPairFieldTags.isPairEnd
    TerminalActiveCarrierKeyRecipeEmitter.emittedTokens tokens

noncomputable def emittedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    TerminalActiveCarrierKeyRecipeEmitter.emittedTokensComputableInPolyTime
    RouteDescriptorPairFieldTags.isPairEnd

end TerminalActiveCarrierKeyRecipeStream
end LeanTrominoes.PeriodicOrthocrossing

end
