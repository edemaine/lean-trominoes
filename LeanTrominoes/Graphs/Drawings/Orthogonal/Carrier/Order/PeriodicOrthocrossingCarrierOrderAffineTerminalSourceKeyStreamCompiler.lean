/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.Carrier.Order.PeriodicOrthocrossingCarrierOrderAffineTerminalSourceKeyEmitterCompiler
import LeanTrominoes.Graphs.Drawings.Orthogonal.Route.PeriodicOrthocrossingRouteDescriptorPairDelimiterData
import LeanTrominoes.Computation.TM2.TM2EndDelimitedBlockMapCompiler

/-! # Pair-stream compiler for direction-split terminal source components -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalDirectionalSourceKeyStream

open Computability Turing

def emittedStream (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorPairFieldTags.isPairEnd
    TerminalDirectionalSourceKeyEmitter.emittedTokens tokens

def emittedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    TerminalDirectionalSourceKeyEmitter.emittedTokensComputableInPolyTime
    RouteDescriptorPairFieldTags.isPairEnd

end TerminalDirectionalSourceKeyStream
end LeanTrominoes.PeriodicOrthocrossing

end
