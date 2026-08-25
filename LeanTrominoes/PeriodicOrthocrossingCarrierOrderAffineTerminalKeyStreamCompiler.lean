/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalKeyEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterData
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Pair-stream compiler for direction-split terminal keys -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalDirectionalCarrierKeyStream

open Computability Turing

def emittedStream (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorPairFieldTags.isPairEnd
    TerminalDirectionalCarrierKeyEmitter.emittedTokens tokens

def emittedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    TerminalDirectionalCarrierKeyEmitter.emittedTokensComputableInPolyTime
    RouteDescriptorPairFieldTags.isPairEnd

end TerminalDirectionalCarrierKeyStream
end LeanTrominoes.PeriodicOrthocrossing

end
