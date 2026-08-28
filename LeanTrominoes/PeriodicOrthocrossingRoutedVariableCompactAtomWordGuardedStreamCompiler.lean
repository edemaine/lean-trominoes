/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterData
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Pair-stream compiler for guarded routed-variable compact atom words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RoutedVariableCompactAtomWordGuardedStream

open Computability Turing

def emittedStream (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorPairFieldTags.isPairEnd
    RoutedVariableCompactAtomWordEmitter.emittedTokens tokens

noncomputable def emittedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    RoutedVariableCompactAtomWordEmitter.emittedTokensComputableInPolyTime
    RouteDescriptorPairFieldTags.isPairEnd

end RoutedVariableCompactAtomWordGuardedStream
end LeanTrominoes.PeriodicOrthocrossing

end
