/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordCleanupCompiler
import LeanTrominoes.PeriodicOrthocrossingRoutedVariableCompactAtomWordEmitterCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterData
import LeanTrominoes.TM2CompositionMachine
import LeanTrominoes.TM2EndDelimitedBlockMapCompiler

/-! # Pair-stream compiler for exact routed-variable compact atom words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RoutedVariableCompactAtomWordStream

open Computability Turing

def emittedTokens (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  RoutedVariableCompactAtomWordCleanup.tokens
    (RoutedVariableCompactAtomWordEmitter.emittedTokens tokens)

def emittedStream (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  TM2EndDelimitedBlockMap.mappedOutput
    RouteDescriptorPairFieldTags.isPairEnd emittedTokens tokens

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => RoutedVariableCompactAtomWordCleanup.tokens
      (RoutedVariableCompactAtomWordEmitter.emittedTokens tokens))
  exact TM2CompositionMachine.computableInPolyTime
    RoutedVariableCompactAtomWordEmitter.emittedTokensComputableInPolyTime
    RoutedVariableCompactAtomWordCleanup.tokensComputableInPolyTime

noncomputable def emittedStreamComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedStream :=
  TM2EndDelimitedBlockMap.computableInPolyTime
    emittedTokensComputableInPolyTime RouteDescriptorPairFieldTags.isPairEnd

end RoutedVariableCompactAtomWordStream
end LeanTrominoes.PeriodicOrthocrossing

end
