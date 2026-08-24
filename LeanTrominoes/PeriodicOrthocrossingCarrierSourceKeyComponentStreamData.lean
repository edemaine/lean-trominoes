/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWordOccurrenceSlotPairProductCompiler
import LeanTrominoes.PeriodicOrthocrossingCrossingSourceKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeStreamCompiler

/-! # Complete doubled source-key component stream data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierSourceKeyComponentStream

local instance : Inhabited DelimitedBinaryWords.finEncoding.Γ :=
  ⟨DelimitedBinaryWords.Token.wordStart⟩

def terminalTags (input : DelimitedBinaryWords.Input) :
    List RouteDescriptorPairFieldTags.Token :=
  RouteDescriptorPairFieldTags.inputTokens
    (DelimitedBinaryWordPairProductMachine.pairs input)

def crossingTags (input : DelimitedBinaryWords.Input) :
    List RouteDescriptorOccurrenceSlotPairFieldTags.Token :=
  RouteDescriptorOccurrenceSlotPairFieldTags.inputTokens
    (DelimitedBinaryWordOccurrenceSlotTags.expandedPairs input)

def terminalTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  TerminalSourceKeyRecipeStream.emittedStream (terminalTags input)

def crossingTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  CrossingSourceKeyRecipeStream.emittedStream (crossingTags input)

def tokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  terminalTokens input ++ crossingTokens input

end CarrierSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
