/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipeStreamCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipeStreamData
import LeanTrominoes.PeriodicOrthocrossingCarrierSourceKeyComponentStreamData

/-! # Complete normalized carrier source-key component stream data -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyComponentStream

open RouteDescriptorOccurrenceSlotBinaryWords

def terminalTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  CarrierNormalizedSourceKeyRecipeStream.terminalEmittedStream
    (CarrierSourceKeyComponentStream.terminalTags input)

def crossingTokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  CarrierNormalizedSourceKeyRecipeStream.crossingEmittedStream
    (CarrierSourceKeyComponentStream.crossingTags input)

def tokens (input : DelimitedBinaryWords.Input) :
    List DelimitedBinaryWords.Token :=
  terminalTokens input ++ crossingTokens input

def guardedWords (descriptors : List RouteDescriptor) : List (List Bool) :=
  CarrierNormalizedSourceKeyRecipeStream.terminalGuardedWords
      (descriptors ×ˢ descriptors) ++
    CarrierNormalizedSourceKeyRecipeStream.crossingGuardedWords
      (taggedDescriptors descriptors ×ˢ taggedDescriptors descriptors)

end CarrierNormalizedSourceKeyComponentStream
end LeanTrominoes.PeriodicOrthocrossing
