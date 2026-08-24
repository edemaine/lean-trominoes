/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterComputable
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterPreparedCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotCrossingCarrierKeyWordRecipeActivationCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionCompiler

/-! # Compiler for crossing carrier-key guarded-word blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CrossingCarrierKeyRecipeEmitter

open Computability Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def recipes : List Recipe :=
  RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyRecipeBlocks.flatten

def preparedInput
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List CarrierKeyRecipeEmitter.Token :=
  CarrierKeyRecipeEmitter.preparedFrom
    RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokens
    RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyExpandedActives
    tokens

def emittedTokens
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  CarrierKeyRecipeEmitterMachine.compiledTokens recipes
    (preparedInput tokens)

noncomputable def preparedInputComputableInPolyTime :
    TM2ComputableInPolyTime id id preparedInput := by
  exact CarrierKeyRecipeEmitter.preparedFromComputableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokens
    RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyExpandedActives
    RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokensComputableInPolyTime
    RouteDescriptorOccurrenceSlotCrossing.crossingCarrierKeyExpandedActivesComputableInPolyTime

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => CarrierKeyRecipeEmitterMachine.compiledTokens recipes
      (preparedInput tokens))
  exact TM2CompositionMachine.computableInPolyTime
    preparedInputComputableInPolyTime
    (CarrierKeyRecipeEmitterMachine.computableInPolyTime recipes)

end CrossingCarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing

end
