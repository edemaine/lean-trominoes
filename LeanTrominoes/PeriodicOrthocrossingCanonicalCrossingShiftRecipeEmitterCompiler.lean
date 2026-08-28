/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCanonicalCrossingShiftRecipeActivationCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterComputable
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterPreparedCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairFieldTagFintypeData
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorOccurrenceSlotPairProjectionCompiler

/-! # Compiler for common-shift canonical-left source-key components -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CanonicalCrossingShiftLeftSourceKeyRecipeEmitter

open Computability Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def recipes : List Recipe :=
  RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyRecipeBlocks.flatten

def preparedInput
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List CarrierKeyRecipeEmitter.Token :=
  CarrierKeyRecipeEmitter.preparedFrom
    RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokens
    RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyExpandedActives
    tokens

def emittedTokens
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  CarrierKeyRecipeEmitterMachine.compiledTokens recipes
    (preparedInput tokens)

noncomputable def preparedInputComputableInPolyTime :
    TM2ComputableInPolyTime id id preparedInput :=
  CarrierKeyRecipeEmitter.preparedFromComputableInPolyTime
    RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokens
    RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyExpandedActives
    RouteDescriptorOccurrenceSlotPairFieldTags.descriptorTokensComputableInPolyTime
    RouteDescriptorOccurrenceSlotCrossing.canonicalCrossingShiftLeftSourceKeyExpandedActivesComputableInPolyTime

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => CarrierKeyRecipeEmitterMachine.compiledTokens recipes
      (preparedInput tokens))
  exact TM2CompositionMachine.computableInPolyTime
    preparedInputComputableInPolyTime
    (CarrierKeyRecipeEmitterMachine.computableInPolyTime recipes)

end CanonicalCrossingShiftLeftSourceKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing

end
