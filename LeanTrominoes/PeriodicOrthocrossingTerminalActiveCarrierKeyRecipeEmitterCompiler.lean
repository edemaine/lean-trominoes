/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierActiveKeyRecipeData
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyRecipeEmitterCompiler

/-! # Compiler for activity-supported terminal carrier-key words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalActiveCarrierKeyRecipeEmitter

open Computability Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def recipes : List Recipe :=
  (forceSupportedBlocks
    RouteDescriptorPairAffine.terminalCarrierKeyRecipeBlocks).flatten

def preparedInput (tokens : List RouteDescriptorPairFieldTags.Token) :
    List CarrierKeyRecipeEmitter.Token :=
  TerminalCarrierKeyRecipeEmitter.preparedInput tokens

def emittedTokens (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  CarrierKeyRecipeEmitterMachine.compiledTokens recipes
    (preparedInput tokens)

noncomputable def preparedInputComputableInPolyTime :
    TM2ComputableInPolyTime id id preparedInput :=
  TerminalCarrierKeyRecipeEmitter.preparedInputComputableInPolyTime

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => CarrierKeyRecipeEmitterMachine.compiledTokens recipes
      (preparedInput tokens))
  exact TM2CompositionMachine.computableInPolyTime
    preparedInputComputableInPolyTime
    (CarrierKeyRecipeEmitterMachine.computableInPolyTime recipes)

end TerminalActiveCarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing

end
