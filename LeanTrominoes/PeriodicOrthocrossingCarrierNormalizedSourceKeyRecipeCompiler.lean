/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierNormalizedSourceKeyRecipeData

/-! # Compilers for fixed normalized carrier source-key recipes -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierNormalizedSourceKeyRecipes

open Computability Turing

def terminalEmittedTokens
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  CarrierKeyRecipeEmitterMachine.compiledTokens terminalRecipes
    (TerminalSourceKeyRecipeEmitter.preparedInput tokens)

noncomputable def terminalEmittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id terminalEmittedTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => CarrierKeyRecipeEmitterMachine.compiledTokens
      terminalRecipes (TerminalSourceKeyRecipeEmitter.preparedInput tokens))
  exact TM2CompositionMachine.computableInPolyTime
    TerminalSourceKeyRecipeEmitter.preparedInputComputableInPolyTime
    (CarrierKeyRecipeEmitterMachine.computableInPolyTime terminalRecipes)

def crossingEmittedTokens
    (tokens : List RouteDescriptorOccurrenceSlotPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  CarrierKeyRecipeEmitterMachine.compiledTokens crossingRecipes
    (CrossingSourceKeyRecipeEmitter.preparedInput tokens)

noncomputable def crossingEmittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id crossingEmittedTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => CarrierKeyRecipeEmitterMachine.compiledTokens
      crossingRecipes (CrossingSourceKeyRecipeEmitter.preparedInput tokens))
  exact TM2CompositionMachine.computableInPolyTime
    CrossingSourceKeyRecipeEmitter.preparedInputComputableInPolyTime
    (CarrierKeyRecipeEmitterMachine.computableInPolyTime crossingRecipes)

end CarrierNormalizedSourceKeyRecipes
end LeanTrominoes.PeriodicOrthocrossing

end
