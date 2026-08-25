/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterComputable
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterPreparedCompiler
import LeanTrominoes.PeriodicOrthocrossingCarrierOrderAffineTerminalAlternativeAlignment
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyRecipeEmitterCompiler

/-! # Guarded-key compiler for direction-split terminal candidates -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalDirectionalCarrierKeyEmitter

open Computability Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def recipes : List Recipe :=
  RouteDescriptorPairAffine.terminalDirectionalCarrierKeyRecipeBlocks.flatten

def preparedInput (tokens : List RouteDescriptorPairFieldTags.Token) :
    List CarrierKeyRecipeEmitter.Token :=
  CarrierKeyRecipeEmitter.preparedFrom id
    RouteDescriptorPairAffine.terminalDirectionalExpandedActives tokens

def emittedTokens (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  CarrierKeyRecipeEmitterMachine.compiledTokens recipes
    (preparedInput tokens)

def preparedInputComputableInPolyTime :
    TM2ComputableInPolyTime id id preparedInput := by
  exact CarrierKeyRecipeEmitter.preparedFromComputableInPolyTime id
    RouteDescriptorPairAffine.terminalDirectionalExpandedActives
    TerminalCarrierKeyRecipeEmitter.identityComputableInPolyTime
    RouteDescriptorPairAffine.terminalDirectionalExpandedActivesComputableInPolyTime

def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => CarrierKeyRecipeEmitterMachine.compiledTokens recipes
      (preparedInput tokens))
  exact TM2CompositionMachine.computableInPolyTime
    preparedInputComputableInPolyTime
    (CarrierKeyRecipeEmitterMachine.computableInPolyTime recipes)

end TerminalDirectionalCarrierKeyEmitter
end LeanTrominoes.PeriodicOrthocrossing

end
