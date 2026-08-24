/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterComputable
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterPreparedCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagFintypeData
import LeanTrominoes.PeriodicOrthocrossingTerminalSourceKeyRecipeActivationCompiler

/-! # Compiler for doubled terminal source-key guarded words -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalSourceKeyRecipeEmitter

open Computability Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def recipes : List Recipe :=
  RouteDescriptorPairAffine.terminalSourceKeyRecipeBlocks.flatten

def preparedInput (tokens : List RouteDescriptorPairFieldTags.Token) :
    List CarrierKeyRecipeEmitter.Token :=
  CarrierKeyRecipeEmitter.preparedFrom id
    RouteDescriptorPairAffine.terminalSourceKeyExpandedActives tokens

def emittedTokens (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  CarrierKeyRecipeEmitterMachine.compiledTokens recipes
    (preparedInput tokens)

noncomputable def preparedInputComputableInPolyTime :
    TM2ComputableInPolyTime id id preparedInput :=
  CarrierKeyRecipeEmitter.preparedFromComputableInPolyTime id
    RouteDescriptorPairAffine.terminalSourceKeyExpandedActives
    PeriodicCNF.AffineEmitterPipeline.identityComputableInPolyTime
    RouteDescriptorPairAffine.terminalSourceKeyExpandedActivesComputableInPolyTime

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => CarrierKeyRecipeEmitterMachine.compiledTokens recipes
      (preparedInput tokens))
  exact TM2CompositionMachine.computableInPolyTime
    preparedInputComputableInPolyTime
    (CarrierKeyRecipeEmitterMachine.computableInPolyTime recipes)

end TerminalSourceKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing

end
