/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataAffineBendCompactAtomWordAlignment
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterComputable
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterPreparedCompiler
import LeanTrominoes.PeriodicOrthocrossingTerminalCarrierKeyRecipeEmitterCompiler

/-! # Guarded compact-word recipe emitter for affine bends -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace BendCompactAtomWordEmitter

open Computability Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def recipes : List Recipe :=
  RouteDescriptorPairAffine.bendCompactAtomWordRecipeBlocks.flatten

def preparedInput (tokens : List RouteDescriptorPairFieldTags.Token) :
    List CarrierKeyRecipeEmitter.Token :=
  CarrierKeyRecipeEmitter.preparedFrom id
    RouteDescriptorPairAffine.bendCompactAtomWordExpandedActives tokens

def emittedTokens (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  CarrierKeyRecipeEmitterMachine.compiledTokens recipes
    (preparedInput tokens)

noncomputable def preparedInputComputableInPolyTime :
    TM2ComputableInPolyTime id id preparedInput := by
  exact CarrierKeyRecipeEmitter.preparedFromComputableInPolyTime id
    RouteDescriptorPairAffine.bendCompactAtomWordExpandedActives
    TerminalCarrierKeyRecipeEmitter.identityComputableInPolyTime
    RouteDescriptorPairAffine.bendCompactAtomWordExpandedActivesComputableInPolyTime

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => CarrierKeyRecipeEmitterMachine.compiledTokens recipes
      (preparedInput tokens))
  exact TM2CompositionMachine.computableInPolyTime
    preparedInputComputableInPolyTime
    (CarrierKeyRecipeEmitterMachine.computableInPolyTime recipes)

end BendCompactAtomWordEmitter
end LeanTrominoes.PeriodicOrthocrossing

end
