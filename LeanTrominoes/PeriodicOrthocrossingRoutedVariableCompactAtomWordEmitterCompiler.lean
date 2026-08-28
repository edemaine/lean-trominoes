/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableCompactAtomWordAlignment
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterComputable
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterPreparedCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairFieldTagFintypeData

/-! # Guarded routed-variable compact-word emission -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace RoutedVariableCompactAtomWordEmitter

open Computability Turing
open RouteDescriptorPairCarrierKeyWordRecipes

/-- The generic emitter's first counter carries the anchor target index;
its second counter carries the selected route index. -/
def indexBlock : RouteDescriptorPairFieldTags.Token →
    List CarrierKeyRecipeEmitter.Token
  | .unit .first field =>
      if field = 4 then [.routeUnit .first] else []
  | .unit .second field =>
      if field = 2 then [.routeUnit .second] else []
  | _ => []

def indexTokens (tokens : List RouteDescriptorPairFieldTags.Token) :
    List CarrierKeyRecipeEmitter.Token :=
  tokens.flatMap indexBlock

def activationTokens (tokens : List RouteDescriptorPairFieldTags.Token) :
    List CarrierKeyRecipeEmitter.Token :=
  CarrierKeyRecipeEmitter.activationTokens
    (RouteDescriptorPairAffine.routedVariableCompactAtomWordExpandedActives
      tokens)

def preparedInput (tokens : List RouteDescriptorPairFieldTags.Token) :
    List CarrierKeyRecipeEmitter.Token :=
  indexTokens tokens ++ activationTokens tokens

def recipes : List Recipe :=
  RouteDescriptorPairAffine.routedVariableCompactAtomWordRecipeBlocks.flatten

def emittedTokens (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  CarrierKeyRecipeEmitterMachine.compiledTokens recipes
    (preparedInput tokens)

noncomputable def indexTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id indexTokens :=
  FiniteBlockTransducer.computableInPolyTime indexBlock

noncomputable def activationTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id activationTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => CarrierKeyRecipeEmitter.activationTokens
      (RouteDescriptorPairAffine.routedVariableCompactAtomWordExpandedActives
        tokens))
  exact TM2CompositionMachine.computableInPolyTime
    RouteDescriptorPairAffine.routedVariableCompactAtomWordExpandedActivesComputableInPolyTime
    CarrierKeyRecipeEmitter.activationTokensComputableInPolyTime

noncomputable def preparedInputComputableInPolyTime :
    TM2ComputableInPolyTime id id preparedInput :=
  TM2ListAppend.nativeComputableInPolyTime
    indexTokensComputableInPolyTime
    activationTokensComputableInPolyTime

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => CarrierKeyRecipeEmitterMachine.compiledTokens recipes
      (preparedInput tokens))
  exact TM2CompositionMachine.computableInPolyTime
    preparedInputComputableInPolyTime
    (CarrierKeyRecipeEmitterMachine.computableInPolyTime recipes)

end RoutedVariableCompactAtomWordEmitter
end LeanTrominoes.PeriodicOrthocrossing

end
