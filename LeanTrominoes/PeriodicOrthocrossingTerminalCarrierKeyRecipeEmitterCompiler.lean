/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterComputable
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterPreparedCompiler
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairAffineTerminalCarrierKeyWordRecipeActivationCompiler

/-! # Compiler for terminal carrier-key guarded-word blocks -/

noncomputable section

namespace LeanTrominoes.PeriodicOrthocrossing
namespace TerminalCarrierKeyRecipeEmitter

open Computability Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def recipes : List Recipe :=
  RouteDescriptorPairAffine.terminalCarrierKeyRecipeBlocks.flatten

def preparedInput (tokens : List RouteDescriptorPairFieldTags.Token) :
    List CarrierKeyRecipeEmitter.Token :=
  CarrierKeyRecipeEmitter.preparedFrom id
    RouteDescriptorPairAffine.terminalCarrierKeyExpandedActives tokens

def emittedTokens (tokens : List RouteDescriptorPairFieldTags.Token) :
    List DelimitedBinaryWords.Token :=
  CarrierKeyRecipeEmitterMachine.compiledTokens recipes
    (preparedInput tokens)

noncomputable def identityComputableInPolyTime :
    TM2ComputableInPolyTime id id
      (id : List RouteDescriptorPairFieldTags.Token →
        List RouteDescriptorPairFieldTags.Token) := by
  let compiler := FiniteBlockTransducer.computableInPolyTime
    (fun token : RouteDescriptorPairFieldTags.Token => [token])
  refine
    { tm := compiler.tm
      inputAlphabet := compiler.inputAlphabet
      outputAlphabet := compiler.outputAlphabet
      time := compiler.time
      outputsFun := ?_ }
  intro tokens
  have outputEq : tokens.flatMap (fun token => [token]) = id tokens := by
    induction tokens with
    | nil => rfl
    | cons token tokens induction => simp [induction]
  have run := compiler.outputsFun tokens
  rw [outputEq] at run
  exact run

noncomputable def preparedInputComputableInPolyTime :
    TM2ComputableInPolyTime id id preparedInput := by
  exact CarrierKeyRecipeEmitter.preparedFromComputableInPolyTime id
    RouteDescriptorPairAffine.terminalCarrierKeyExpandedActives
    identityComputableInPolyTime
    RouteDescriptorPairAffine.terminalCarrierKeyExpandedActivesComputableInPolyTime

noncomputable def emittedTokensComputableInPolyTime :
    TM2ComputableInPolyTime id id emittedTokens := by
  change TM2ComputableInPolyTime id id
    (fun tokens => CarrierKeyRecipeEmitterMachine.compiledTokens recipes
      (preparedInput tokens))
  exact TM2CompositionMachine.computableInPolyTime
    preparedInputComputableInPolyTime
    (CarrierKeyRecipeEmitterMachine.computableInPolyTime recipes)

end TerminalCarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing

end
