/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterMachine

/-! # Configurations of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

structure TapeData where
  input : List CarrierKeyRecipeEmitter.Token
  firstRoute : List Unit
  secondRoute : List Unit
  scratch : List Unit
  outputReverse : List DelimitedBinaryWords.Token
  output : List DelimitedBinaryWords.Token

def tapes (data : TapeData) : ∀ stack, List (Alphabet stack)
  | .input => data.input
  | .firstRoute => data.firstRoute
  | .secondRoute => data.secondRoute
  | .scratch => data.scratch
  | .outputReverse => data.outputReverse
  | .output => data.output

def cfg {recipes : List Recipe} (label : Label recipes)
    (state : State recipes.length) (data : TapeData) :
    TM2.Cfg Alphabet (Label recipes) (State recipes.length) :=
  ⟨some label, state, tapes data⟩

def scanCfg {recipes : List Recipe} (state : State recipes.length)
    (data : TapeData) :=
  cfg (recipes := recipes) .scan state data

def emitCfg {recipes : List Recipe} (index : Fin recipes.length)
    (state : State recipes.length) (data : TapeData) :=
  cfg (.emit index) state data

def scanRouteCfg {recipes : List Recipe} (index : Fin recipes.length)
    (state : State recipes.length) (data : TapeData) :=
  cfg (.scanRoute index) state data

def restoreRouteCfg {recipes : List Recipe}
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) :=
  cfg (.restoreRoute index) state data

def clearFirstRouteCfg {recipes : List Recipe}
    (state : State recipes.length) (data : TapeData) :=
  cfg (recipes := recipes) .clearFirstRoute state data

def clearSecondRouteCfg {recipes : List Recipe}
    (state : State recipes.length) (data : TapeData) :=
  cfg (recipes := recipes) .clearSecondRoute state data

def reverseOutputCfg {recipes : List Recipe}
    (state : State recipes.length) (data : TapeData) :=
  cfg (recipes := recipes) .reverseOutput state data

def haltDataCfg {recipes : List Recipe} (state : State recipes.length)
    (data : TapeData) :
    TM2.Cfg Alphabet (Label recipes) (State recipes.length) :=
  ⟨none, state, tapes data⟩

def beginEmissionCfg (recipes : List Recipe)
    (state : State recipes.length) (data : TapeData) :
    TM2.Cfg Alphabet (Label recipes) (State recipes.length) :=
  if nonempty : 0 < recipes.length then
    emitCfg ⟨0, nonempty⟩ state data
  else
    clearFirstRouteCfg state data

def afterRecipeCfg (recipes : List Recipe)
    (index : Fin recipes.length) (state : State recipes.length)
    (data : TapeData) :
    TM2.Cfg Alphabet (Label recipes) (State recipes.length) :=
  if nextExists : index.val + 1 < recipes.length then
    emitCfg ⟨index.val + 1, nextExists⟩ state data
  else
    clearFirstRouteCfg state data

@[simp] theorem update_tapes_input (data : TapeData)
    (value : List CarrierKeyRecipeEmitter.Token) :
    Function.update (tapes data) Stack.input value =
      tapes { data with input := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_firstRoute (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) Stack.firstRoute value =
      tapes { data with firstRoute := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_secondRoute (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) Stack.secondRoute value =
      tapes { data with secondRoute := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_scratch (data : TapeData)
    (value : List Unit) :
    Function.update (tapes data) Stack.scratch value =
      tapes { data with scratch := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_outputReverse (data : TapeData)
    (value : List DelimitedBinaryWords.Token) :
    Function.update (tapes data) Stack.outputReverse value =
      tapes { data with outputReverse := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

@[simp] theorem update_tapes_output (data : TapeData)
    (value : List DelimitedBinaryWords.Token) :
    Function.update (tapes data) Stack.output value =
      tapes { data with output := value } := by
  funext stack
  cases stack <;> simp [tapes, Function.update]

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
