/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterScannedOutputSemantics

/-! # Named data for complete carrier-key recipe-emitter execution -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- The output produced for an arbitrary compact input.  The finite-control
activation word determines how many input activation bits are retained. -/
def compiledTokens (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) :
    List DelimitedBinaryWords.Token :=
  allRecipeTokens recipes input
    (scanState (initialState recipes.length) input)

def initialData (input : List CarrierKeyRecipeEmitter.Token) : TapeData :=
  ⟨input, [], [], [], [], []⟩

def scannedData (input : List CarrierKeyRecipeEmitter.Token) : TapeData :=
  ⟨[], routeUnits input .first, routeUnits input .second, [], [], []⟩

def emittedData (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) : TapeData :=
  { scannedData input with
    outputReverse := (compiledTokens recipes input).reverse }

def clearedData (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) : TapeData :=
  { emittedData recipes input with
    firstRoute := []
    secondRoute := [] }

def prefixTime (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) : Nat :=
  input.length + 1 +
    allRecipeTime recipes input
      (scanState (initialState recipes.length) input)

def cleanupTime (input : List CarrierKeyRecipeEmitter.Token) : Nat :=
  (routeUnits input .first).length +
    (routeUnits input .second).length + 2

def totalTime (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) : Nat :=
  prefixTime recipes input + cleanupTime input +
    (compiledTokens recipes input).length + 1

@[simp] theorem compiledTokens_eq_emittedTokens
    (recipes : List Recipe) (input : List CarrierKeyRecipeEmitter.Token)
    (lengthEq : (CarrierKeyRecipeEmitter.activationBits input).length =
      recipes.length) :
    compiledTokens recipes input = emittedTokens recipes input := by
  exact allRecipeTokens_scanState recipes input lengthEq

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
