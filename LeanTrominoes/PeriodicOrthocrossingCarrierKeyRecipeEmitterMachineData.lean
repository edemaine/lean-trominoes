/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.FixedLengthWordEvaluator
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterData

/-! # Machine data for compact carrier-key recipe emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open RouteDescriptorPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes

/-- Four fixed fields after the dynamically copied route-index units. -/
def fixedSuffixBits (recipe : Recipe) : List Bool :=
  true :: CarrierKeyWords.natField recipe.segmentIndex ++
    CarrierKeyWords.intField recipe.translate.1 ++
      CarrierKeyWords.intField recipe.translate.2

/-- Delimited prefix of an active guarded carrier-key word. -/
def activePrefixTokens : List DelimitedBinaryWords.Token :=
  [.wordStart, .bit true]

/-- Fixed suffix and closing delimiter of an active guarded word. -/
def activeSuffixTokens (recipe : Recipe) :
    List DelimitedBinaryWords.Token :=
  (fixedSuffixBits recipe).map .bit ++ [.wordEnd]

/-- Complete common rejection-sentinel token block. -/
def sentinelTokens : List DelimitedBinaryWords.Token :=
  DelimitedBinaryWords.wordTokens
    PaddedSupportedCandidateWords.sentinelWord

/-- Physical active word assembled from the retained unary route counter and
one fixed recipe suffix. -/
def activeTokens (input : List CarrierKeyRecipeEmitter.Token)
    (recipe : Recipe) : List DelimitedBinaryWords.Token :=
  activePrefixTokens ++
    List.replicate (CarrierKeyRecipeEmitter.routeCount input recipe.side)
      (.bit false) ++
    activeSuffixTokens recipe

/-- Physical block selected by one activation/recipe pair. -/
def tokenBlock (input : List CarrierKeyRecipeEmitter.Token)
    (active : Bool) (recipe : Recipe) :
    List DelimitedBinaryWords.Token :=
  if active && recipe.supported then activeTokens input recipe
  else sentinelTokens

/-- Complete physical stream specified by a compact emitter input. -/
def emittedTokens (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) :
    List DelimitedBinaryWords.Token :=
  (List.zipWith (tokenBlock input)
    (CarrierKeyRecipeEmitter.activationBits input) recipes).flatten

inductive Stack
  | input
  | firstRoute
  | secondRoute
  | scratch
  | outputReverse
  | output
  deriving DecidableEq, Fintype

inductive Label (recipes : List Recipe)
  | scan
  | emit (index : Fin recipes.length)
  | scanRoute (index : Fin recipes.length)
  | restoreRoute (index : Fin recipes.length)
  | reverseOutput
  deriving Fintype

inductive Payload
  | input (token : CarrierKeyRecipeEmitter.Token)
  | unit
  | output (token : DelimitedBinaryWords.Token)
  deriving DecidableEq, Fintype

/-- The fixed activation vector remains in finite control throughout all
route-stack rescans. -/
structure State (recipeCount : Nat) where
  actives : List.Vector Bool recipeCount
  payload : Option Payload
  deriving DecidableEq, Fintype

abbrev Alphabet : Stack → Type
  | .input => CarrierKeyRecipeEmitter.Token
  | .firstRoute | .secondRoute | .scratch => Unit
  | .outputReverse | .output => DelimitedBinaryWords.Token

def initialState (recipeCount : Nat) : State recipeCount :=
  { actives := List.Vector.replicate recipeCount false
    payload := none }

def clearPayload {recipeCount : Nat} (state : State recipeCount) :
    State recipeCount :=
  { state with payload := none }

def readInput {recipeCount : Nat} (state : State recipeCount) :
    Option CarrierKeyRecipeEmitter.Token → State recipeCount
  | none => clearPayload state
  | some token => { state with payload := some (.input token) }

def readUnit {recipeCount : Nat} (state : State recipeCount) :
    Option Unit → State recipeCount
  | none => clearPayload state
  | some _ => { state with payload := some .unit }

def readOutput {recipeCount : Nat} (state : State recipeCount) :
    Option DelimitedBinaryWords.Token → State recipeCount
  | none => clearPayload state
  | some token => { state with payload := some (.output token) }

def payloadPresent {recipeCount : Nat} (state : State recipeCount) : Bool :=
  state.payload.isSome

def isRouteUnit {recipeCount : Nat} (side : Side)
    (state : State recipeCount) : Bool :=
  match state.payload with
  | some (.input (.routeUnit tokenSide)) => decide (tokenSide = side)
  | _ => false

def isActivation {recipeCount : Nat} (state : State recipeCount) : Bool :=
  match state.payload with
  | some (.input (.activation _)) => true
  | _ => false

def storeActivation {recipeCount : Nat} (state : State recipeCount) :
    State recipeCount :=
  match state.payload with
  | some (.input (.activation active)) =>
      { actives := FixedLengthWordEvaluator.shiftAppend
          state.actives active
        payload := none }
  | _ => clearPayload state

def activeAt (recipes : List Recipe) (state : State recipes.length)
    (index : Fin recipes.length) : Bool :=
  state.actives.get index && (recipes.get index).supported

def routeStack : Side → Stack
  | .first => .firstRoute
  | .second => .secondRoute

def outputFromState {recipeCount : Nat} (state : State recipeCount) :
    DelimitedBinaryWords.Token :=
  match state.payload with
  | some (.output token) => token
  | _ => default

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
