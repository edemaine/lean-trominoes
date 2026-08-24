/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.DelimitedBinaryWords
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairCarrierKeyWordRecipeData

/-! # Compact input data for carrier-key recipe emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitter

open RouteDescriptorPairFieldTags
open RouteDescriptorPairCarrierKeyWordRecipes

/-- The emitter retains only the two unbounded route-index fields and one
fixed-length activation word. -/
inductive Token
  | routeUnit (side : Side)
  | activation (active : Bool)
  deriving DecidableEq, Fintype, Inhabited

/-- Keep precisely the unary units of field two, which stores a route index. -/
def routeBlock : RouteDescriptorPairFieldTags.Token → List Token
  | .unit side field =>
      if field = 2 then [.routeUnit side] else []
  | _ => []

/-- Compact pair data followed by its flattened recipe activations. -/
def prepared (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) : List Token :=
  tokens.flatMap routeBlock ++ actives.map .activation

/-- Recover the activation suffix of a compact emitter input. -/
def activationBits (input : List Token) : List Bool :=
  input.filterMap fun
    | .activation active => some active
    | .routeUnit _ => none

/-- Count the retained route-index units on one side. -/
def routeCount (input : List Token) (side : Side) : Nat :=
  input.count (.routeUnit side)

/-- Interpret one recipe from compact emitter input. -/
def preparedKey (input : List Token) (recipe : Recipe) :
    CarrierKeyWords.CarrierKey :=
  (routeCount input recipe.side, recipe.segmentIndex, recipe.translate)

/-- Guarded word emitted from compact input for one activation/recipe pair. -/
def preparedWord (input : List Token)
    (active : Bool) (recipe : Recipe) : List Bool :=
  if active && recipe.supported then
    true :: CarrierKeyWords.word (preparedKey input recipe)
  else
    PaddedSupportedCandidateWords.sentinelWord

/-- Emit the activation-aligned fixed recipe list. -/
def words (recipes : List Recipe) (input : List Token) : List (List Bool) :=
  List.zipWith (preparedWord input)
    (activationBits input) recipes

/-- Semantic delimited-word output of the compact emitter. -/
def output (recipes : List Recipe) (input : List Token) :
    DelimitedBinaryWords.Input :=
  ⟨words recipes input⟩

end CarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
