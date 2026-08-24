/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterMachineData

/-! # Finite machine for compact carrier-key recipe emission -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

open Computability StateTransition Turing
open RouteDescriptorPairCarrierKeyWordRecipes

def pushTokens {recipes : List Recipe}
    (tokens : List DelimitedBinaryWords.Token)
    (next : TM2.Stmt Alphabet (Label recipes) (State recipes.length)) :
    TM2.Stmt Alphabet (Label recipes) (State recipes.length) :=
  tokens.foldr
    (fun token continuation =>
      .push .outputReverse (fun _ => token) continuation)
    next

def beginEmission (recipes : List Recipe) :
    TM2.Stmt Alphabet (Label recipes) (State recipes.length) :=
  if nonempty : 0 < recipes.length then
    .goto fun _ => .emit ⟨0, nonempty⟩
  else
    .goto fun _ => .reverseOutput

def afterRecipe (recipes : List Recipe)
    (index : Fin recipes.length) :
    TM2.Stmt Alphabet (Label recipes) (State recipes.length) :=
  if nextExists : index.val + 1 < recipes.length then
    .goto fun _ => .emit ⟨index.val + 1, nextExists⟩
  else
    .goto fun _ => .reverseOutput

def program (recipes : List Recipe) :
    Label recipes → TM2.Stmt Alphabet (Label recipes)
      (State recipes.length)
  | .scan =>
      .pop .input readInput
        (.branch payloadPresent
          (.branch (isRouteUnit .first)
            (.push .firstRoute (fun _ => ())
              (.load clearPayload (.goto fun _ => .scan)))
            (.branch (isRouteUnit .second)
              (.push .secondRoute (fun _ => ())
                (.load clearPayload (.goto fun _ => .scan)))
              (.branch isActivation
                (.load storeActivation (.goto fun _ => .scan))
                (.load clearPayload (.goto fun _ => .scan)))))
          (beginEmission recipes))
  | .emit index =>
      .branch (fun state => activeAt recipes state index)
        (pushTokens activePrefixTokens
          (.goto fun _ => .scanRoute index))
        (pushTokens sentinelTokens (afterRecipe recipes index))
  | .scanRoute index =>
      match (recipes.get index).side with
      | .first =>
          .pop .firstRoute readUnit
            (.branch payloadPresent
              (.push .scratch (fun _ => ())
                (.push .outputReverse
                  (fun _ => DelimitedBinaryWords.Token.bit false)
                  (.load clearPayload
                    (.goto fun _ => .scanRoute index))))
              (.goto fun _ => .restoreRoute index))
      | .second =>
          .pop .secondRoute readUnit
            (.branch payloadPresent
              (.push .scratch (fun _ => ())
                (.push .outputReverse
                  (fun _ => DelimitedBinaryWords.Token.bit false)
                  (.load clearPayload
                    (.goto fun _ => .scanRoute index))))
              (.goto fun _ => .restoreRoute index))
  | .restoreRoute index =>
      match (recipes.get index).side with
      | .first =>
          .pop .scratch readUnit
            (.branch payloadPresent
              (.push .firstRoute (fun _ => ())
                (.load clearPayload
                  (.goto fun _ => .restoreRoute index)))
              (pushTokens (activeSuffixTokens (recipes.get index))
                (afterRecipe recipes index)))
      | .second =>
          .pop .scratch readUnit
            (.branch payloadPresent
              (.push .secondRoute (fun _ => ())
                (.load clearPayload
                  (.goto fun _ => .restoreRoute index)))
              (pushTokens (activeSuffixTokens (recipes.get index))
                (afterRecipe recipes index)))
  | .reverseOutput =>
      .pop .outputReverse readOutput
        (.branch payloadPresent
          (.push .output outputFromState
            (.load clearPayload (.goto fun _ => .reverseOutput)))
          .halt)

abbrev machine (recipes : List Recipe) : FinTM2 where
  K := Stack
  k₀ := .input
  k₁ := .output
  Γ := Alphabet
  Λ := Label recipes
  main := .scan
  σ := State recipes.length
  initialState := initialState recipes.length
  m := program recipes

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
