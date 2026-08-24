/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterConfigurations

/-! # Semantic input scan of the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitterMachine

/-- Finite-control effect of consuming one compact input token. -/
def scanToken {recipeCount : Nat} (state : State recipeCount) :
    CarrierKeyRecipeEmitter.Token → State recipeCount
  | .routeUnit _ => clearPayload state
  | .activation active =>
      { actives := FixedLengthWordEvaluator.shiftAppend
          state.actives active
        payload := none }

/-- Finite-control state after consuming a complete compact input. -/
def scanState {recipeCount : Nat} :
    State recipeCount → List CarrierKeyRecipeEmitter.Token →
      State recipeCount
  | state, [] => state
  | state, token :: tokens => scanState (scanToken state token) tokens

theorem clearPayload_eq_self {recipeCount : Nat}
    (state : State recipeCount) (payloadEq : state.payload = none) :
    clearPayload state = state := by
  rcases state with ⟨actives, payload⟩
  change payload = none at payloadEq
  subst payload
  rfl

@[simp] theorem scanToken_payload {recipeCount : Nat}
    (state : State recipeCount)
    (token : CarrierKeyRecipeEmitter.Token) :
    (scanToken state token).payload = none := by
  cases token <;> rfl

@[simp] theorem scanState_payload
    {recipeCount : Nat}
    (state : State recipeCount)
    (input : List CarrierKeyRecipeEmitter.Token)
    (payloadEq : state.payload = none) :
    (scanState state input).payload = none := by
  induction input generalizing state with
  | nil => exact payloadEq
  | cons token input induction =>
      exact induction (scanToken state token) (scanToken_payload state token)

/-- Unary stack content representing one retained route counter. -/
def routeUnits (input : List CarrierKeyRecipeEmitter.Token)
    (side : RouteDescriptorPairFieldTags.Side) : List Unit :=
  List.replicate (CarrierKeyRecipeEmitter.routeCount input side) ()

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
