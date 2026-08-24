/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterTimeList

/-! # A linear clock for the carrier-key recipe emitter -/

namespace LeanTrominoes.PeriodicOrthocrossing

open Computability

namespace CarrierKeyRecipeEmitterMachine

open RouteDescriptorPairCarrierKeyWordRecipes

/-- A fixed linear clock for one fixed carrier-key recipe list. -/
noncomputable def timePolynomial (recipes : List Recipe) : Polynomial Nat :=
  Polynomial.C (3 * recipes.length + outputWeight recipes + 7) *
    (Polynomial.X + Polynomial.C 1)

@[simp] theorem timePolynomial_eval (recipes : List Recipe) (length : Nat) :
    (timePolynomial recipes).eval length =
      (3 * recipes.length + outputWeight recipes + 7) * (length + 1) := by
  simp [timePolynomial, Polynomial.eval_mul, Polynomial.eval_add]

theorem totalTime_le_polynomial_eval (recipes : List Recipe)
    (input : List CarrierKeyRecipeEmitter.Token) :
    totalTime recipes input ≤
      (timePolynomial recipes).eval input.length := by
  rw [timePolynomial_eval]
  have recipeBound := allRecipeTime_le recipes input
    (scanState (initialState recipes.length) input)
  have firstBound := routeUnits_length_le input
    RouteDescriptorPairFieldTags.Side.first
  have secondBound := routeUnits_length_le input
    RouteDescriptorPairFieldTags.Side.second
  have outputBound := compiledTokens_length_le recipes input
  unfold totalTime prefixTime cleanupTime
  calc
    input.length + 1 +
          allRecipeTime recipes input
            (scanState (initialState recipes.length) input) +
          ((routeUnits input .first).length +
            (routeUnits input .second).length + 2) +
          (compiledTokens recipes input).length + 1 ≤
        input.length + 1 +
          recipes.length * (2 * input.length + 3) +
          (input.length + input.length + 2) +
          (recipes.length * input.length + outputWeight recipes) + 1 := by
      omega
    _ ≤ (3 * recipes.length + outputWeight recipes + 7) *
          (input.length + 1) := by
      nlinarith

end CarrierKeyRecipeEmitterMachine
end LeanTrominoes.PeriodicOrthocrossing
