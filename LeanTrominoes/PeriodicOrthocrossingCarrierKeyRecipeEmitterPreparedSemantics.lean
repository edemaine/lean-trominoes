/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterData

/-! # Semantics of compact carrier-key recipe preparation -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitter

open RouteDescriptorPairFieldTags

theorem routeBlock_count (tokens : List RouteDescriptorPairFieldTags.Token)
    (side : Side) :
    (tokens.flatMap routeBlock).count (.routeUnit side) =
      tokens.count (.unit side 2) := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      cases token with
      | pairStart => simpa [routeBlock] using induction
      | pairEnd => simpa [routeBlock] using induction
      | unit tokenSide field =>
          by_cases fieldEq : field = 2
          · subst field
            cases tokenSide <;> cases side <;>
              simp [routeBlock, induction]
          · simp [routeBlock, fieldEq, induction]

theorem activation_route_count_zero (actives : List Bool) (side : Side) :
    (actives.map Token.activation).count (.routeUnit side) = 0 := by
  induction actives with
  | nil => rfl
  | cons active actives induction => simp [induction]

@[simp] theorem routeCount_prepared
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) (side : Side) :
    routeCount (prepared tokens actives) side =
      tokenFieldValue tokens side 2 := by
  unfold routeCount prepared tokenFieldValue
  rw [List.count_append, routeBlock_count,
    activation_route_count_zero, Nat.add_zero]

end CarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
