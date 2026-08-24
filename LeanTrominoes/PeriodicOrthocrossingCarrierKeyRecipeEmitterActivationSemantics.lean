/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingCarrierKeyRecipeEmitterData

/-! # Activation semantics of compact carrier-key recipe preparation -/

namespace LeanTrominoes.PeriodicOrthocrossing
namespace CarrierKeyRecipeEmitter

theorem activation_routeBlock_nil
    (tokens : List RouteDescriptorPairFieldTags.Token) :
    activationBits (tokens.flatMap routeBlock) = [] := by
  induction tokens with
  | nil => rfl
  | cons token tokens induction =>
      cases token with
      | pairStart => simpa [routeBlock, activationBits] using induction
      | pairEnd => simpa [routeBlock, activationBits] using induction
      | unit side field =>
          by_cases fieldEq : field = 2
          · subst field
            simpa [routeBlock, activationBits] using induction
          · simpa [routeBlock, fieldEq, activationBits] using induction

@[simp] theorem activationBits_prepared
    (tokens : List RouteDescriptorPairFieldTags.Token)
    (actives : List Bool) :
    activationBits (prepared tokens actives) = actives := by
  unfold prepared activationBits
  rw [List.filterMap_append]
  change activationBits (tokens.flatMap routeBlock) ++ _ = _
  rw [activation_routeBlock_nil]
  simp

end CarrierKeyRecipeEmitter
end LeanTrominoes.PeriodicOrthocrossing
