/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterData

/-! # Delimiters inside tagged descriptor fields -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairFieldTags

theorem taggedFields_continue
    (side : Side) (field : Fin 11) (numbers : List Nat) :
    ∀ token ∈ taggedFields side field numbers,
      isPairEnd token = false := by
  induction numbers generalizing field with
  | nil => simp [taggedFields]
  | cons number numbers induction =>
      intro token member
      rw [taggedFields] at member
      rcases List.mem_append.mp member with replicated | remaining
      · have equal : token = .unit side field :=
          (List.mem_replicate.mp replicated).2
        subst token
        rfl
      · exact induction (nextField field) token remaining

theorem descriptorUnits_continue
    (side : Side) (descriptor : RouteDescriptor) :
    ∀ token ∈ descriptorUnits side descriptor,
      isPairEnd token = false := by
  exact taggedFields_continue side 0 descriptor.unaryFields

end RouteDescriptorPairFieldTags
end PeriodicOrthocrossing
end LeanTrominoes
