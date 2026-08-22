/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterTokenSemantics
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorPairDelimiterBodyData

/-! # Final delimiter of a descriptor-pair body -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing
namespace RouteDescriptorPairFieldTags

@[simp] theorem descriptorPairTokens_eq_body
    (pair : RouteDescriptor × RouteDescriptor) :
    descriptorPairTokens pair = descriptorPairBody pair ++ [.pairEnd] := by
  simp [descriptorPairTokens, descriptorPairBody, List.append_assoc]

theorem descriptorPairBody_continue
    (pair : RouteDescriptor × RouteDescriptor) :
    ∀ token ∈ descriptorPairBody pair,
      isPairEnd token = false := by
  intro token member
  simp only [descriptorPairBody, List.mem_cons,
    List.mem_append] at member
  rcases member with start | first | second
  · subst token
    rfl
  · exact descriptorUnits_continue .first pair.1 token first
  · exact descriptorUnits_continue .second pair.2 token second

end RouteDescriptorPairFieldTags
end PeriodicOrthocrossing
end LeanTrominoes
