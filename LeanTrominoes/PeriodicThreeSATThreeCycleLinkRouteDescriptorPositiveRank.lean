/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationData

/-! # Positive target ranks of cycle descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Every cycle-link descriptor has positive target-port rank. -/
theorem cycleLinkRouteDescriptor_targetPortRank_ne_zero
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) {descriptor : RouteDescriptor}
    (descriptorMember : descriptor ∈ cycleLinkRouteDescriptors source) :
    descriptor.targetPortRank ≠ 0 := by
  unfold cycleLinkRouteDescriptors at descriptorMember
  rcases List.mem_map.mp descriptorMember with
    ⟨tagged, _taggedMember, rfl⟩
  simp [cycleLinkRouteDescriptor]

end PeriodicThreeSATThree
end LeanTrominoes
