/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorEnumerationData

/-! # Fixed projections of copied-occurrence route descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Every descriptor in the copied-source prefix has target-port rank zero. -/
theorem occurrenceRouteDescriptor_targetPortRank_eq_zero
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {descriptor : RouteDescriptor}
    (descriptorMember : descriptor ∈ occurrenceRouteDescriptors source) :
    descriptor.targetPortRank = 0 := by
  unfold occurrenceRouteDescriptors at descriptorMember
  rcases List.mem_map.mp descriptorMember with
    ⟨tagged, _taggedMember, rfl⟩
  rfl

end PeriodicThreeSATThree
end LeanTrominoes
