/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorTargetBounds
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorTargetLookup

/-! # Occurrence descriptors matched to cycle targets -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Every cycle descriptor has a matching occurrence-prefix descriptor at
the same target vertex. -/
theorem exists_occurrenceRouteDescriptor_for_cycleTarget
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) {cycle : RouteDescriptor}
    (cycleMember : cycle ∈ cycleLinkRouteDescriptors source) :
    ∃ occurrence ∈ occurrenceRouteDescriptors source,
      cycle.targetVertexIndex = occurrence.targetVertexIndex := by
  rcases exists_occurrenceRouteDescriptor_targetVertexIndex
      source cycle.targetVertexIndex
      (cycleLinkRouteDescriptor_targetVertexIndex_lt
        source cycleMember) with
    ⟨occurrence, occurrenceMember, occurrenceTarget⟩
  exact ⟨occurrence, occurrenceMember, occurrenceTarget.symm⟩

end PeriodicThreeSATThree
end LeanTrominoes
