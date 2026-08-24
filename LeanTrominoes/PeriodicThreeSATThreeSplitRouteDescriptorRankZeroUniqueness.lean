/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorPositiveRank
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorProjections
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorTargetLookup

/-! # Uniqueness of rank-zero split descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- The occurrence-prefix descriptor at a target vertex is the unique
rank-zero descriptor at that target in the complete split stream. -/
theorem splitRouteDescriptor_rankZero_eq_occurrence
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) {selected second : RouteDescriptor}
    (selectedMember : selected ∈ occurrenceRouteDescriptors source)
    (secondMember : second ∈ splitRouteDescriptors source)
    (secondRankZero : second.targetPortRank = 0)
    (targetEq : selected.targetVertexIndex = second.targetVertexIndex) :
    second = selected := by
  unfold splitRouteDescriptors at secondMember
  rcases List.mem_append.mp secondMember with
    occurrenceMember | cycleMember
  · exact occurrenceRouteDescriptor_eq_of_targetVertexIndex_eq
      source occurrenceMember selectedMember targetEq.symm
  · exact (cycleLinkRouteDescriptor_targetPortRank_ne_zero
      source cycleMember secondRankZero).elim

end PeriodicThreeSATThree
end LeanTrominoes
