/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrencePositiveOffsets
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorEnumerationData

/-! # Horizontal offsets of copied-occurrence route descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Every copied-occurrence route descriptor of a zero-anchored
forward-local source stays in the current slice or points to the next
slice. -/
theorem occurrenceRouteDescriptors_offset_zero_or_one
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (forward : source.IsForwardLocal)
    (zeroAnchored : source.IsZeroAnchored) :
    ∀ descriptor ∈ occurrenceRouteDescriptors source,
      descriptor.offset = (0, 0) ∨ descriptor.offset = (1, 0) := by
  intro descriptor descriptorMember
  unfold occurrenceRouteDescriptors at descriptorMember
  rcases List.mem_map.mp descriptorMember with
    ⟨taggedIncidence, taggedMember, rfl⟩
  have copiedMember : occurrenceIncidence taggedIncidence.1 ∈
      occurrenceIncidences source := by
    unfold occurrenceIncidences
    exact List.mem_map.mpr
      ⟨taggedIncidence.1,
        List.fst_mem_of_mem_zipIdx taggedMember, rfl⟩
  have offsetCases := occurrenceIncidences_edge_offset_zero_or_one
    source forward zeroAnchored
    (occurrenceIncidence taggedIncidence.1) copiedMember
  simpa only [occurrenceRouteDescriptor, CNFIncidence.edge_offset,
    occurrenceIncidence_literal_offset, occurrenceIncidence_clause,
    clauseAnchor_occurrenceClause] using offsetCases

end PeriodicThreeSATThree
end LeanTrominoes
