/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceLiteralPortRank
import LeanTrominoes.PeriodicOrthocrossingRouteDescriptorExt
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceRanks
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorData
import LeanTrominoes.PeriodicThreeSATThreeRouteDescriptorHeader
import LeanTrominoes.PeriodicThreeSATThreeRouteDescriptorTargetVertex

/-! # Correctness of copied occurrence route descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- Pointwise lifting preserves every source incidence's global index. -/
theorem occurrenceIncidence_tagged_mem
    {Variable : Type*}
    (source : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMember : tagged ∈
      (PeriodicCNF.incidencesWithMetadata source).zipIdx) :
    (occurrenceIncidence tagged.1, tagged.2) ∈
      (occurrenceIncidences source).zipIdx := by
  apply (List.mem_zipIdx_iff_getElem?).mpr
  unfold occurrenceIncidences
  rw [List.getElem?_map,
    (List.mem_zipIdx_iff_getElem?).mp taggedMember]
  rfl

/-- The explicit copied-source record is exactly the semantic numeric route
descriptor at the same global edge index. -/
theorem occurrenceIncidence_numericRouteDescriptor_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (tagged : CNFIncidence Variable × Nat)
    (taggedMember : tagged ∈
      (PeriodicCNF.incidencesWithMetadata source).zipIdx) :
    (occurrenceIncidence tagged.1).numericRouteDescriptor
        (formula source) tagged.2 =
      occurrenceRouteDescriptor source tagged.1 tagged.2 := by
  have copiedMember :=
    occurrenceIncidence_tagged_mem source tagged taggedMember
  have formulaMember :=
    occurrenceIncidence_tagged_mem_formula source
      (occurrenceIncidence tagged.1, tagged.2) copiedMember
  apply PeriodicOrthocrossing.RouteDescriptor.ext
  · simp [occurrenceRouteDescriptor]
  · simp [occurrenceRouteDescriptor]
  · simp [CNFIncidence.numericRouteDescriptor,
      occurrenceRouteDescriptor]
  · simp [occurrenceRouteDescriptor]
  · rw [numericRouteDescriptor_formula_targetVertexIndex]
    rfl
  · simpa [occurrenceRouteDescriptor] using
      CNFIncidence.numericRouteDescriptor_sourcePortRank_eq_literalIndex
        (formula source)
        (occurrenceIncidence tagged.1, tagged.2) formulaMember
  · simpa [occurrenceRouteDescriptor] using
      occurrenceIncidence_numericRouteDescriptor_targetPortRank
        source (occurrenceIncidence tagged.1, tagged.2) copiedMember
  · simp [CNFIncidence.numericRouteDescriptor,
      occurrenceRouteDescriptor, occurrenceLiteral,
      CNFIncidence.edge_offset]

end PeriodicThreeSATThree
end LeanTrominoes
