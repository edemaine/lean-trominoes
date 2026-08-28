/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFIncidenceRouteDescriptorEnumerationData
import LeanTrominoes.PeriodicThreeSATThreeCycleLinkRouteDescriptorSemantics
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorSemantics
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationData

/-! # Correctness of the complete explicit split descriptor stream -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

/-- The complete explicit copied-plus-cycle stream is exactly the semantic
numeric route-descriptor enumeration of the occurrence-split formula. -/
theorem numericRouteDescriptors_formula_eq_splitRouteDescriptors
    {Variable : Type*} [DecidableEq Variable]
    [DecidableEq (ThreeOccurrenceVariable Variable)]
    (source : PeriodicCNF Variable) :
    PeriodicCNF.numericRouteDescriptors (formula source) =
      splitRouteDescriptors source := by
  have occurrenceIndices :
      (occurrenceIncidences source).zipIdx =
        (PeriodicCNF.incidencesWithMetadata source).zipIdx.map
          (fun tagged =>
            (occurrenceIncidence tagged.1, tagged.2)) := by
    unfold occurrenceIncidences
    rw [List.zipIdx_map]
    apply List.map_congr_left
    intro tagged taggedMember
    cases tagged
    rfl
  unfold PeriodicCNF.numericRouteDescriptors splitRouteDescriptors
  rw [formula_incidencesWithMetadata_eq_occurrence_append_cycle]
  rw [← cycleLinkIncidences_eq_cycleIncidences]
  rw [List.zipIdx_append, List.map_append]
  congr 1
  · rw [occurrenceIndices, List.map_map]
    unfold occurrenceRouteDescriptors
    apply List.map_congr_left
    intro tagged taggedMember
    rcases tagged with ⟨incidence, edgeIndex⟩
    change (occurrenceIncidence incidence).numericRouteDescriptor
      (formula source) edgeIndex =
        occurrenceRouteDescriptor source incidence edgeIndex
    exact occurrenceIncidence_numericRouteDescriptor_eq
      source (incidence, edgeIndex) taggedMember
  · rw [occurrenceIncidences_length]
    rw [List.zipIdx_eq_map_add, List.map_map]
    unfold cycleLinkRouteDescriptors
    apply List.map_congr_left
    intro tagged taggedMember
    rcases tagged with ⟨incidence, localIndex⟩
    simp only [Function.comp_apply, Nat.zero_add]
    exact cycleLinkIncidence_numericRouteDescriptor_eq
      source (incidence, localIndex) taggedMember

end PeriodicThreeSATThree
end LeanTrominoes
