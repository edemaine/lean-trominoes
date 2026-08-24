/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeRotatedOccurrenceVariablesBasic
import LeanTrominoes.PeriodicThreeSATThreeSplitRouteDescriptorEnumerationData

/-! # Target-index bounds of cycle descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Every cycle descriptor targets a valid rotated occurrence-copy index. -/
theorem cycleLinkRouteDescriptor_targetVertexIndex_lt
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) {descriptor : RouteDescriptor}
    (descriptorMember : descriptor ∈ cycleLinkRouteDescriptors source) :
    descriptor.targetVertexIndex <
      PeriodicCNF.presentationLiteralCount source := by
  unfold cycleLinkRouteDescriptors at descriptorMember
  rcases List.mem_map.mp descriptorMember with
    ⟨tagged, taggedMember, rfl⟩
  have incidenceMember : tagged.1 ∈ cycleLinkIncidences source :=
    List.fst_mem_of_mem_zipIdx taggedMember
  have atomOriginal : tagged.1.literal.atom ∈
      allOccurrenceVariables source :=
    cycleLinkIncidence_atom_mem_allOccurrenceVariables
      source tagged.1 incidenceMember
  have atomRotated : tagged.1.literal.atom ∈
      rotatedOccurrenceVariables source := by
    rw [← cycleLinkIncidences_atoms_dedup_eq_rotatedOccurrenceVariables,
      List.mem_dedup, mem_cycleLinkIncidenceAtoms_iff]
    exact atomOriginal
  simp only [cycleLinkRouteDescriptor]
  rw [← rotatedOccurrenceVariables_length source]
  exact (@List.idxOf_lt_length_iff
    (ThreeOccurrenceVariable Variable)
    instBEqOfDecidableEq (by infer_instance)
    (rotatedOccurrenceVariables source)
    tagged.1.literal.atom).mpr atomRotated

end PeriodicThreeSATThree
end LeanTrominoes
