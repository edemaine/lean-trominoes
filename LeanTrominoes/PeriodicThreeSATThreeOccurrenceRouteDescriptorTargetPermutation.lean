/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListMapIdxOfSelfBEq
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorTargetVertexProjection
import LeanTrominoes.PeriodicThreeSATThreeRotatedOccurrenceVariablesBasic

/-! # Occurrence descriptor target-index permutation -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- The occurrence-prefix descriptors target every rotated occurrence-copy
vertex exactly once. -/
theorem occurrenceRouteDescriptors_targetVertexIndices_perm_range
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((occurrenceRouteDescriptors source).map
      RouteDescriptor.targetVertexIndex).Perm
        (List.range (PeriodicCNF.presentationLiteralCount source)) := by
  have sameMembers : ∀ copy,
      copy ∈ allOccurrenceVariables source ↔
        copy ∈ rotatedOccurrenceVariables source := by
    intro copy
    rw [← cycleLinkIncidences_atoms_dedup_eq_rotatedOccurrenceVariables,
      List.mem_dedup, mem_cycleLinkIncidenceAtoms_iff]
  have copiesPerm : (allOccurrenceVariables source).Perm
      (rotatedOccurrenceVariables source) :=
    (List.perm_ext_iff_of_nodup
      (allOccurrenceVariables_nodup source)
      (rotatedOccurrenceVariables_nodup source)).mpr sameMembers
  rw [occurrenceRouteDescriptors_targetVertexIndices]
  have mappedPerm := copiesPerm.map (fun copy =>
    (rotatedOccurrenceVariables source).idxOf copy)
  rw [List.map_idxOf_self_eq_range_beq _
      (rotatedOccurrenceVariables_nodup source),
    rotatedOccurrenceVariables_length] at mappedPerm
  exact mappedPerm

/-- Consequently, occurrence descriptor target indices are duplicate-free. -/
theorem occurrenceRouteDescriptors_targetVertexIndices_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((occurrenceRouteDescriptors source).map
      RouteDescriptor.targetVertexIndex).Nodup :=
  (occurrenceRouteDescriptors_targetVertexIndices_perm_range source).nodup_iff.mpr
    List.nodup_range

end PeriodicThreeSATThree
end LeanTrominoes
