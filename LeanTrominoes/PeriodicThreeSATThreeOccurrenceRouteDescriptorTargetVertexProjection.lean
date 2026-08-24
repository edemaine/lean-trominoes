/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceAtoms
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorEnumerationData

/-! # Target-index projection of occurrence descriptors -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Occurrence descriptor target indices are the rotated-list indices of
the positional copies in source presentation order. -/
theorem occurrenceRouteDescriptors_targetVertexIndices
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (occurrenceRouteDescriptors source).map
        RouteDescriptor.targetVertexIndex =
      (allOccurrenceVariables source).map fun copy =>
        (rotatedOccurrenceVariables source).idxOf copy := by
  have copiesEq : allOccurrenceVariables source =
      (PeriodicCNF.incidencesWithMetadata source).map fun incidence =>
        (incidence.literal.atom, incidence.clauseIndex,
          incidence.literalIndex) := by
    rw [← occurrenceIncidences_atoms]
    simp only [occurrenceIncidences, List.map_map,
      Function.comp_def, occurrenceIncidence_atom]
  rw [copiesEq]
  unfold occurrenceRouteDescriptors
  rw [List.map_map]
  simp only [Function.comp_def, occurrenceRouteDescriptor]
  calc
    ((PeriodicCNF.incidencesWithMetadata source).zipIdx).map
        (fun tagged =>
          (rotatedOccurrenceVariables source).idxOf
            (tagged.1.literal.atom, tagged.1.clauseIndex,
              tagged.1.literalIndex)) =
      (((PeriodicCNF.incidencesWithMetadata source).zipIdx).map
        Prod.fst).map (fun incidence =>
          (rotatedOccurrenceVariables source).idxOf
            (incidence.literal.atom, incidence.clauseIndex,
              incidence.literalIndex)) := by
              rw [List.map_map]
              rfl
    _ = (PeriodicCNF.incidencesWithMetadata source).map
        (fun incidence =>
          (rotatedOccurrenceVariables source).idxOf
            (incidence.literal.atom, incidence.clauseIndex,
              incidence.literalIndex)) := by
              rw [List.zipIdx_map_fst]
    _ = _ := by
      rw [List.map_map]
      rfl

end PeriodicThreeSATThree
end LeanTrominoes
