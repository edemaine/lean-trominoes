/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFSourceOccurrenceTargetVertexIndexSemantics
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceAtoms
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorEnumerationData

/-! # Target fields of compiled source occurrence route descriptors -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace SourceOccurrenceTargetVertexIndices

/-- The compiled stream lists the target variable-vertex index of every
positional source occurrence, in presentation order. -/
theorem indices_eq_allOccurrenceVariableTargets
    (source : SourceSplitRouteDescriptorTokens.Source) :
    indices source =
      (PeriodicThreeSATThree.allOccurrenceVariables source.formula).map
        fun copy =>
          (PeriodicThreeSATThree.rotatedOccurrenceVariables
            source.formula).idxOf copy := by
  apply List.ext_getElem?
  intro index
  cases copyLookup :
      (PeriodicThreeSATThree.allOccurrenceVariables
        source.formula)[index]? with
  | none =>
      rw [indices_getElem?]
      have atomLookup :
          (SourceOccurrenceAtomRanks.occurrenceAtoms
            source.formula)[index]? = none := by
        rw [SourceOccurrenceAtomRanks.occurrenceAtoms_eq_allOccurrenceVariables_fst,
          List.getElem?_map, copyLookup]
        rfl
      rw [atomLookup, List.getElem?_map, copyLookup]
      rfl
  | some copy =>
      have copyMember : (copy, index) ∈
          (PeriodicThreeSATThree.allOccurrenceVariables
            source.formula).zipIdx :=
        (List.mem_zipIdx_iff_getElem?).mpr copyLookup
      rw [indices_getElem?_eq_copy_target source
        (copy, index) copyMember,
        List.getElem?_map, copyLookup]
      rfl

/-- Equivalently, the compiled values are exactly the target-vertex fields of
the occurrence-prefix route descriptors. -/
theorem indices_eq_occurrenceRouteDescriptor_targetVertexIndices
    (source : SourceSplitRouteDescriptorTokens.Source) :
    indices source =
      (PeriodicThreeSATThree.occurrenceRouteDescriptors
        source.formula).map
          (fun descriptor => descriptor.targetVertexIndex) := by
  rw [indices_eq_allOccurrenceVariableTargets]
  have copiesEq :
      PeriodicThreeSATThree.allOccurrenceVariables source.formula =
        (PeriodicCNF.incidencesWithMetadata source.formula).map
          fun incidence =>
            (incidence.literal.atom, incidence.clauseIndex,
              incidence.literalIndex) := by
    rw [← PeriodicThreeSATThree.occurrenceIncidences_atoms]
    simp only [PeriodicThreeSATThree.occurrenceIncidences, List.map_map,
      Function.comp_def,
      PeriodicThreeSATThree.occurrenceIncidence_atom]
  rw [copiesEq, PeriodicThreeSATThree.occurrenceRouteDescriptors]
  conv_lhs =>
    rw [← List.zipIdx_map_fst 0
      (PeriodicCNF.incidencesWithMetadata source.formula)]
  simp only [List.map_map, Function.comp_def,
    PeriodicThreeSATThree.occurrenceRouteDescriptor]

end SourceOccurrenceTargetVertexIndices
end PeriodicCNF
end LeanTrominoes
