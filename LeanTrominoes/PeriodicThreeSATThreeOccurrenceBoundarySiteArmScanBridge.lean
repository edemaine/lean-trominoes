/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedVariableSiteArmScanData
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceData
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceRouteDescriptorEnumerationData

/-! # Boundary arm scan bridge from descriptors to copied incidences -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Testing occurrence-descriptor offset one is the same as testing the
corresponding copied incidence, after erasing presentation indices. -/
theorem occurrenceRouteDescriptors_boundarySiteArmBlocks_eq_incidences
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((occurrenceRouteDescriptors source).flatMap fun descriptor =>
        if descriptor.offset = ((1, 0) : Cell) then
          routedVariableNextBoundarySiteArmBlocks else []) =
      ((occurrenceIncidences source).flatMap fun incidence =>
        if incidence.edge.offset = ((1, 0) : Cell) then
          routedVariableNextBoundarySiteArmBlocks else []) := by
  unfold occurrenceRouteDescriptors occurrenceIncidences
  rw [List.flatMap_map, List.flatMap_map]
  calc
    _ = (PeriodicCNF.incidencesWithMetadata source).zipIdx.flatMap
          (fun taggedIncidence =>
            if taggedIncidence.1.edge.offset = ((1, 0) : Cell) then
              routedVariableNextBoundarySiteArmBlocks else []) := by
        apply List.flatMap_congr
        intro taggedIncidence _taggedMember
        have offsetEq :
            (occurrenceRouteDescriptor source taggedIncidence.1
                taggedIncidence.2).offset =
              taggedIncidence.1.edge.offset := by
          unfold occurrenceRouteDescriptor
          rw [CNFIncidence.edge_offset]
        rw [offsetEq]
    _ = (PeriodicCNF.incidencesWithMetadata source).flatMap
          (fun incidence =>
            if incidence.edge.offset = ((1, 0) : Cell) then
              routedVariableNextBoundarySiteArmBlocks else []) :=
        PeriodicCNF.zipIdx_flatMap_fst
          (fun incidence : CNFIncidence Variable =>
            if incidence.edge.offset = ((1, 0) : Cell) then
              routedVariableNextBoundarySiteArmBlocks else [])
          (PeriodicCNF.incidencesWithMetadata source) 0
    _ = _ := by
      apply List.flatMap_congr
      intro incidence _incidenceMember
      have offsetEq : (occurrenceIncidence incidence).edge.offset =
          incidence.edge.offset := by
        rw [CNFIncidence.edge_offset, CNFIncidence.edge_offset,
          occurrenceIncidence_literal_offset,
          occurrenceIncidence_clause,
          clauseAnchor_occurrenceClause]
      rw [offsetEq]

end LeanTrominoes.PeriodicThreeSATThree
