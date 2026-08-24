/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.ListFlatMapKeyNodup
import LeanTrominoes.ListZipIdxFstMembership
import LeanTrominoes.PeriodicThreeSATThreeVariableRouteSiteArmBlocks

/-! # Semantic routed-variable arm scan over boundary sites -/

namespace LeanTrominoes.PeriodicThreeSATThree

open PeriodicOrthocrossing PlanarThreeSAT
open PeriodicCNF.FormulaShapeRetainedPlanarMetadataDirection

/-- Boundary-only copied-incidence site blocks are duplicate-free because
their positional occurrence atoms are unique. -/
theorem occurrenceBoundaryVariableRouteSites_nodup
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (occurrenceBoundaryVariableRouteSites source).Nodup := by
  unfold occurrenceBoundaryVariableRouteSites
  apply flatMap_nodup_of_map_key_nodup
    (occurrenceIncidences source)
    (fun incidence => incidence.literal.atom)
    Prod.fst
    (fun incidence =>
      if incidence.edge.offset = (1, 0) then
        nextBoundaryVariableRouteSiteBlock incidence.literal.atom
      else [])
  · rw [occurrenceIncidences_atoms]
    exact allOccurrenceVariables_nodup source
  · intro incidence _incidenceMember
    by_cases offsetOne : Cell.sub incidence.literal.offset
        (PeriodicCNF.clauseAnchor incidence.clause) = (1, 0) <;>
      simp [offsetOne]
  · intro incidence _incidenceMember site siteMember
    by_cases offsetOne : Cell.sub incidence.literal.offset
        (PeriodicCNF.clauseAnchor incidence.clause) = (1, 0)
    · simp only [CNFIncidence.edge_offset, offsetOne, if_pos] at siteMember
      rw [nextBoundaryVariableRouteSiteBlock_eq] at siteMember
      simp only [List.mem_cons, List.not_mem_nil, or_false] at siteMember
      rcases siteMember with rfl | rfl | rfl <;> rfl
    · simp [CNFIncidence.edge_offset, offsetOne] at siteMember

/-- Mapping the deduplicated boundary site stream produces three singleton
left-arm sites for each next-slice copied incidence, in incidence order. -/
theorem occurrenceBoundaryVariableRouteSites_numericArms_eq
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    ((occurrenceBoundaryVariableRouteSites source).dedup).map
        (fun site =>
          ((variableRouteOccurrencesAt (formula source) site).take 3).map
            (fun occurrence =>
              targetDuplicatorArm
                (occurrence.incidence.numericRouteDescriptor
                  (formula source) occurrence.edgeIndex).targetPortRank)) =
      (occurrenceIncidences source).flatMap fun incidence =>
        if incidence.edge.offset = (1, 0) then
          routedVariableNextBoundarySiteArmBlocks
        else
          [] := by
  rw [List.dedup_eq_self.mpr
    (occurrenceBoundaryVariableRouteSites_nodup source)]
  unfold occurrenceBoundaryVariableRouteSites
  rw [List.map_flatMap]
  apply List.flatMap_congr
  intro incidence incidenceMember
  by_cases offsetOne : incidence.edge.offset = (1, 0)
  · simp only [offsetOne, if_pos]
    rcases exists_mem_zipIdx_fst
        (occurrenceIncidences source) 0 incidenceMember with
      ⟨index, selectedMember⟩
    exact nextOccurrenceVariableRouteBoundarySiteArmBlock_eq
      source (incidence, index) selectedMember offsetOne
  · have offsetOne' : ¬Cell.sub incidence.literal.offset
        (PeriodicCNF.clauseAnchor incidence.clause) = (1, 0) := by
      simpa only [CNFIncidence.edge_offset] using offsetOne
    simp [offsetOne']

end LeanTrominoes.PeriodicThreeSATThree
