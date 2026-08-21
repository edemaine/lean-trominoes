/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarDegree
import LeanTrominoes.PeriodicOrthocrossingRetainedPeriodicPlanarSATVariablePositions

/-! # Translation-zero variable route sites -/

namespace LeanTrominoes.PeriodicOrthocrossing

/-- For a local incidence graph, an atom occurs in the source formula exactly
when its translation-zero lifted variable site is enumerated by the routed
planar construction. -/
theorem mem_variableOccurrences_iff_zeroSite_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (isLocal : formula.incidenceGraph.IsLocal)
    (atom : Variable) :
    atom ∈ formula.variableOccurrences ↔
      (atom, (0, 0)) ∈ drawingVariableRouteSites formula := by
  constructor
  · intro atomMem
    rw [← PeriodicCNF.incidencesWithMetadata_literal_atoms]
      at atomMem
    rcases List.mem_map.mp atomMem with
      ⟨incidence, incidenceMem, atomEq⟩
    rcases List.mem_iff_getElem.mp incidenceMem with
      ⟨edgeIndex, edgeIndexLt, incidenceAt⟩
    have taggedIncidenceMem :
        (incidence, edgeIndex) ∈
          (PeriodicCNF.incidencesWithMetadata formula).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,
        List.getElem?_eq_some_iff]
      exact ⟨edgeIndexLt, incidenceAt⟩
    have taggedEdgeMem :=
      PeriodicCNF.tagged_incidence_edge_mem
        formula taggedIncidenceMem
    have edgeLocal : incidence.edge.span ≤ 1 :=
      isLocal incidence.edge
        (List.fst_mem_of_mem_zipIdx taggedEdgeMem)
    let canonicalTranslate : Cell :=
      (-incidence.edge.offset.1, -incidence.edge.offset.2)
    let canonicalOccurrence : CNFRouteOccurrence Variable :=
      ⟨incidence, edgeIndex, canonicalTranslate⟩
    have canonicalOccurrenceMem :
        canonicalOccurrence ∈ drawingCNFRouteOccurrences formula := by
      apply List.mem_flatMap.mpr
      refine ⟨(incidence, edgeIndex), taggedIncidenceMem, ?_⟩
      apply List.mem_map.mpr
      refine ⟨canonicalTranslate, ?_, rfl⟩
      apply (mem_neighborTranslations_iff canonicalTranslate).mpr
      exact edgeNegativeOffset_isNeighbor_of_span_le_one
        incidence.edge edgeLocal
    rw [drawingVariableRouteSites, List.mem_dedup]
    apply List.mem_map.mpr
    refine ⟨canonicalOccurrence, canonicalOccurrenceMem, ?_⟩
    simp [canonicalOccurrence, canonicalTranslate,
      CNFRouteOccurrence.variableOccurrence,
      CNFRouteOccurrence.edge, Cell.add, atomEq]
  · intro siteMem
    rw [drawingVariableRouteSites, List.mem_dedup] at siteMem
    rcases List.mem_map.mp siteMem with
      ⟨occurrence, occurrenceMem, siteEq⟩
    rcases List.mem_flatMap.mp occurrenceMem with
      ⟨taggedIncidence, taggedIncidenceMem,
        translatedOccurrenceMem⟩
    rcases List.mem_map.mp translatedOccurrenceMem with
      ⟨translate, _, occurrenceEq⟩
    subst occurrence
    rw [← PeriodicCNF.incidencesWithMetadata_literal_atoms]
    apply List.mem_map.mpr
    refine
      ⟨taggedIncidence.1,
        List.fst_mem_of_mem_zipIdx taggedIncidenceMem, ?_⟩
    simpa [CNFRouteOccurrence.variableOccurrence] using
      congrArg Prod.fst siteEq

end LeanTrominoes.PeriodicOrthocrossing
