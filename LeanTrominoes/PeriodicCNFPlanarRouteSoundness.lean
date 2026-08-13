/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarCompleteness
import LeanTrominoes.PeriodicOrthocrossingPlanarRouteSoundness

/-!
# Route soundness for CNF incidences

The generic first-to-last propagation theorem specializes directly to the
canonical source and target terminals stored on each metadata-rich CNF
incidence occurrence.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every enumerated metadata-rich incidence occurrence retains the matching
tagged edge of the incidence graph. -/
theorem CNFRouteOccurrence.taggedEdge_mem
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    (occurrence.edge, occurrence.edgeIndex) ∈
      (PeriodicCNF.incidenceGraph formula).edges.zipIdx := by
  rcases List.mem_flatMap.mp occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem, occurrenceMem⟩
  rcases List.mem_map.mp occurrenceMem with
    ⟨translate, translateMem, occurrenceEq⟩
  subst occurrence
  exact PeriodicCNF.tagged_incidence_edge_mem
    formula taggedIncidenceMem

/-- Every enumerated metadata-rich incidence occurrence uses one of the nine
neighboring translations covered by the finite route core. -/
theorem CNFRouteOccurrence.translate_neighbor
    {Variable : Type*}
    (formula : PeriodicCNF Variable)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    IsNeighborTranslation occurrence.translate := by
  rcases List.mem_flatMap.mp occurrenceMem with
    ⟨taggedIncidence, taggedIncidenceMem, occurrenceMem⟩
  rcases List.mem_map.mp occurrenceMem with
    ⟨translate, translateMem, occurrenceEq⟩
  subst occurrence
  exact (mem_neighborTranslations_iff translate).mp
    translateMem

/-- A satisfying incidence-graph route core propagates every routed
literal's value from its canonical clause terminal to its canonical variable
terminal. -/
theorem drawingCNFRoutePlanarCore_source_eq_target
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (assignment :
      Sum CarrierNode (CrossingRecord × CrossoverInternal) → Bool)
    (holds :
      FormulaHolds assignment
        (drawingRoutePlanarCoreFormula
          (PeriodicCNF.incidenceGraph formula)))
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem :
      occurrence ∈ drawingCNFRouteOccurrences formula) :
    assignment
        (.inl (.terminal
          (occurrence.sourceTerminal formula))) =
      assignment
        (.inl (.terminal
          (occurrence.targetTerminal formula))) := by
  have propagated :=
    drawingRoutePlanarCoreFormula_route_terminal_eq
      (PeriodicCNF.incidenceGraph formula)
      assignment holds
      (occurrence.taggedEdge_mem formula occurrenceMem)
      occurrence.translate
      (occurrence.translate_neighbor formula occurrenceMem)
      defaultTaggedGridSegment
  simpa [CNFRouteOccurrence.sourceTerminal,
    CNFRouteOccurrence.targetTerminal,
    CNFRouteOccurrence.taggedSegments,
    CNFRouteOccurrence.edge,
    taggedRouteSegmentTerminal] using propagated

end PeriodicOrthocrossing
end LeanTrominoes
