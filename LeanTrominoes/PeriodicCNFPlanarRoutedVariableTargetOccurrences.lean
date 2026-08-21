/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarOccurrences
import LeanTrominoes.PeriodicCNFPlanarDegree
import LeanTrominoes.PlanarThreeSATEqualityEndpointOccurrences

/-! # Target-terminal occurrences in routed variable gadgets -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- For an occurrence-three presentation, every neighboring incidence-route
target is one of the three active routed-variable equality arms and therefore
occurs in the complete routed-variable formula. -/
theorem targetTerminal_mem_drawingRoutedVariableFormula
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (occurrences : formula.OccurrencesAtMost 3)
    {occurrence : CNFRouteOccurrence Variable}
    (occurrenceMem : occurrence ∈ drawingCNFRouteOccurrences formula) :
    (PlanarSATNode.carrier
        (.terminal (occurrence.targetTerminal formula)) :
      PlanarSATNode Variable) ∈
        embeddedVariableOccurrences
          (drawingRoutedVariableFormula formula) := by
  let site := occurrence.variableOccurrence
  let node : PlanarSATNode Variable :=
    .carrier (.terminal (occurrence.targetTerminal formula))
  let nodes := routedVariableNodes formula site
  have siteMem : site ∈ drawingVariableRouteSites formula := by
    simp only [drawingVariableRouteSites, List.mem_dedup, List.mem_map]
    exact ⟨occurrence, occurrenceMem, rfl⟩
  have occurrenceAtMem :
      occurrence ∈ variableRouteOccurrencesAt formula site := by
    simp [variableRouteOccurrencesAt, site, occurrenceMem]
  have nodeMem : node ∈ nodes := by
    apply List.mem_dedup.mpr
    exact List.mem_map.mpr ⟨occurrence, occurrenceAtMem, rfl⟩
  have lengthLe : nodes.length ≤ 3 := by
    calc
      nodes.length ≤
          ((variableRouteOccurrencesAt formula site).map fun routed =>
            (PlanarSATNode.carrier
              (.terminal (routed.targetTerminal formula)) :
              PlanarSATNode Variable)).length := by
        exact List.Sublist.length_le (List.dedup_sublist _)
      _ ≤ 3 := by
        simpa using variableRouteOccurrencesAt_length_le_three
          formula occurrences site
  have nodeTakeMem : node ∈ nodes.take 3 := by
    rw [List.take_of_length_le lengthLe]
    exact nodeMem
  have firstMem :
      node ∈ (drawingRoutedVariableLinks formula).map EqualityLink.first := by
    rw [drawingRoutedVariableLinks_firsts]
    apply List.mem_flatMap.mpr
    exact ⟨site, siteMem, nodeTakeMem⟩
  rcases List.mem_map.mp firstMem with ⟨link, linkMem, firstEq⟩
  have occurrenceInFamily :=
    EqualityLink.first_mem_embeddedVariableOccurrences_equalityFamily
      linkMem
  rw [firstEq] at occurrenceInFamily
  rw [drawingRoutedVariableFormula_eq_equalityFamily]
  exact occurrenceInFamily

end LeanTrominoes.PeriodicOrthocrossing
