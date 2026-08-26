/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicThreeSATThreeRoutedVariableRotatedEdgeIndexDedup
import LeanTrominoes.PeriodicThreeSATThreeOccurrenceIncidenceAtomLookup

/-! # Boundary routed-variable edge indices are later representatives -/

namespace LeanTrominoes
namespace PeriodicThreeSATThree

open PeriodicOrthocrossing

/-- Route indices selected by the boundary-only site prefix. -/
def boundaryRoutedVariableEdgeIndexScan
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) : List Nat :=
  ((occurrenceBoundaryVariableRouteSites source).dedup).flatMap fun site =>
    ((variableRouteOccurrencesAt (formula source) site).take 3).map
      CNFRouteOccurrence.edgeIndex

/-- Every boundary-only site belongs to a genuine positional occurrence
that appears later in rotated cycle order. -/
theorem occurrenceBoundaryVariableRouteSite_atom_mem_rotated
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {site : VariableRouteSite (ThreeOccurrenceVariable Variable)}
    (siteMember : site ∈ occurrenceBoundaryVariableRouteSites source) :
    site.1 ∈ rotatedOccurrenceVariables source := by
  unfold occurrenceBoundaryVariableRouteSites at siteMember
  rcases List.mem_flatMap.mp siteMember with
    ⟨incidence, incidenceMember, blockMember⟩
  have offsetOne : incidence.edge.offset = (1, 0) := by
    by_contra offsetNotOne
    rw [if_neg offsetNotOne] at blockMember
    simp at blockMember
  rw [if_pos offsetOne] at blockMember
  have siteAtomEq : site.1 = incidence.literal.atom := by
    rw [nextBoundaryVariableRouteSiteBlock_eq] at blockMember
    simp only [List.mem_cons, List.not_mem_nil, or_false] at blockMember
    rcases blockMember with rfl | rfl | rfl <;> rfl
  rw [mem_rotatedOccurrenceVariables_iff_allOccurrenceVariables,
    siteAtomEq]
  rw [← occurrenceIncidences_atoms]
  exact List.mem_map_of_mem incidenceMember

/-- Every route index in the boundary prefix occurs again in the canonical
final-site fiber of the same positional occurrence. -/
theorem boundaryRoutedVariableEdgeIndexScan_subset_canonical
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (positiveOffsets : ∀ incidence ∈ occurrenceIncidences source,
      incidence.edge.offset = (0, 0) ∨
        incidence.edge.offset = (1, 0)) :
    boundaryRoutedVariableEdgeIndexScan source ⊆
      canonicalRoutedVariableEdgeIndexScan source := by
  intro edgeIndex edgeIndexMember
  rcases List.mem_flatMap.mp edgeIndexMember with
    ⟨site, siteMember, siteEdgeMember⟩
  have siteMember' : site ∈ occurrenceBoundaryVariableRouteSites source :=
    List.mem_dedup.mp siteMember
  have atomMember :=
    occurrenceBoundaryVariableRouteSite_atom_mem_rotated
      source siteMember'
  rcases List.mem_map.mp siteEdgeMember with
    ⟨occurrence, occurrenceMember, rfl⟩
  have occurrenceMember' : occurrence ∈
      variableRouteOccurrencesAt (formula source) site :=
    List.mem_of_mem_take occurrenceMember
  have edgeMember : occurrence.edgeIndex ∈
      (variableRouteOccurrencesAt (formula source) site).map
        CNFRouteOccurrence.edgeIndex :=
    List.mem_map.mpr ⟨occurrence, occurrenceMember', rfl⟩
  have finalMember :=
    variableRouteOccurrenceEdgeIndices_subset_finalSite
      (formula source)
      (formula_incidencesWithMetadata_offsets_zero_or_one
        source positiveOffsets)
      site.1 site.2 edgeMember
  have finalTake :
      (variableRouteOccurrencesAt
          (formula source) (site.1, (1, 1))).take 3 =
        variableRouteOccurrencesAt
          (formula source) (site.1, (1, 1)) :=
    (List.take_eq_self_iff _).mpr
      (variableRouteOccurrencesAt_length_le_three
        (formula source)
        (formula_occurrencesAtMostThree_decidableEq source)
        (site.1, (1, 1)))
  apply List.mem_flatMap.mpr
  refine ⟨site.1, atomMember, ?_⟩
  unfold routedVariableFinalSiteEdgeIndexBlock
  rw [finalTake]
  exact finalMember

end PeriodicThreeSATThree
end LeanTrominoes
