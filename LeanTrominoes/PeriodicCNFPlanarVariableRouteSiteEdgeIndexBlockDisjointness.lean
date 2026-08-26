/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarVariableRouteSiteEdgeIndexBlockDedup

/-! # Disjoint route-index blocks at different variable atoms -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Translated site blocks belonging to different variable atoms contain
disjoint global route indices. -/
theorem routedVariableSiteEdgeIndexBlock_disjoint_of_atom_ne
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {firstAtom secondAtom : Variable}
    (atomNe : firstAtom ≠ secondAtom) :
    List.Disjoint
      (routedVariableSiteEdgeIndexBlock formula firstAtom)
      (routedVariableSiteEdgeIndexBlock formula secondAtom) := by
  rw [List.disjoint_left]
  intro edgeIndex firstMember secondMember
  rcases List.mem_flatMap.mp firstMember with
    ⟨firstSite, firstSiteMember, firstEdgeMember⟩
  rcases List.mem_map.mp firstEdgeMember with
    ⟨firstOccurrence, firstOccurrenceMember, firstIndexEq⟩
  rcases List.mem_flatMap.mp secondMember with
    ⟨secondSite, secondSiteMember, secondEdgeMember⟩
  rcases List.mem_map.mp secondEdgeMember with
    ⟨secondOccurrence, secondOccurrenceMember, secondIndexEq⟩
  have firstOccurrenceMember' : firstOccurrence ∈
      variableRouteOccurrencesAt formula firstSite :=
    List.mem_of_mem_take firstOccurrenceMember
  have secondOccurrenceMember' : secondOccurrence ∈
      variableRouteOccurrencesAt formula secondSite :=
    List.mem_of_mem_take secondOccurrenceMember
  have firstData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula firstSite firstOccurrenceMember'
  have secondData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula secondSite secondOccurrenceMember'
  have firstSiteAtom : firstSite.1 = firstAtom := by
    rw [variableRouteSiteBlock, List.mem_map] at firstSiteMember
    rcases firstSiteMember with
      ⟨translate, _translateMember, siteEq⟩
    exact congrArg Prod.fst siteEq.symm
  have secondSiteAtom : secondSite.1 = secondAtom := by
    rw [variableRouteSiteBlock, List.mem_map] at secondSiteMember
    rcases secondSiteMember with
      ⟨translate, _translateMember, siteEq⟩
    exact congrArg Prod.fst siteEq.symm
  have firstAtomEq : firstOccurrence.incidence.literal.atom = firstAtom :=
    (congrArg Prod.fst firstData.2).trans firstSiteAtom
  have secondAtomEq :
      secondOccurrence.incidence.literal.atom = secondAtom :=
    (congrArg Prod.fst secondData.2).trans secondSiteAtom
  have edgeIndexEq : firstOccurrence.edgeIndex =
      secondOccurrence.edgeIndex :=
    firstIndexEq.trans secondIndexEq.symm
  have incidenceEq := CNFRouteOccurrence.incidence_eq_of_edgeIndex_eq
    formula firstData.1 secondData.1 edgeIndexEq
  have incidenceAtomEq : firstOccurrence.incidence.literal.atom =
      secondOccurrence.incidence.literal.atom :=
    congrArg (fun incidence => incidence.literal.atom) incidenceEq
  exact atomNe
    (firstAtomEq.symm.trans (incidenceAtomEq.trans secondAtomEq))

end PeriodicOrthocrossing
end LeanTrominoes
