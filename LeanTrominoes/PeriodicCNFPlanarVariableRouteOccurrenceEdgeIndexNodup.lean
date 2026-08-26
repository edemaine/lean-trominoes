/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableNodeOrder
import LeanTrominoes.PeriodicCNFPlanarVariableNormalizationDegree

/-! # Distinct edge indices at one routed-variable site -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Two represented occurrences with the same global edge index and the
same variable site are the same translated occurrence. -/
theorem variableRouteOccurrencesAt_eq_of_edgeIndex_eq
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable)
    {first second : CNFRouteOccurrence Variable}
    (firstMember : first ∈ variableRouteOccurrencesAt formula site)
    (secondMember : second ∈ variableRouteOccurrencesAt formula site)
    (edgeIndexEq : first.edgeIndex = second.edgeIndex) :
    first = second := by
  have firstData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site firstMember
  have secondData :=
    variableRouteOccurrencesAt_mem_drawing_and_variableOccurrence
      formula site secondMember
  have incidenceEq := CNFRouteOccurrence.incidence_eq_of_edgeIndex_eq
    formula firstData.1 secondData.1 edgeIndexEq
  have siteEq : first.variableOccurrence = second.variableOccurrence :=
    firstData.2.trans secondData.2.symm
  rcases first with ⟨firstIncidence, firstIndex, firstTranslate⟩
  rcases second with ⟨secondIncidence, secondIndex, secondTranslate⟩
  simp only at incidenceEq edgeIndexEq
  subst secondIncidence
  subst secondIndex
  have translateEq : firstTranslate = secondTranslate := by
    simp only [CNFRouteOccurrence.variableOccurrence,
      CNFRouteOccurrence.edge, Cell.add, Prod.mk.injEq] at siteEq
    exact Prod.ext
      (by omega)
      (by omega)
  subst secondTranslate
  rfl

/-- Global edge indices of the occurrences reaching one site are
duplicate-free. -/
theorem variableRouteOccurrencesAt_edgeIndices_nodup
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    ((variableRouteOccurrencesAt formula site).map
      CNFRouteOccurrence.edgeIndex).Nodup := by
  apply (variableRouteOccurrencesAt_nodup formula site).map_on
  intro first firstMember second secondMember edgeIndexEq
  exact variableRouteOccurrencesAt_eq_of_edgeIndex_eq
    formula site firstMember secondMember edgeIndexEq

end PeriodicOrthocrossing
end LeanTrominoes
