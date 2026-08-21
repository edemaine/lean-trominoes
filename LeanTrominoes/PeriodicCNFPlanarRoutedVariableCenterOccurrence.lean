/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableLinkExistence
import LeanTrominoes.PlanarThreeSATEqualityEndpointOccurrences

/-! # Central-atom occurrence in one routed variable gadget -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- The central atom of every represented site occurs in that site's active
equality-family formula. -/
theorem routedVariableCenter_mem_routedVariableFormulaAt
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {site : VariableRouteSite Variable}
    (siteMem : site ∈ drawingVariableRouteSites formula) :
    PlanarSATNode.atom site ∈ embeddedVariableOccurrences
      (routedVariableFormulaAt formula site) := by
  rcases routedVariableLinksAt_exists_of_mem_drawingVariableRouteSites
      formula siteMem with ⟨link, linkMem⟩
  have secondMem :=
    EqualityLink.second_mem_embeddedVariableOccurrences_equalityFamily
      linkMem
  rw [routedVariableLinksAt_second formula site linkMem] at secondMem
  exact secondMem

end LeanTrominoes.PeriodicOrthocrossing
