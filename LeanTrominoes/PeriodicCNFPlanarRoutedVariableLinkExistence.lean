/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarOccurrences

/-! # Active-link existence at represented variable-route sites -/

namespace LeanTrominoes.PeriodicOrthocrossing

open PlanarThreeSAT

/-- Every represented variable-route site has at least one active equality
link, because the site itself was obtained from a route occurrence. -/
theorem routedVariableLinksAt_exists_of_mem_drawingVariableRouteSites
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {site : VariableRouteSite Variable}
    (siteMem : site ∈ drawingVariableRouteSites formula) :
    ∃ link, link ∈ routedVariableLinksAt formula site := by
  rw [drawingVariableRouteSites, List.mem_dedup] at siteMem
  rcases List.mem_map.mp siteMem with
    ⟨occurrence, occurrenceMem, siteEq⟩
  have occurrenceAtMem :
      occurrence ∈ variableRouteOccurrencesAt formula site := by
    simp [variableRouteOccurrencesAt, occurrenceMem, siteEq]
  have nodeMem :
      PlanarSATNode.carrier
          (.terminal (occurrence.targetTerminal formula)) ∈
        routedVariableNodes formula site :=
    (mem_routedVariableNodes_iff formula site _).mpr
      ⟨occurrence, occurrenceAtMem, rfl⟩
  cases nodesEq : routedVariableNodes formula site with
  | nil =>
      simp [nodesEq] at nodeMem
  | cons first rest =>
      refine
        ⟨⟨first, .atom site,
            routedVariableEqualityPositions formula site
              first.duplicatorArm⟩, ?_⟩
      simp [routedVariableLinksAt, nodesEq]

end LeanTrominoes.PeriodicOrthocrossing
