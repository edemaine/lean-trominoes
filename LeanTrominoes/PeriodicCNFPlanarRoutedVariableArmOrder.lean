/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableNodeOrder

/-! # Exact order of routed-variable duplicator arms -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Active link arms occur in the same order as the selected target
terminals, truncated to the three available duplicator ports. -/
theorem routedVariableLinksAt_arms_eq_targetTerminalArms
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    ((routedVariableLinksAt formula site).map fun link =>
        link.first.duplicatorArm) =
      ((variableRouteOccurrencesAt formula site).take 3).map
        fun occurrence =>
          (occurrence.targetTerminal formula).duplicatorArm := by
  have firsts :
      (routedVariableLinksAt formula site).map EqualityLink.first =
        (routedVariableNodes formula site).take 3 := by
    simp [routedVariableLinksAt, List.map_map, Function.comp_def]
  calc
    ((routedVariableLinksAt formula site).map fun link =>
        link.first.duplicatorArm) =
        ((routedVariableLinksAt formula site).map
          EqualityLink.first).map PlanarSATNode.duplicatorArm := by
      simp [List.map_map, Function.comp_def]
    _ = ((routedVariableNodes formula site).take 3).map
        PlanarSATNode.duplicatorArm := by rw [firsts]
    _ = _ := by
      rw [routedVariableNodes_eq_map_targetTerminals]
      simp [List.map_take, List.map_map, Function.comp_def,
        PlanarSATNode.duplicatorArm]

end PeriodicOrthocrossing
end LeanTrominoes
