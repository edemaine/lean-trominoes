/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRoutedVariableArmOrder
import LeanTrominoes.PeriodicCNFPlanarVariablePortGeometry

/-! # Routed-variable duplicator arms from target-port ranks -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PlanarThreeSAT

/-- Active link arms are the geometric classifications of the selected
incidences' target-port ranks, in global edge order. -/
theorem routedVariableLinksAt_arms_eq_targetPortRankArms
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (site : VariableRouteSite Variable) :
    ((routedVariableLinksAt formula site).map fun link =>
        link.first.duplicatorArm) =
      ((variableRouteOccurrencesAt formula site).take 3).map
        fun occurrence =>
          targetDuplicatorArm
            (portRank (PeriodicCNF.incidenceGraph formula)
              (targetPort occurrence.edge occurrence.edgeIndex)) := by
  rw [routedVariableLinksAt_arms_eq_targetTerminalArms]
  apply List.map_congr_left
  intro occurrence _
  exact occurrence.targetTerminal_duplicatorArm formula

end PeriodicOrthocrossing
end LeanTrominoes
