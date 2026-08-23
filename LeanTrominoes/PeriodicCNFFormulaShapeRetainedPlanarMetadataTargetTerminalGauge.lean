/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTargetTerminalGaugeVertical

/-! # Canonical gauges of routed target terminals -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- A routed incidence's target-terminal prototype is based one incidence
offset away from the canonical target vertex, so its canonical variable
gauge is exactly that edge offset. -/
theorem retainedGauge_targetTerminal_eq_edgeOffset
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (incidence : CNFIncidence Variable)
    (edgeIndex : Nat)
    (edgeMember :
      (incidence.edge, edgeIndex) ∈ source.incidenceGraph.edges.zipIdx) :
    retainedDrawingWrappedPeriodicPlanarSATVariableGauge source
        ⟨PeriodicPlanarSATVariable.terminal
          ((⟨incidence, edgeIndex, (0, 0)⟩ :
            CNFRouteOccurrence Variable).targetTerminal source).indexed
          .finish⟩ =
      incidence.edge.offset := by
  apply Prod.ext
  · exact retainedGauge_targetTerminal_horizontal_eq_edgeOffset
      source wellFormed incidence edgeIndex edgeMember
  · exact retainedGauge_targetTerminal_vertical_eq_edgeOffset
      source wellFormed incidence edgeIndex edgeMember

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
