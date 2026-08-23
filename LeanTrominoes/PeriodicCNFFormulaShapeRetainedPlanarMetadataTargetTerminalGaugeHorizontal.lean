/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTargetTerminalPositionHorizontal

/-! # Horizontal gauges of routed target terminals -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The horizontal target-terminal gauge is its incidence-edge offset. -/
theorem retainedGauge_targetTerminal_horizontal_eq_edgeOffset
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (incidence : CNFIncidence Variable)
    (edgeIndex : Nat)
    (edgeMember :
      (incidence.edge, edgeIndex) ∈ source.incidenceGraph.edges.zipIdx) :
    (retainedDrawingWrappedPeriodicPlanarSATVariableGauge source
        ⟨PeriodicPlanarSATVariable.terminal
          ((⟨incidence, edgeIndex, (0, 0)⟩ :
            CNFRouteOccurrence Variable).targetTerminal source).indexed
          .finish⟩).1 =
      incidence.edge.offset.1 := by
  let occurrence : CNFRouteOccurrence Variable :=
    ⟨incidence, edgeIndex, (0, 0)⟩
  change (retainedDrawingWrappedPeriodicPlanarSATVariableGauge source
      ⟨PeriodicPlanarSATVariable.terminal
        (occurrence.targetTerminal source).indexed .finish⟩).1 =
    occurrence.edge.offset.1
  unfold retainedDrawingWrappedPeriodicPlanarSATVariableGauge
  rw [wrappedDrawingPeriodicPlanarSATPlacement_canonicalPositionGauge_mk]
  change
    (drawingPeriodicPlanarSATVariablePosition source
      (.terminal
        (occurrence.targetTerminal source).indexed .finish)).1 /
        (drawingPeriodicPlanarSATPlacement source).period =
      occurrence.edge.offset.1
  exact targetTerminal_position_horizontal_ediv_eq_edgeOffset
    source wellFormed incidence edgeIndex edgeMember

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
