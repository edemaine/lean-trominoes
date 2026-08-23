/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataBendNextSliceSemantics
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataTargetTerminalPointHorizontal

/-! # Horizontal physical-position quotients of target terminals -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- Adding the target terminal's fixed local macrocell coordinate leaves its
horizontal period quotient equal to the incidence offset. -/
theorem targetTerminal_position_horizontal_ediv_eq_edgeOffset
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (incidence : CNFIncidence Variable)
    (edgeIndex : Nat)
    (edgeMember :
      (incidence.edge, edgeIndex) ∈ source.incidenceGraph.edges.zipIdx) :
    (drawingPeriodicPlanarSATVariablePosition source
      (.terminal
        ((⟨incidence, edgeIndex, (0, 0)⟩ :
          CNFRouteOccurrence Variable).targetTerminal source).indexed
        .finish)).1 /
        (drawingPeriodicPlanarSATPlacement source).period =
      incidence.edge.offset.1 := by
  let occurrence : CNFRouteOccurrence Variable :=
    ⟨incidence, edgeIndex, (0, 0)⟩
  change
    (drawingPeriodicPlanarSATVariablePosition source
      (.terminal
        (occurrence.targetTerminal source).indexed .finish)).1 /
        (drawingPeriodicPlanarSATPlacement source).period =
      occurrence.edge.offset.1
  have localBounds :=
    periodicPlanarSATVariableLocalPosition_in_macrocell
      (Variable := Variable)
      (PeriodicPlanarSATVariable.terminal
        (occurrence.targetTerminal source).indexed .finish)
  have periodPositive := drawingGridSize_pos source.incidenceGraph
  have quotient :=
    macrocellCoordinate_ediv_period_eq_center_ediv
      periodPositive
      (center :=
        (periodicPlanarSATVariableDrawingPoint source
          (.terminal
            (occurrence.targetTerminal source).indexed .finish)).1)
      (localCoordinate :=
        (periodicPlanarSATVariableLocalPosition
          (.terminal
            (occurrence.targetTerminal source).indexed .finish :
              PeriodicPlanarSATVariable Variable)).1)
      (le_of_lt localBounds.1) localBounds.2.1
  rw [drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
  calc
    _ =
        (periodicPlanarSATVariableDrawingPoint source
          (.terminal
            (occurrence.targetTerminal source).indexed .finish)).1 /
          drawingGridSize source.incidenceGraph := by
      simpa [Cell.add, Cell.scale, drawingPeriodicPlanarSATPlacement,
        planarMacroScale] using quotient
    _ = _ := targetTerminal_drawingPoint_horizontal_ediv_eq_edgeOffset
      source wellFormed incidence edgeIndex edgeMember

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
