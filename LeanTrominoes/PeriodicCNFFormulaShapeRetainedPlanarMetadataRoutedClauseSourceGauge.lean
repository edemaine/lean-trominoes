/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFFormulaShapeRetainedPlanarMetadataRoutedClauseFamilySemantics
import LeanTrominoes.PeriodicOrthocrossingRetainedPlanarSATGaugedVariablePositions

/-! # Canonical gauges of routed source-clause terminals -/

namespace LeanTrominoes
namespace PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- A routed incidence's source terminal at translation zero already lies in
the canonical physical period cell, so its retained variable gauge is zero. -/
theorem retainedGauge_sourceTerminal_eq_zero
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
            CNFRouteOccurrence Variable).sourceTerminal source).indexed
          .start⟩ =
      (0, 0) := by
  let occurrence : CNFRouteOccurrence Variable :=
    ⟨incidence, edgeIndex, (0, 0)⟩
  change retainedDrawingWrappedPeriodicPlanarSATVariableGauge source
      ⟨PeriodicPlanarSATVariable.terminal
        (occurrence.sourceTerminal source).indexed .start⟩ =
    (0, 0)
  have sourceMember :
      occurrence.edge.source ∈ source.incidenceGraph.vertices :=
    (wellFormed.2 occurrence.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)).1
  have sourceEqual :
      occurrence.edge.source =
        .clause occurrence.clauseOccurrence.1 := by
    rfl
  have bounded :=
    drawing_vertexPosition_in_fundamental_square
      source.incidenceGraph sourceMember
  have drawingPointBounds :
      InFundamentalDrawingSquare source.incidenceGraph
        (periodicPlanarSATVariableDrawingPoint source
          (.terminal
            (occurrence.sourceTerminal source).indexed .start)) := by
    change InFundamentalDrawingSquare source.incidenceGraph
      (SegmentTerminal.drawingPoint source.incidenceGraph
        (occurrence.sourceTerminal source))
    rw [occurrence.sourceTerminal_drawingPoint_eq_lifted
      source wellFormed edgeMember]
    rw [← sourceEqual]
    simpa [liftedIncidenceVertexPosition, occurrence,
      CNFRouteOccurrence.clauseOccurrence,
      PeriodicGridDrawing.periodTranslation,
      Cell.add, Cell.scale,
      InFundamentalDrawingSquare,
      PeriodicGridDrawing.PositionInFundamentalSquare] using
        And.intro (le_of_lt bounded.1)
          (And.intro bounded.2.1
            (And.intro (le_of_lt bounded.2.2.1)
              bounded.2.2.2))
  have localBounds :=
    periodicPlanarSATVariableLocalPosition_in_macrocell
      (Variable := Variable)
      (PeriodicPlanarSATVariable.terminal
        (occurrence.sourceTerminal source).indexed .start)
  have periodPositive :=
    drawingGridSize_pos source.incidenceGraph
  unfold retainedDrawingWrappedPeriodicPlanarSATVariableGauge
  rw [wrappedDrawingPeriodicPlanarSATPlacement_canonicalPositionGauge_mk]
  apply Prod.ext
  · change
      (drawingPeriodicPlanarSATVariablePosition source
        (.terminal
          (occurrence.sourceTerminal source).indexed .start)).1 /
          (drawingPeriodicPlanarSATPlacement source).period = 0
    rw [drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
    simpa [drawingPeriodicPlanarSATPlacement,
      Cell.add, Cell.scale, planarMacroScale] using
      (macrocellCoordinate_ediv_period_eq_zero
        periodPositive
        drawingPointBounds.1 drawingPointBounds.2.1
        (le_of_lt localBounds.1) localBounds.2.1)
  · change
      (drawingPeriodicPlanarSATVariablePosition source
        (.terminal
          (occurrence.sourceTerminal source).indexed .start)).2 /
          (drawingPeriodicPlanarSATPlacement source).period = 0
    rw [drawingPeriodicPlanarSATVariablePosition_eq_scale_add_local]
    simpa [drawingPeriodicPlanarSATPlacement,
      Cell.add, Cell.scale, planarMacroScale] using
      (macrocellCoordinate_ediv_period_eq_zero
        periodPositive
        drawingPointBounds.2.2.1 drawingPointBounds.2.2.2
        (le_of_lt localBounds.2.2.1) localBounds.2.2.2)

end FormulaShapeRetainedPlanarMetadataDirection
end PeriodicCNF
end LeanTrominoes
