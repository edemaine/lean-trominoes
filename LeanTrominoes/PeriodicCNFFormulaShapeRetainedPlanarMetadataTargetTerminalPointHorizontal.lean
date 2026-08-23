/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarVariablePortGeometry
import LeanTrominoes.PeriodicIntegerPeriodQuotient

/-! # Horizontal drawing-point quotients of target terminals -/

namespace LeanTrominoes.PeriodicCNF
namespace FormulaShapeRetainedPlanarMetadataDirection

open PeriodicOrthocrossing PlanarThreeSAT

/-- The horizontal period quotient of a target-terminal drawing point is
the incidence edge's horizontal offset. -/
theorem targetTerminal_drawingPoint_horizontal_ediv_eq_edgeOffset
    {Variable : Type} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (wellFormed : source.incidenceGraph.IsWellFormed)
    (incidence : CNFIncidence Variable)
    (edgeIndex : Nat)
    (edgeMember :
      (incidence.edge, edgeIndex) ∈ source.incidenceGraph.edges.zipIdx) :
    (SegmentTerminal.drawingPoint source.incidenceGraph
      ((⟨incidence, edgeIndex, (0, 0)⟩ :
        CNFRouteOccurrence Variable).targetTerminal source)).1 /
        drawingGridSize source.incidenceGraph =
      incidence.edge.offset.1 := by
  let occurrence : CNFRouteOccurrence Variable :=
    ⟨incidence, edgeIndex, (0, 0)⟩
  change
    (SegmentTerminal.drawingPoint source.incidenceGraph
      (occurrence.targetTerminal source)).1 /
        drawingGridSize source.incidenceGraph =
      occurrence.edge.offset.1
  have targetMember :
      occurrence.edge.target ∈ source.incidenceGraph.vertices :=
    (wellFormed.2 occurrence.edge
      (List.fst_mem_of_mem_zipIdx edgeMember)).2
  have targetIndexLt :
      source.incidenceGraph.vertices.idxOf occurrence.edge.target <
        source.incidenceGraph.vertices.length :=
    List.idxOf_lt_length_iff.mpr targetMember
  have targetXNonnegative :
      0 ≤ vertexX
        (source.incidenceGraph.vertices.idxOf occurrence.edge.target) := by
    simp [vertexX]
    omega
  have targetXSmall :
      vertexX
          (source.incidenceGraph.vertices.idxOf occurrence.edge.target) <
        drawingGridSize source.incidenceGraph := by
    simp only [vertexX, drawingGridSize]
    omega
  have periodPositive := drawingGridSize_pos source.incidenceGraph
  rw [occurrence.targetTerminal_drawingPoint]
  simp only [Cell.add, Cell.scale]
  simp only [occurrence, CNFRouteOccurrence.edge,
    vertexPosition, Int.zero_add]
  exact coordinate_add_period_mul_ediv_eq_shift periodPositive
    targetXNonnegative targetXSmall _

end FormulaShapeRetainedPlanarMetadataDirection
end LeanTrominoes.PeriodicCNF
