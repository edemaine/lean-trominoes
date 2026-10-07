/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GeneralVertexNormalizationRoutes

/-! # Endpoints, orthogonality, and translation of normalized routes -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing
variable {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}

theorem normalizedRoute_endpoints (chosen : Vertex → GraphPort Vertex)
    (tagged : PeriodicEdge Vertex × Nat) (cell : Cell) :
    (normalizedRoute graph drawing chosen tagged cell).head? =
      some (Cell.scale 32 (liftedVertex graph drawing tagged.1.source cell)) ∧
    (normalizedRoute graph drawing chosen tagged cell).getLast? =
      some (Cell.scale 32 (liftedVertex graph drawing tagged.1.target (Cell.add cell tagged.1.offset))) := by
  have firstLong : 2 ≤ (sourceFan graph drawing chosen tagged cell).length := by
    simpa [sourceFan,fanAt,translatePolyline] using (fanAssignment_simple graph drawing chosen (sourcePort tagged.1 tagged.2)).1
  have lastLong : 2 ≤ (targetFan graph drawing chosen tagged cell).reverse.length := by
    simpa [targetFan,fanAt,translatePolyline] using (fanAssignment_simple graph drawing chosen (targetPort tagged.1 tagged.2)).1
  have firstNonempty : sourceFan graph drawing chosen tagged cell ≠ [] := by intro equal; simp [equal] at firstLong
  constructor
  · unfold normalizedRoute
    rw [joinPolylines_head?_of_first (joinPolylines_ne_nil_of_first firstNonempty),
      joinPolylines_head?_of_first firstNonempty]
    exact fanAt_head chosen _ _
  · unfold normalizedRoute
    rw [joinPolylines_getLast?_of_second lastLong,List.getLast?_reverse]
    exact fanAt_head chosen _ _

theorem normalizedRoute_orthogonal (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    OrthogonalPolyline (normalizedRoute graph drawing chosen tagged cell) := by
  have first : OrthogonalPolyline (sourceFan graph drawing chosen tagged cell) :=
    (fanAssignment_orthogonal graph drawing chosen _).translate _
  have middle : OrthogonalPolyline (trimmedCore drawing tagged.2 cell) :=
    GridPolyline.clippedScaledRoute_orthogonal (liftedRoute_orthogonal valid.1 orthogonal member cell)
  have last : OrthogonalPolyline (targetFan graph drawing chosen tagged cell).reverse :=
    ((fanAssignment_orthogonal graph drawing chosen _).translate _).reverse
  apply isChain_joinPolylines (isChain_joinPolylines first middle
    (sourceFan_joint valid orthogonal distinct chosen member cell)) last
  rw [joinPolylines_getLast?_of_second
    (by simpa [trimmedCore,GridPolyline.clippedScaledRoute_length] using (liftedRoute_simple valid member cell).1)]
  exact targetFan_joint valid orthogonal distinct chosen member cell

theorem translate_join (offset : Cell) (first second : List Cell) :
    translatePolyline offset (joinPolylines first second) =
      joinPolylines (translatePolyline offset first) (translatePolyline offset second) := by
  simp [translatePolyline,joinPolylines,List.map_tail]

theorem fanAt_add_position (chosen : Vertex → GraphPort Vertex) (port : GraphPort Vertex) (position offset : Cell) :
    fanAt graph drawing chosen port (Cell.add offset position) =
      translatePolyline (Cell.scale 32 offset) (fanAt graph drawing chosen port position) := by
  unfold fanAt translatePolyline
  simp only [List.map_map]
  apply List.map_congr_left
  intro point _
  apply Prod.ext <;> simp [Cell.add,Cell.scale] <;> ring

theorem liftedVertex_add_cell (vertex : Vertex) (cell offset : Cell) :
    liftedVertex graph drawing vertex (Cell.add cell offset) =
      Cell.add (drawing.periodTranslation cell) (liftedVertex graph drawing vertex offset) := by
  apply Prod.ext <;> simp [liftedVertex,PeriodicGridDrawing.periodTranslation,Cell.add,Cell.scale] <;> ring

theorem normalizedRoute_translate (chosen : Vertex → GraphPort Vertex) (tagged : PeriodicEdge Vertex × Nat) (cell : Cell) :
    normalizedRoute graph drawing chosen tagged cell =
      translatePolyline (Cell.scale 32 (drawing.periodTranslation cell)) (normalizedRoute graph drawing chosen tagged (0,0)) := by
  have first : sourceFan graph drawing chosen tagged cell =
      translatePolyline (Cell.scale 32 (drawing.periodTranslation cell)) (sourceFan graph drawing chosen tagged (0,0)) := by
    unfold sourceFan
    have position : liftedVertex graph drawing tagged.1.source cell =
        Cell.add (drawing.periodTranslation cell) (liftedVertex graph drawing tagged.1.source (0,0)) := by
      simpa [Cell.add] using (liftedVertex_add_cell (graph := graph) (drawing := drawing) tagged.1.source cell (0,0))
    rw [position,fanAt_add_position]
  have last : targetFan graph drawing chosen tagged cell =
      translatePolyline (Cell.scale 32 (drawing.periodTranslation cell)) (targetFan graph drawing chosen tagged (0,0)) := by
    unfold targetFan
    rw [liftedVertex_add_cell,fanAt_add_position]
    simp [Cell.add]
  have middle : trimmedCore drawing tagged.2 cell =
      translatePolyline (Cell.scale 32 (drawing.periodTranslation cell)) (trimmedCore drawing tagged.2 (0,0)) := by
    change GridPolyline.clippedScaledRoute (translatePolyline (drawing.periodTranslation cell) (drawing.edgeRoute tagged.2)) = _
    rw [GridPolyline.clippedScaledRoute_translate]
    have zero : drawing.realEdgeRoute tagged.2 (0,0) = drawing.edgeRoute tagged.2 := by
      change translatePolyline (drawing.periodTranslation (0,0)) (drawing.edgeRoute tagged.2) = _
      rw [show drawing.periodTranslation (0,0) = (0,0) by simp [PeriodicGridDrawing.periodTranslation,Cell.scale],translatePolyline_zero]
    simp only [trimmedCore,zero]
  unfold normalizedRoute
  rw [translate_join,translate_join,first,middle,last]
  simp [translatePolyline,List.map_reverse]

end LeanTrominoes.GeneralVertexNormalization
