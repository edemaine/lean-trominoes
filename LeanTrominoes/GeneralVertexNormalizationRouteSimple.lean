/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GeneralVertexNormalizationCoreContacts
import LeanTrominoes.GridPolylineRealThreePartSimple

/-! # Normalized routes remain simple, including loops -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing
variable {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}

theorem normalizedRoute_simple (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    GridPolyline.IsRealSimple (normalizedRoute graph drawing chosen tagged cell) := by
  have fm := sourcePort_mem_allPorts graph member
  have tm := targetPort_mem_allPorts graph member
  have firstSimple : GridPolyline.IsRealOpenSimple (sourceFan graph drawing chosen tagged cell) :=
    (fanAssignment_simple graph drawing chosen _).translate _
  have middleSimple : GridPolyline.IsRealOpenSimple (trimmedCore drawing tagged.2 cell) :=
    GridPolyline.clippedScaledRoute_isRealOpenSimple (liftedRoute_simple valid member cell)
      (liftedRoute_orthogonal valid.1 orthogonal member cell)
  have lastSimple : GridPolyline.IsRealOpenSimple (targetFan graph drawing chosen tagged cell).reverse := by
    simpa only [targetFan,fanAt,translatePolyline,List.map_reverse] using
      (fanAssignment_reverse_simple graph drawing chosen (targetPort tagged.1 tagged.2)).translate
        (Cell.scale 32 (liftedVertex graph drawing tagged.1.target (Cell.add cell tagged.1.offset)))
  have firstHead : (sourceFan graph drawing chosen tagged cell).head? =
      some (Cell.scale 32 (liftedVertex graph drawing tagged.1.source cell)) := fanAt_head chosen _ _
  have firstLast : (sourceFan graph drawing chosen tagged cell).getLast? =
      some (Cell.add (Cell.scale 32 (liftedVertex graph drawing tagged.1.source cell))
        (Cell.scale 8 (portSide drawing (sourcePort tagged.1 tagged.2)).direction.step)) := fanAt_last distinct chosen fm _
  have middleHead := (sourceFan_joint valid orthogonal distinct chosen member cell).symm.trans firstLast
  have lastHead : (targetFan graph drawing chosen tagged cell).reverse.head? =
      some (Cell.add (Cell.scale 32 (liftedVertex graph drawing tagged.1.target (Cell.add cell tagged.1.offset)))
        (Cell.scale 8 (portSide drawing (targetPort tagged.1 tagged.2)).direction.step)) := by
    rw [List.head?_reverse]
    exact fanAt_last distinct chosen tm _
  have middleLast := (targetFan_joint valid orthogonal distinct chosen member cell).trans lastHead
  have lastLast : (targetFan graph drawing chosen tagged cell).reverse.getLast? =
      some (Cell.scale 32 (liftedVertex graph drawing tagged.1.target (Cell.add cell tagged.1.offset))) := by
    rw [List.getLast?_reverse]
    exact fanAt_head chosen _ _
  have long : 2 ≤ (normalizedRoute graph drawing chosen tagged cell).length := by
    have firstLong := firstSimple.1
    unfold normalizedRoute joinPolylines
    simp only [List.length_append,List.length_tail]
    omega
  apply GridPolyline.isRealSimple_of_three_parts firstSimple middleSimple lastSimple long
    (normalizedRoute_segments valid orthogonal distinct chosen member cell)
    firstHead firstLast middleHead middleLast lastHead lastLast
  · intro point fanContains coreContains
    exact (fanAt_trimmedRoute_contact distinct chosen fm (liftedRoute_simple valid member cell)
      (liftedRoute_orthogonal valid.1 orthogonal member cell) _
      (liftedRoute_vertexAvoidance valid member (port_vertex_mem valid.1.1 fm) _ _) fanContains coreContains).1
  · intro point coreContains fanContains
    have original := (GridPolyline.realContains_reverse _ _).mp fanContains
    exact (fanAt_trimmedRoute_contact distinct chosen tm (liftedRoute_simple valid member cell)
      (liftedRoute_orthogonal valid.1 orthogonal member cell) _
      (liftedRoute_vertexAvoidance valid member (port_vertex_mem valid.1.1 tm) _ _) original coreContains).1
  · intro point firstContains lastContains
    have original := (GridPolyline.realContains_reverse _ _).mp lastContains
    have contact := fan_occurrence_contacts valid.1 distinct chosen fm tm firstContains original
    rcases contact.2.2 with same | center
    · have kinds := congrArg GraphPort.endKind same
      simp [sourcePort,targetPort] at kinds
    · have positions : liftedVertex graph drawing tagged.1.source cell =
        liftedVertex graph drawing tagged.1.target (Cell.add cell tagged.1.offset) :=
        congrArg₂ (liftedVertex graph drawing) contact.1 contact.2.1
      exact ⟨center,center.trans (congrArg (fun position => realCell (Cell.scale 32 position)) positions)⟩

end LeanTrominoes.GeneralVertexNormalization
