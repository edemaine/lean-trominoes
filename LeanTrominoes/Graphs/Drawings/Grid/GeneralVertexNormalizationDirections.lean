/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationDrawing

/-! # Degree-three incidences use west, north, east, with the selected one west -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing DegreeThreeVertexNormalization
variable {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}

theorem firstDirection_join {first second : List Cell} (long : 2 ≤ first.length) :
    AxisDirection.polylineFirstDirection (joinPolylines first second) = AxisDirection.polylineFirstDirection first := by
  cases first with
  | nil => simp at long
  | cons first rest =>
    cases rest with
    | nil => simp at long
    | cons second rest => simp [joinPolylines,AxisDirection.polylineFirstDirection]

theorem normalizedRoute_firstDirection (chosen : Vertex → GraphPort Vertex) (tagged : PeriodicEdge Vertex × Nat) (cell : Cell) :
    AxisDirection.polylineFirstDirection (normalizedRoute graph drawing chosen tagged cell) =
      AxisDirection.polylineFirstDirection (fanAssignment graph drawing chosen (sourcePort tagged.1 tagged.2)) := by
  have long : 2 ≤ (sourceFan graph drawing chosen tagged cell).length := by
    simpa [sourceFan,fanAt,translatePolyline] using (fanAssignment_simple graph drawing chosen (sourcePort tagged.1 tagged.2)).1
  have joinedLong : 2 ≤ (joinPolylines (sourceFan graph drawing chosen tagged cell) (trimmedCore drawing tagged.2 cell)).length := by
    simp only [joinPolylines,List.length_append,List.length_tail]
    omega
  rw [normalizedRoute,firstDirection_join joinedLong,firstDirection_join long]
  exact AxisDirection.polylineFirstDirection_translatePolyline _ _

theorem normalizedRoute_lastDirection_outward (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (cell : Cell) :
    (AxisDirection.polylineLastDirection (normalizedRoute graph drawing chosen tagged cell)).opposite =
      AxisDirection.polylineFirstDirection (fanAssignment graph drawing chosen (targetPort tagged.1 tagged.2)) := by
  have lastLong : 2 ≤ (targetFan graph drawing chosen tagged cell).reverse.length := by
    simpa [targetFan,fanAt,translatePolyline] using (fanAssignment_simple graph drawing chosen (targetPort tagged.1 tagged.2)).1
  have targetHead : (targetFan graph drawing chosen tagged cell).reverse.head? = some
      (Cell.add (Cell.scale 32 (liftedVertex graph drawing tagged.1.target (Cell.add cell tagged.1.offset)))
        (Cell.scale 8 (portSide drawing (targetPort tagged.1 tagged.2)).direction.step)) := by
    rw [List.head?_reverse]
    exact fanAt_last distinct chosen (targetPort_mem_allPorts graph member) _
  have middleEnd := (targetFan_joint valid orthogonal distinct chosen member cell).trans targetHead
  have joinedEnd := (joinPolylines_getLast?_of_second
    (first := sourceFan graph drawing chosen tagged cell)
    (by simpa [trimmedCore,GridPolyline.clippedScaledRoute_length] using (liftedRoute_simple valid member cell).1)).trans middleEnd
  unfold normalizedRoute
  change (AxisDirection.polylineLastDirection (joinAtEndpoint _ _)).opposite = _
  rw [AxisDirection.polylineLastDirection_joinAtEndpoint joinedEnd targetHead lastLong,
    AxisDirection.polylineLastDirection_reverse,AxisDirection.opposite_opposite]
  exact AxisDirection.polylineFirstDirection_translatePolyline _ _

theorem normalizedDrawing_portDirection (valid : drawing.IsRealDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (distinct : DistinctPortSides drawing graph) (chosen : Vertex → GraphPort Vertex)
    {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    portDirection (normalizedDrawing graph drawing chosen) port =
      AxisDirection.polylineFirstDirection (fanAssignment graph drawing chosen port) := by
  obtain ⟨tagged,taggedMember,kind⟩ := allPorts_has_edge member
  rcases kind with rfl | rfl
  · change AxisDirection.polylineFirstDirection ((normalizedDrawing graph drawing chosen).edgeRoute tagged.2) = _
    rw [normalizedDrawing_edgeRoute chosen taggedMember]
    exact normalizedRoute_firstDirection chosen tagged (0,0)
  · change (AxisDirection.polylineLastDirection ((normalizedDrawing graph drawing chosen).edgeRoute tagged.2)).opposite = _
    rw [normalizedDrawing_edgeRoute chosen taggedMember]
    exact normalizedRoute_lastDirection_outward valid orthogonal distinct chosen taggedMember (0,0)

theorem fanAssignment_degree_three_directions (chosen : Vertex → GraphPort Vertex) {port : GraphPort Vertex}
    (degree : (portsAt graph port.vertex).length = 3) :
    AxisDirection.polylineFirstDirection (fanAssignment graph drawing chosen port) = .west ∨
      AxisDirection.polylineFirstDirection (fanAssignment graph drawing chosen port) = .north ∨
      AxisDirection.polylineFirstDirection (fanAssignment graph drawing chosen port) = .east := by
  unfold fanAssignment
  rw [if_pos degree,selectedTemplate_firstDirection]
  cases selectedCanonicalPort (omittedAt graph drawing port.vertex) (portSide drawing (chosen port.vertex)) (portSide drawing port) <;>
    simp [CanonicalVertexPort.direction]

theorem normalizedDrawing_degree_three_directions (planar : drawing.IsRealPlanarDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (chosen : Vertex → GraphPort Vertex) {port : GraphPort Vertex} (member : port ∈ allPorts graph)
    (degree : (portsAt graph port.vertex).length = 3) :
    portDirection (normalizedDrawing graph drawing chosen) port = .west ∨
      portDirection (normalizedDrawing graph drawing chosen) port = .north ∨
      portDirection (normalizedDrawing graph drawing chosen) port = .east := by
  rw [normalizedDrawing_portDirection planar.1 orthogonal (distinctPortSides_of_planar_orthogonal planar orthogonal) chosen member]
  exact fanAssignment_degree_three_directions chosen degree

theorem normalizedDrawing_chosen_west (planar : drawing.IsRealPlanarDrawing graph) (orthogonal : drawing.IsOrthogonal)
    (chosen : Vertex → GraphPort Vertex) (vertex : Vertex) (member : chosen vertex ∈ allPorts graph)
    (atVertex : (chosen vertex).vertex = vertex) (degree : (portsAt graph vertex).length = 3) :
    portDirection (normalizedDrawing graph drawing chosen) (chosen vertex) = .west := by
  have distinct := distinctPortSides_of_planar_orthogonal planar orthogonal
  rw [normalizedDrawing_portDirection planar.1 orthogonal distinct chosen member]
  exact fanAssignment_chosen_west distinct chosen vertex member atVertex degree

end LeanTrominoes.GeneralVertexNormalization
