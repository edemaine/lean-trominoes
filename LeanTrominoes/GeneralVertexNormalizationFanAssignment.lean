/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GeneralVertexNormalizationEndpointDirections
import LeanTrominoes.DegreeThreeVertexNormalizationSelectedPort

/-! # Assigning uncolored templates to graph incidences -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing DegreeThreeVertexNormalization

def DistinctPortSides {Vertex : Type*} (drawing : PeriodicGridDrawing) (graph : PeriodicGraph Vertex) : Prop :=
  ∀ first ∈ allPorts graph, ∀ second ∈ allPorts graph,
    first.vertex = second.vertex → portSide drawing first = portSide drawing second → first = second

def usedSides {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (vertex : Vertex) : List VertexSide :=
  (portsAt graph vertex).map (portSide drawing)

def omittedSideOfList : List VertexSide → VertexSide
  | [first,second,third] => omittedSide first second third
  | _ => .east

def omittedAt {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (vertex : Vertex) : VertexSide :=
  omittedSideOfList (usedSides graph drawing vertex)

def straightTemplate (side : VertexSide) : List Cell := [(0,0),Cell.scale 8 side.direction.step]

def fanAssignment {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (drawing : PeriodicGridDrawing)
    (chosen : Vertex → GraphPort Vertex) (port : GraphPort Vertex) : List Cell :=
  if (portsAt graph port.vertex).length = 3 then
    selectedTemplate (omittedAt graph drawing port.vertex) (portSide drawing (chosen port.vertex))
      (selectedCanonicalPort (omittedAt graph drawing port.vertex) (portSide drawing (chosen port.vertex)) (portSide drawing port))
  else straightTemplate (portSide drawing port)

theorem usedSides_nodup {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : DistinctPortSides drawing graph) (vertex : Vertex) :
    (usedSides graph drawing vertex).Nodup := by
  apply List.Nodup.map_on ?_ (portsAt_nodup graph vertex)
  intro first firstMember second secondMember sameSide
  have firstData : first ∈ allPorts graph ∧ first.vertex = vertex := by simpa [portsAt] using firstMember
  have secondData : second ∈ allPorts graph ∧ second.vertex = vertex := by simpa [portsAt] using secondMember
  exact distinct first firstData.1 second secondData.1 (firstData.2.trans secondData.2.symm) sameSide

theorem omittedSideOfList_not_mem {sides : List VertexSide} (long : sides.length = 3) (nodup : sides.Nodup) :
    omittedSideOfList sides ∉ sides := by
  obtain ⟨first,second,third,rfl⟩ := List.length_eq_three.mp long
  exact (omittedSide_spec first second third nodup).1

theorem portSide_ne_omittedAt {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : DistinctPortSides drawing graph) {port : GraphPort Vertex}
    (member : port ∈ allPorts graph) (degree : (portsAt graph port.vertex).length = 3) :
    portSide drawing port ≠ omittedAt graph drawing port.vertex := by
  have sideMember : portSide drawing port ∈ usedSides graph drawing port.vertex :=
    List.mem_map.mpr ⟨port,port_mem_portsAt graph member,rfl⟩
  have long : (usedSides graph drawing port.vertex).length = 3 := by simpa [usedSides] using degree
  have notMember := omittedSideOfList_not_mem long (usedSides_nodup distinct port.vertex)
  intro equal
  apply notMember
  simpa only [equal,omittedAt] using sideMember

theorem fanAssignment_head {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (chosen : Vertex → GraphPort Vertex) (port : GraphPort Vertex) :
    (fanAssignment graph drawing chosen port).head? = some (0,0) := by
  unfold fanAssignment
  split
  · exact (selectedTemplate_endpoints _ _ _).1
  · simp [straightTemplate]

theorem fanAssignment_last {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : DistinctPortSides drawing graph)
    (chosen : Vertex → GraphPort Vertex) {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
    (fanAssignment graph drawing chosen port).getLast? = some (Cell.scale 8 (portSide drawing port).direction.step) := by
  unfold fanAssignment
  split
  · rename_i degree
    rw [(selectedTemplate_endpoints _ _ _).2]
    simp only [selectedBoundaryPoint,selectedBoundarySide_selectedCanonicalPort _ _ _
      (portSide_ne_omittedAt distinct member degree)]
  · simp [straightTemplate]

theorem fanAssignment_simple {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (drawing : PeriodicGridDrawing) (chosen : Vertex → GraphPort Vertex) (port : GraphPort Vertex) :
    GridPolyline.IsRealOpenSimple (fanAssignment graph drawing chosen port) := by
  unfold fanAssignment
  split
  · exact selectedTemplate_isRealOpenSimple _ _ _
  · apply GridPolyline.isRealOpenSimple_of_box_certificate
    cases side : portSide drawing port <;>
      simp [straightTemplate,GridPolyline.SimpleBoxCertificate,gridPolylineSegments,
        Cell.scale,VertexSide.direction,AxisDirection.step]

theorem fanAssignment_chosen_west {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {drawing : PeriodicGridDrawing} (distinct : DistinctPortSides drawing graph)
    (chosen : Vertex → GraphPort Vertex) (vertex : Vertex)
    (chosenMember : chosen vertex ∈ allPorts graph) (atVertex : (chosen vertex).vertex = vertex)
    (degree : (portsAt graph vertex).length = 3) :
    AxisDirection.polylineFirstDirection (fanAssignment graph drawing chosen (chosen vertex)) = .west := by
  have used := portSide_ne_omittedAt distinct chosenMember (by simpa [atVertex] using degree)
  unfold fanAssignment
  simp only [atVertex,degree,ite_true]
  rw [selectedCanonicalPort_chosen _ _ (by simpa only [atVertex] using used)]
  exact selectedTemplate_firstDirection _ _ .west

end LeanTrominoes.GeneralVertexNormalization
