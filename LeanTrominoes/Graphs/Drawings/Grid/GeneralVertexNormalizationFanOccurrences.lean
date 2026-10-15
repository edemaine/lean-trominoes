/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Grid.GeneralVertexNormalizationRoutes
import LeanTrominoes.Graphs.Drawings.Grid.PeriodicGridDrawingRealLiftedVertices
import LeanTrominoes.Common.Geometry.GridPolylineRealEndpointContainment

/-! # Fan contacts identify lifted incidences -/
namespace LeanTrominoes.GeneralVertexNormalization
open PeriodicOrthocrossing

def portCell {Vertex : Type*} (tagged : PeriodicEdge Vertex × Nat) (cell : Cell) (target : Bool) : Cell :=
  if target then Cell.add cell tagged.1.offset else cell

theorem endpoint_occurrence_injective {Vertex : Type*} {graph : PeriodicGraph Vertex}
    {a b : PeriodicEdge Vertex × Nat} (am : a ∈ graph.edges.zipIdx) (bm : b ∈ graph.edges.zipIdx)
    {aCell bCell : Cell} {aTarget bTarget : Bool}
    (ports : endpointPort a aTarget = endpointPort b bTarget)
    (cells : portCell a aCell aTarget = portCell b bCell bTarget) : (a.2,aCell) = (b.2,bCell) := by
  have indices : a.2 = b.2 := by
    have equal := congrArg GraphPort.edgeIndex ports
    cases aTarget <;> cases bTarget <;> simpa [endpointPort,sourcePort,targetPort] using equal
  have kinds : aTarget = bTarget := by
    have equal := congrArg GraphPort.endKind ports
    cases aTarget <;> cases bTarget <;> simp_all [endpointPort,sourcePort,targetPort]
  subst bTarget
  have firstAt := List.mem_zipIdx_iff_getElem?.mp am
  have secondAt := List.mem_zipIdx_iff_getElem?.mp bm
  rw [← indices] at secondAt
  have tags : a = b := Prod.ext (Option.some.inj (firstAt.symm.trans secondAt)) indices
  subst b
  have cellEq : aCell = bCell := by
    cases aTarget
    · simpa [portCell] using cells
    · have hx := congrArg Prod.fst cells
      have hy := congrArg Prod.snd cells
      simp [portCell,Cell.add] at hx hy
      exact Prod.ext (by omega) (by omega)
  exact congrArg (fun cell => (a.2,cell)) cellEq

variable {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex} {drawing : PeriodicGridDrawing}

theorem fan_occurrence_contacts (valid : drawing.IsCompatible graph) (distinct : DistinctPortSides drawing graph)
    (chosen : Vertex → GraphPort Vertex) {first second : GraphPort Vertex}
    (fm : first ∈ allPorts graph) (sm : second ∈ allPorts graph) {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains
      (fanAt graph drawing chosen first (liftedVertex graph drawing first.vertex firstCell)) point)
    (secondContains : GridPolyline.RealContains
      (fanAt graph drawing chosen second (liftedVertex graph drawing second.vertex secondCell)) point) :
    first.vertex = second.vertex ∧ firstCell = secondCell ∧
      (first = second ∨ point = realCell (Cell.scale 32 (liftedVertex graph drawing first.vertex firstCell))) := by
  have positions := fanAt_contacts_same_position graph drawing chosen first second firstContains secondContains
  have occurrences := valid.lifted_vertex_eq (port_vertex_mem valid.1 fm) (port_vertex_mem valid.1 sm) positions
  refine ⟨occurrences.1,occurrences.2,?_⟩
  by_cases same : first = second
  · exact Or.inl same
  · apply Or.inr
    apply fanAt_contacts_center distinct chosen fm sm occurrences.1 same _ firstContains
    simpa only [positions] using secondContains

theorem fan_midpoint_identifies_port (valid : drawing.IsCompatible graph) (distinct : DistinctPortSides drawing graph)
    (chosen : Vertex → GraphPort Vertex) {first second : GraphPort Vertex}
    (fm : first ∈ allPorts graph) (sm : second ∈ allPorts graph) {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains
      (fanAt graph drawing chosen first (liftedVertex graph drawing first.vertex firstCell)) point)
    (firstMidpoint : point = realCell (Cell.add (Cell.scale 32 (liftedVertex graph drawing first.vertex firstCell))
      (Cell.scale 8 (portSide drawing first).direction.step)))
    (secondMidpoint : point = realCell (Cell.add (Cell.scale 32 (liftedVertex graph drawing second.vertex secondCell))
      (Cell.scale 8 (portSide drawing second).direction.step))) : first = second ∧ firstCell = secondCell := by
  have secondContains : GridPolyline.RealContains
      (fanAt graph drawing chosen second (liftedVertex graph drawing second.vertex secondCell)) point := by
    rw [secondMidpoint]
    exact GridPolyline.realContains_last
      (by simpa [fanAt,translatePolyline] using (fanAssignment_simple graph drawing chosen second).1)
      (fanAt_last distinct chosen sm _)
  have contact := fan_occurrence_contacts valid distinct chosen fm sm firstContains secondContains
  refine ⟨?_,contact.2.1⟩
  rcases contact.2.2 with same | center
  · exact same
  · have equal := realCell_injective (center.symm.trans firstMidpoint)
    cases side : portSide drawing first <;>
      simp [Cell.add,Cell.scale,side,VertexSide.direction,AxisDirection.step] at equal

end LeanTrominoes.GeneralVertexNormalization
