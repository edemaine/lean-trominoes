/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralRouteFanCoreSeparation

/-! # Ports and cells identify the fans of complete route occurrences -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan route

def routeFanPort {Vertex : Type*} (tagged : PeriodicEdge Vertex × Nat) (target : Bool) : GraphPort Vertex :=
  if target then targetPort tagged.1 tagged.2 else sourcePort tagged.1 tagged.2

def routeFanCell {Vertex : Type*} (tagged : PeriodicEdge Vertex × Nat) (cell : Cell) (target : Bool) : Cell :=
  if target then Cell.add cell tagged.1.offset else cell

theorem route_fan_key_injective {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    {firstTagged secondTagged : PeriodicEdge Vertex × Nat}
    (firstMember : firstTagged ∈ graph.edges.zipIdx) (secondMember : secondTagged ∈ graph.edges.zipIdx)
    (firstTarget secondTarget : Bool) {firstCell secondCell : Cell}
    (ports : routeFanPort firstTagged firstTarget = routeFanPort secondTagged secondTarget)
    (cells : routeFanCell firstTagged firstCell firstTarget = routeFanCell secondTagged secondCell secondTarget) :
    firstTagged = secondTagged ∧ firstCell = secondCell := by
  have indices := congrArg GraphPort.edgeIndex ports
  have kinds := congrArg GraphPort.endKind ports
  cases firstTarget <;> cases secondTarget
  · change firstTagged.2 = secondTagged.2 at indices
    exact ⟨tagged_eq_of_mem_zipIdx_of_snd_eq firstMember secondMember indices,cells⟩
  · cases kinds
  · cases kinds
  · change firstTagged.2 = secondTagged.2 at indices
    have taggedEq := tagged_eq_of_mem_zipIdx_of_snd_eq firstMember secondMember indices
    refine ⟨taggedEq,?_⟩
    change Cell.add firstCell firstTagged.1.offset = Cell.add secondCell secondTagged.1.offset at cells
    rw [← taggedEq] at cells
    apply Prod.ext
    · have x := congrArg Prod.fst cells
      simp only [Cell.add] at x
      omega
    · have y := congrArg Prod.snd cells
      simp only [Cell.add] at y
      omega

theorem fan_periodic_contacts_same_cell {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool) {first second : GraphPort Vertex}
    (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph)
    {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) firstCell) (fan graph orthogonal first)) point)
    (secondContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) secondCell) (fan graph orthogonal second)) point) :
    firstCell = secondCell := by
  have normalized {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
      ∀ vertex ∈ fan graph orthogonal port,
        1 ≤ vertex.1 ∧ vertex.1 ≤ (drawingGridSize graph : Int)-1 ∧ 1 ≤ vertex.2 ∧ vertex.2 ≤ 3 := by
    have block := fan_block_bounds wellFormed member
    intro vertex vertexMember
    have bounds := fan_block_points orthogonal member vertex vertexMember
    omega
  exact GridPolyline.real_normalized_routes_cells_unique
    (by unfold drawingGridSize; omega : (3 : Int) < drawingGridSize graph)
    (normalized firstMember) (normalized secondMember) firstContains secondContains

theorem routeFanPort_mem {Vertex : Type*} (graph : PeriodicGraph Vertex)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (target : Bool) :
    routeFanPort tagged target ∈ allPorts graph := by
  cases target
  · exact sourcePort_mem_allPorts graph member
  · exact targetPort_mem_allPorts graph member

theorem route_fan_contact_is_endpoint {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (orthogonal : Bool) (tagged : PeriodicEdge Vertex × Nat) (cell : Cell) (target : Bool) :
    GridPolyline.RealIsEndpoint (translatePolyline (Cell.scale (drawingGridSize graph : Int) cell)
      (route graph orthogonal tagged.1 tagged.2))
      (realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) (routeFanCell tagged cell target))
        (vertexX graph (routeFanPort tagged target).vertex,2))) := by
  cases target
  · refine Or.inl ⟨_,?_,rfl⟩
    rw [translatePolyline,List.head?_map,route_head]
    rfl
  · refine Or.inr ⟨_,?_,rfl⟩
    rw [translatePolyline,List.getLast?_map,route_last]
    simp only [Option.map_some,routeFanCell,routeFanPort,ite_true,targetPort,Cell.add,Cell.scale]
    congr 2 <;> ring

theorem route_fans_meet_only_at_endpoints {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool) (degree : orthogonal = true → graph.DegreeAtMost 4)
    {firstTagged secondTagged : PeriodicEdge Vertex × Nat}
    (firstMember : firstTagged ∈ graph.edges.zipIdx) (secondMember : secondTagged ∈ graph.edges.zipIdx)
    (firstTarget secondTarget : Bool) {firstCell secondCell : Cell}
    (different : (firstTagged,firstCell) ≠ (secondTagged,secondCell)) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) (routeFanCell firstTagged firstCell firstTarget))
        (fan graph orthogonal (routeFanPort firstTagged firstTarget))) point)
    (secondContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) (routeFanCell secondTagged secondCell secondTarget))
        (fan graph orthogonal (routeFanPort secondTagged secondTarget))) point) :
    GridPolyline.RealIsEndpoint (translatePolyline (Cell.scale (drawingGridSize graph : Int) firstCell)
      (route graph orthogonal firstTagged.1 firstTagged.2)) point ∧
    GridPolyline.RealIsEndpoint (translatePolyline (Cell.scale (drawingGridSize graph : Int) secondCell)
      (route graph orthogonal secondTagged.1 secondTagged.2)) point := by
  have firstPortMember := routeFanPort_mem graph firstMember firstTarget
  have secondPortMember := routeFanPort_mem graph secondMember secondTarget
  have cells := fan_periodic_contacts_same_cell wellFormed orthogonal firstPortMember secondPortMember firstContains secondContains
  have distinctPorts : routeFanPort firstTagged firstTarget ≠ routeFanPort secondTagged secondTarget := by
    intro ports
    have same := route_fan_key_injective firstMember secondMember firstTarget secondTarget ports cells
    exact different (Prod.ext same.1 same.2)
  have contact := fan_periodic_contacts_center wellFormed orthogonal degree firstPortMember secondPortMember
    distinctPorts firstContains secondContains
  constructor
  · rw [contact.2.2]
    exact route_fan_contact_is_endpoint graph orthogonal firstTagged firstCell firstTarget
  · rw [contact.2.2,contact.1,contact.2.1]
    exact route_fan_contact_is_endpoint graph orthogonal secondTagged secondCell secondTarget

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
