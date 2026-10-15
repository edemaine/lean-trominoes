/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralPorts
import LeanTrominoes.Graphs.Drawings.Orthogonal.Degree.PeriodicOrthocrossingDegreeFourFans
import LeanTrominoes.Graphs.Drawings.Orthogonal.Correctness.PeriodicOrthocrossingCorrectness

/-! # General-degree track drawing and its degree-four orthogonal variant -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts

def position {Vertex : Type*} (graph : PeriodicGraph Vertex) [DecidableEq Vertex]
    (index : Nat) : Cell :=
  (blockStart (degrees graph) index+1,2)

def fan {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (orthogonal : Bool) (port : GraphPort Vertex) : List Cell :=
  if orthogonal then
    (degreeFourFan ⟨portRank graph port % 4,Nat.mod_lt _ (by decide)⟩).map
      (Cell.add (vertexX graph port.vertex,0))
  else [(vertexX graph port.vertex,2),(portX graph port,3)]

def core {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (edge : PeriodicEdge Vertex) (index : Nat) : List Cell :=
  let size : Int := drawingGridSize graph
  let sx := portX graph (sourcePort edge index)
  let tx := portX graph (targetPort edge index)
  let start : Cell := (sx,3)
  let finish := Cell.add (tx,3) (Cell.scale size edge.offset)
  let low := edgeTrack index
  let high := low+1
  let gate : Int := 3*graph.vertices.length+2*graph.edges.length+4+2*index
  match edge.offset with
  | (0,0) => [start,(sx,low),(tx,low),finish]
  | (1,0) =>
    if tx < sx then [start,(sx,low),(size+tx,low),finish]
    else [start,(sx,low),(size,low),(size,high),(size+tx,high),finish]
  | (-1,0) =>
    if sx < tx then [start,(sx,low),(tx-size,low),finish]
    else [start,(sx,low),(0,low),(0,high),(tx-size,high),finish]
  | (0,1) => [start,(sx,high),(gate,high),(gate,size+low),(tx,size+low),finish]
  | (0,-1) => [start,(sx,low),(gate,low),(gate,high-size),(tx,high-size),finish]
  | _ => [start,(sx,low),(finish.1,low),finish]

def route {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (orthogonal : Bool) (edge : PeriodicEdge Vertex) (index : Nat) : List Cell :=
  joinPolylines (joinPolylines (fan graph orthogonal (sourcePort edge index)) (core graph edge index))
    (translatePolyline (Cell.scale (drawingGridSize graph : Int) edge.offset)
      (fan graph orthogonal (targetPort edge index)).reverse)

def drawing {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (orthogonal : Bool) : PeriodicGridDrawing where
  gridSizePred := drawingGridSize graph-1
  vertexPositions := graph.vertices.zipIdx.map fun tagged => position graph tagged.2
  edgeRoutes := graph.edges.zipIdx.map fun tagged => route graph orthogonal tagged.1 tagged.2

theorem drawing_gridSize {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (orthogonal : Bool) :
    (drawing graph orthogonal).gridSize = drawingGridSize graph := by
  have positive := drawingGridSize_pos graph
  simp only [drawing,PeriodicGridDrawing.gridSize]
  omega

theorem drawing_gridSize_linear {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex) (orthogonal : Bool)
    (nonempty : 0 < graph.vertices.length+graph.edges.length) :
    (drawing graph orthogonal).gridSize ≤ 32*(graph.vertices.length+graph.edges.length) := by
  rw [drawing_gridSize]
  unfold drawingGridSize
  omega

theorem fan_length {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (orthogonal : Bool) (port : GraphPort Vertex) : 2 ≤ (fan graph orthogonal port).length := by
  cases orthogonal
  · simp [fan]
  · have valid : ∀ rank : Fin 4, 2 ≤ (degreeFourFan rank).length := by decide +kernel
    simpa [fan] using valid ⟨portRank graph port % 4,Nat.mod_lt _ (by decide)⟩

theorem fan_head {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (orthogonal : Bool) (port : GraphPort Vertex) :
    (fan graph orthogonal port).head? = some (vertexX graph port.vertex,2) := by
  cases orthogonal
  · simp [fan]
  · let rank : Fin 4 := ⟨portRank graph port % 4,Nat.mod_lt _ (by decide)⟩
    change ((degreeFourFan rank).map (Cell.add (vertexX graph port.vertex,0))).head? = _
    rw [List.head?_map,(degreeFourFan_endpoints rank).1]
    simp [Cell.add]

theorem fan_last {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (orthogonal : Bool) {port : GraphPort Vertex} (member : port ∈ allPorts graph)
    (degree : orthogonal = true → graph.DegreeAtMost 4) :
    (fan graph orthogonal port).getLast? = some (portX graph port,3) := by
  cases orthogonal
  · simp [fan]
  · have rank : portRank graph port < 4 :=
      lt_of_lt_of_le (port_rank_bound member) (by rw [portsAt_length]; exact degree rfl _)
    let selected : Fin 4 := ⟨portRank graph port % 4,Nat.mod_lt _ (by decide)⟩
    change ((degreeFourFan selected).map (Cell.add (vertexX graph port.vertex,0))).getLast? = _
    rw [List.getLast?_map,(degreeFourFan_endpoints selected).2]
    simp only [Option.map_some,Cell.add]
    dsimp only [selected]
    rw [Nat.mod_eq_of_lt rank]
    congr 2
    simp only [vertexX,portX]
    omega

theorem route_head {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (orthogonal : Bool) (edge : PeriodicEdge Vertex) (index : Nat) :
    (route graph orthogonal edge index).head? = some (vertexX graph edge.source,2) := by
  have nonempty : fan graph orthogonal (sourcePort edge index) ≠ [] := by
    have length := fan_length graph orthogonal (sourcePort edge index)
    intro empty
    simp [empty] at length
  unfold route
  rw [joinPolylines_head?_of_first (joinPolylines_ne_nil_of_first nonempty),
    joinPolylines_head?_of_first nonempty,fan_head]
  rfl

theorem route_last {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (orthogonal : Bool) (edge : PeriodicEdge Vertex) (index : Nat) :
    (route graph orthogonal edge index).getLast? =
      some (Cell.add (Cell.scale (drawingGridSize graph : Int) edge.offset) (vertexX graph edge.target,2)) := by
  have targetLength : 2 ≤ (translatePolyline (Cell.scale (drawingGridSize graph : Int) edge.offset)
      (fan graph orthogonal (targetPort edge index)).reverse).length := by
    simpa [translatePolyline] using fan_length graph orthogonal (targetPort edge index)
  unfold route
  rw [joinPolylines_getLast?_of_second targetLength]
  simp only [translatePolyline,List.getLast?_map,List.getLast?_reverse,fan_head,Option.map_some]
  rfl

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
