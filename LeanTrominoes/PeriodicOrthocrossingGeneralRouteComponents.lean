/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralFanCoreContacts

/-! # Real images of complete routes split into two fans and the track core -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan core route

theorem route_realContains_parts {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (orthogonal : Bool) (degree : orthogonal = true → graph.DegreeAtMost 4)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) (point : ℝ × ℝ) :
    GridPolyline.RealContains (route graph orthogonal tagged.1 tagged.2) point ↔
      (GridPolyline.RealContains (fan graph orthogonal (sourcePort tagged.1 tagged.2)) point ∨
        GridPolyline.RealContains (core graph tagged.1 tagged.2) point) ∨
      GridPolyline.RealContains (translatePolyline (Cell.scale (drawingGridSize graph : Int) tagged.1.offset)
        (fan graph orthogonal (targetPort tagged.1 tagged.2))) point := by
  have sourceLast := fan_last orthogonal (sourcePort_mem_allPorts graph member) degree
  have targetLast := fan_last orthogonal (targetPort_mem_allPorts graph member) degree
  have sourceCoreLast : (joinPolylines (fan graph orthogonal (sourcePort tagged.1 tagged.2))
      (core graph tagged.1 tagged.2)).getLast? =
      some (Cell.add (portX graph (targetPort tagged.1 tagged.2),3)
        (Cell.scale (drawingGridSize graph : Int) tagged.1.offset)) := by
    rw [joinPolylines_getLast?_of_second (core_length graph tagged.1 tagged.2),core_last]
  have targetHead : (translatePolyline (Cell.scale (drawingGridSize graph : Int) tagged.1.offset)
      (fan graph orthogonal (targetPort tagged.1 tagged.2)).reverse).head? =
      some (Cell.add (portX graph (targetPort tagged.1 tagged.2),3)
        (Cell.scale (drawingGridSize graph : Int) tagged.1.offset)) := by
    rw [translatePolyline,List.head?_map,List.head?_reverse,targetLast]
    simp [Cell.add,add_comm]
  unfold route
  rw [GridPolyline.realContains_join sourceCoreLast targetHead,
    GridPolyline.realContains_join sourceLast (core_head graph tagged.1 tagged.2)]
  have reverseImage : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) tagged.1.offset)
        (fan graph orthogonal (targetPort tagged.1 tagged.2)).reverse) point ↔
      GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) tagged.1.offset)
        (fan graph orthogonal (targetPort tagged.1 tagged.2))) point := by
    rw [translatePolyline,List.map_reverse]
    exact GridPolyline.realContains_reverse _ _
  rw [reverseImage]

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
