/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralRouteComponents

/-! # Contacts between the three pieces of a complete route -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan core classifiedCore

theorem fan_core_real_contact {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (edgeLocal : tagged.1.span ≤ 1) {port : GraphPort Vertex} (portMember : port ∈ allPorts graph)
    {cell : Cell} {point : ℝ × ℝ}
    (fanContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) cell) (fan graph orthogonal port)) point)
    (coreContains : GridPolyline.RealContains (core graph tagged.1 tagged.2) point) :
    point = realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) cell) (portX graph port,3)) := by
  obtain ⟨segment,segmentMember,contains⟩ := coreContains
  rw [← classifiedCore_segments] at segmentMember
  obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp segmentMember
  have shifted : (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) (0,0))).RealContains point := by
    simpa [GridSegment.translate,Cell.scale,Cell.add] using contains
  exact (fan_core_contacts_only_at_joint wellFormed orthogonal degree portMember member edgeLocal
    pieceMember fanContains shifted).1

theorem reverse_translated_fan_realContains {Vertex : Type*} [DecidableEq Vertex] (graph : PeriodicGraph Vertex)
    (orthogonal : Bool) (port : GraphPort Vertex) (offset : Cell) (point : ℝ × ℝ) :
    GridPolyline.RealContains (translatePolyline offset (fan graph orthogonal port).reverse) point ↔
      GridPolyline.RealContains (translatePolyline offset (fan graph orthogonal port)) point := by
  rw [translatePolyline,List.map_reverse]
  exact GridPolyline.realContains_reverse _ _

theorem route_outer_fans_contacts {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) {point : ℝ × ℝ}
    (sourceContains : GridPolyline.RealContains (fan graph orthogonal (sourcePort tagged.1 tagged.2)) point)
    (targetContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) tagged.1.offset)
        (fan graph orthogonal (targetPort tagged.1 tagged.2)).reverse) point) :
    point = realCell (vertexX graph tagged.1.source,2) ∧
      point = realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) tagged.1.offset)
        (vertexX graph tagged.1.target,2)) := by
  have liftedSource : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) (0,0))
        (fan graph orthogonal (sourcePort tagged.1 tagged.2))) point := by
    apply (GridPolyline.realContains_translate_inverse _ _ _).mpr
    simpa [Cell.scale] using sourceContains
  have liftedTarget := (reverse_translated_fan_realContains _ _ _ _ _).mp targetContains
  have different : sourcePort tagged.1 tagged.2 ≠ targetPort tagged.1 tagged.2 := by
    intro equal
    have kinds := congrArg GraphPort.endKind equal
    cases kinds
  have contact := fan_periodic_contacts_center wellFormed orthogonal degree
    (sourcePort_mem_allPorts graph member) (targetPort_mem_allPorts graph member) different
    liftedSource liftedTarget
  have vertices : tagged.1.source = tagged.1.target := contact.1
  have cells : (0,0) = tagged.1.offset := contact.2.1
  have source : point = realCell (vertexX graph tagged.1.source,2) := by
    simpa [sourcePort,Cell.scale,Cell.add] using contact.2.2
  refine ⟨source,?_⟩
  simpa [← vertices,← cells,Cell.scale,Cell.add] using source

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
