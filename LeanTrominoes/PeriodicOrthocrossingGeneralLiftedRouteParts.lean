/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralRouteFans

/-! # Every point of a lifted route belongs to one of its fans or one core piece -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan core route classifiedCore

theorem translatePolyline_twice (first second : Cell) (points : List Cell) :
    translatePolyline first (translatePolyline second points) = translatePolyline (Cell.add first second) points := by
  simp [translatePolyline,List.map_map,Function.comp_def,Cell.add,add_assoc]

theorem lifted_route_realContains_parts {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (orthogonal : Bool) (degree : orthogonal = true → graph.DegreeAtMost 4)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx) {cell : Cell} {point : ℝ × ℝ}
    (contains : GridPolyline.RealContains (translatePolyline (Cell.scale (drawingGridSize graph : Int) cell)
      (route graph orthogonal tagged.1 tagged.2)) point) :
    (∃ target : Bool, GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) (routeFanCell tagged cell target))
        (fan graph orthogonal (routeFanPort tagged target))) point) ∨
      ∃ piece ∈ classifiedCore graph tagged.1 tagged.2,
        (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) cell)).RealContains point := by
  have original := (GridPolyline.realContains_translate_inverse _ _ _).mp contains
  rw [route_realContains_parts orthogonal degree member] at original
  rcases original with (sourceContains | coreContains) | targetContains
  · exact Or.inl ⟨false,(GridPolyline.realContains_translate_inverse _ _ _).mpr sourceContains⟩
  · have lifted := (GridPolyline.realContains_translate_inverse (Cell.scale (drawingGridSize graph : Int) cell)
      (core graph tagged.1 tagged.2) point).mpr coreContains
    obtain ⟨segment,segmentMember,segmentContains⟩ := lifted
    rw [gridPolylineSegments_translatePolyline,← classifiedCore_segments,List.map_map] at segmentMember
    obtain ⟨piece,pieceMember,rfl⟩ := List.mem_map.mp segmentMember
    exact Or.inr ⟨piece,pieceMember,segmentContains⟩
  · have lifted := (GridPolyline.realContains_translate_inverse (Cell.scale (drawingGridSize graph : Int) cell)
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) tagged.1.offset)
        (fan graph orthogonal (targetPort tagged.1 tagged.2))) point).mpr targetContains
    rw [translatePolyline_twice] at lifted
    have shifts : Cell.add (Cell.scale (drawingGridSize graph : Int) cell)
        (Cell.scale (drawingGridSize graph : Int) tagged.1.offset) =
        Cell.scale (drawingGridSize graph : Int) (Cell.add cell tagged.1.offset) := by
      apply Prod.ext <;> simp [Cell.add,Cell.scale,mul_add]
    rw [shifts] at lifted
    exact Or.inl ⟨true,lifted⟩

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
