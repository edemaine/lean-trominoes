/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralRouteJointContacts
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralCoreSimple
import LeanTrominoes.Common.Geometry.GridPolylineRealThreePartSimple

/-! # Complete general track routes are simple, including closed loops -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan core

theorem route_isRealSimple {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4)
    {tagged : PeriodicEdge Vertex × Nat} (member : tagged ∈ graph.edges.zipIdx)
    (edgeLocal : tagged.1.span ≤ 1) : GridPolyline.IsRealSimple (route graph orthogonal tagged.1 tagged.2) := by
  have sourceMember := sourcePort_mem_allPorts graph member
  have targetMember := targetPort_mem_allPorts graph member
  let shift := Cell.scale (drawingGridSize graph : Int) tagged.1.offset
  have targetHead : (translatePolyline shift (fan graph orthogonal (targetPort tagged.1 tagged.2)).reverse).head? =
      some (Cell.add (portX graph (targetPort tagged.1 tagged.2),3) shift) := by
    rw [translatePolyline,List.head?_map,List.head?_reverse,fan_last orthogonal targetMember degree]
    simp [Cell.add,add_comm]
  have targetLast : (translatePolyline shift (fan graph orthogonal (targetPort tagged.1 tagged.2)).reverse).getLast? =
      some (Cell.add shift (vertexX graph tagged.1.target,2)) := by
    rw [translatePolyline,List.getLast?_map,List.getLast?_reverse,fan_head]
    rfl
  have long : 2 ≤ (route graph orthogonal tagged.1 tagged.2).length := by
    have sourceLong := fan_length graph orthogonal (sourcePort tagged.1 tagged.2)
    unfold route joinPolylines
    simp only [List.length_append,List.length_tail]
    omega
  apply GridPolyline.isRealSimple_of_three_parts
    (GridPolyline.isRealOpenSimple_of_box_certificate (fan_simple_box_certificate graph orthogonal _))
    (GridPolyline.isRealOpenSimple_of_box_certificate (core_simple_box_certificate wellFormed member edgeLocal))
    (GridPolyline.isRealOpenSimple_of_box_certificate (fan_reverse_translated_simple graph orthogonal _ shift))
    long (route_segments orthogonal degree member)
    (fan_head graph orthogonal _) (fan_last orthogonal sourceMember degree)
    (core_head graph tagged.1 tagged.2) (core_last graph tagged.1 tagged.2) targetHead targetLast
  · intro point sourceContains coreContains
    have shifted : GridPolyline.RealContains
        (translatePolyline (Cell.scale (drawingGridSize graph : Int) (0,0))
          (fan graph orthogonal (sourcePort tagged.1 tagged.2))) point := by
      apply (GridPolyline.realContains_translate_inverse _ _ _).mpr
      simpa [Cell.scale] using sourceContains
    simpa [Cell.scale,Cell.add] using
      fan_core_real_contact wellFormed orthogonal degree member edgeLocal sourceMember shifted coreContains
  · intro point coreContains targetContains
    have shifted := (reverse_translated_fan_realContains _ _ _ _ _).mp targetContains
    have contact := fan_core_real_contact wellFormed orthogonal degree member edgeLocal targetMember shifted coreContains
    simpa only [shift,Cell.add,add_comm] using contact
  · exact fun _ => route_outer_fans_contacts wellFormed orthogonal degree member

theorem drawing_realRoutesAreSimple {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4) (isLocal : graph.IsLocal) :
    (drawing graph orthogonal).RealRoutesAreSimple := by
  intro points member
  change points ∈ graph.edges.zipIdx.map (fun tagged => route graph orthogonal tagged.1 tagged.2) at member
  obtain ⟨tagged,taggedMember,rfl⟩ := List.mem_map.mp member
  exact route_isRealSimple wellFormed orthogonal degree taggedMember
    (isLocal tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember))

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
