/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Graphs.Drawings.Orthogonal.General.PeriodicOrthocrossingGeneralFanBlocks
import LeanTrominoes.Common.Geometry.GridPolylineRealPeriodicSeparation

/-! # Distinct fan occurrences meet only at their shared graph vertex -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan

theorem fan_same_vertex_contacts_center {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4) {first second : GraphPort Vertex}
    (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph)
    (different : first ≠ second) (sameVertex : first.vertex = second.vertex) {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains (fan graph orthogonal first) point)
    (secondContains : GridPolyline.RealContains (fan graph orthogonal second) point) :
    point = realCell (vertexX graph first.vertex,2) := by
  have distinctColumns : portX graph first ≠ portX graph second := by
    intro equal
    exact different (portX_injective wellFormed firstMember secondMember equal)
  cases orthogonal
  · obtain ⟨firstSegment,firstSegmentMember,firstContains⟩ := firstContains
    obtain ⟨secondSegment,secondSegmentMember,secondContains⟩ := secondContains
    simp only [fan,Bool.false_eq_true,ite_false,gridPolylineSegments,List.mem_singleton] at firstSegmentMember secondSegmentMember
    subst firstSegment
    subst secondSegment
    rw [← sameVertex] at secondContains
    simpa [realCell] using GridSegment.straight_fan_meet_only_at_center
      (vertexX graph first.vertex) (portX graph first) (portX graph second) distinctColumns point firstContains secondContains
  · have firstRankBound : portRank graph first < 4 :=
      lt_of_lt_of_le (port_rank_bound firstMember) (by rw [portsAt_length]; exact degree rfl _)
    have secondRankBound : portRank graph second < 4 :=
      lt_of_lt_of_le (port_rank_bound secondMember) (by rw [portsAt_length]; exact degree rfl _)
    let firstRank : Fin 4 := ⟨portRank graph first % 4,Nat.mod_lt _ (by decide)⟩
    let secondRank : Fin 4 := ⟨portRank graph second % 4,Nat.mod_lt _ (by decide)⟩
    have distinctRanks : firstRank ≠ secondRank := by
      intro equal
      have equalVals := congrArg Fin.val equal
      dsimp only [firstRank,secondRank] at equalVals
      rw [Nat.mod_eq_of_lt firstRankBound,Nat.mod_eq_of_lt secondRankBound] at equalVals
      apply distinctColumns
      simp only [portX,sameVertex,equalVals]
    simp only [fan,ite_true] at firstContains secondContains
    change GridPolyline.RealContains (translatePolyline (vertexX graph first.vertex,0) (degreeFourFan firstRank)) point at firstContains
    change GridPolyline.RealContains (translatePolyline (vertexX graph second.vertex,0) (degreeFourFan secondRank)) point at secondContains
    rw [← sameVertex] at secondContains
    have firstLocal := (GridPolyline.realContains_translate_inverse _ _ _).mp firstContains
    have secondLocal := (GridPolyline.realContains_translate_inverse _ _ _).mp secondContains
    have center := degreeFourFan_meet_only_at_center distinctRanks firstLocal secondLocal
    have cx := congrArg Prod.fst center
    have cy := congrArg Prod.snd center
    apply Prod.ext <;> simp only [realCell,Prod.fst,Prod.snd,Int.cast_ofNat,Int.cast_zero,sub_zero] at cx cy ⊢ <;> linarith

theorem fan_periodic_contacts_center {Vertex : Type*} [DecidableEq Vertex]
    {graph : PeriodicGraph Vertex} (wellFormed : graph.IsWellFormed) (orthogonal : Bool)
    (degree : orthogonal = true → graph.DegreeAtMost 4) {first second : GraphPort Vertex}
    (firstMember : first ∈ allPorts graph) (secondMember : second ∈ allPorts graph)
    (different : first ≠ second) {firstCell secondCell : Cell} {point : ℝ × ℝ}
    (firstContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) firstCell) (fan graph orthogonal first)) point)
    (secondContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) secondCell) (fan graph orthogonal second)) point) :
    first.vertex = second.vertex ∧ firstCell = secondCell ∧
      point = realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) firstCell) (vertexX graph first.vertex,2)) := by
  have normalized {port : GraphPort Vertex} (member : port ∈ allPorts graph) :
      ∀ vertex ∈ fan graph orthogonal port,
        1 ≤ vertex.1 ∧ vertex.1 ≤ (drawingGridSize graph : Int)-1 ∧ 1 ≤ vertex.2 ∧ vertex.2 ≤ 3 := by
    have block := fan_block_bounds wellFormed member
    intro vertex vertexMember
    have bounds := fan_block_points orthogonal member vertex vertexMember
    omega
  have cells := GridPolyline.real_normalized_routes_cells_unique
    (by unfold drawingGridSize; omega : (3 : Int) < drawingGridSize graph)
    (normalized firstMember) (normalized secondMember) firstContains secondContains
  rw [← cells] at secondContains
  have firstLocal := (GridPolyline.realContains_translate_inverse _ _ _).mp firstContains
  have secondLocal := (GridPolyline.realContains_translate_inverse _ _ _).mp secondContains
  have vertices := fan_contacts_same_vertex wellFormed orthogonal firstMember secondMember firstLocal secondLocal
  have center := fan_same_vertex_contacts_center wellFormed orthogonal degree firstMember secondMember different vertices firstLocal secondLocal
  refine ⟨vertices,cells,?_⟩
  have cx := congrArg Prod.fst center
  have cy := congrArg Prod.snd center
  apply Prod.ext <;> simp only [realCell,Cell.add,Cell.scale,Prod.fst,Prod.snd,Int.cast_add,Int.cast_mul] at cx cy ⊢ <;> linarith

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
