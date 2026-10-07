/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicOrthocrossingGeneralFanPortContacts
import LeanTrominoes.PeriodicOrthocrossingGeneralFanTrackSeparation

/-! # The only contacts between fans and cores are their prescribed port joints -/
namespace LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
attribute [local irreducible] fan classifiedCore core

theorem fan_core_contacts_only_at_joint {Vertex : Type*} [DecidableEq Vertex] {graph : PeriodicGraph Vertex}
    (wellFormed : graph.IsWellFormed) (orthogonal : Bool) (degree : orthogonal = true → graph.DegreeAtMost 4)
    {fanPort : GraphPort Vertex} (fanMember : fanPort ∈ allPorts graph)
    {tagged : PeriodicEdge Vertex × Nat} (edgeMember : tagged ∈ graph.edges.zipIdx) (edgeLocal : tagged.1.span ≤ 1)
    {piece : ClassifiedSegment Vertex} (pieceMember : piece ∈ classifiedCore graph tagged.1 tagged.2)
    {fanCell coreCell : Cell} {point : ℝ × ℝ}
    (fanContains : GridPolyline.RealContains
      (translatePolyline (Cell.scale (drawingGridSize graph : Int) fanCell) (fan graph orthogonal fanPort)) point)
    (coreContains : (piece.segment.translate (Cell.scale (drawingGridSize graph : Int) coreCell)).RealContains point) :
    point = realCell (Cell.add (Cell.scale (drawingGridSize graph : Int) fanCell) (portX graph fanPort,3)) ∧
      ((fanPort = sourcePort tagged.1 tagged.2 ∧ fanCell = coreCell) ∨
        (fanPort = targetPort tagged.1 tagged.2 ∧ fanCell = Cell.add coreCell tagged.1.offset)) := by
  have axis : piece.segment.IsAxisAligned := by
    apply (orthogonalPolyline_iff_segments _).mp (core_orthogonal wellFormed edgeMember edgeLocal)
    rw [← classifiedCore_segments]
    exact List.mem_map.mpr ⟨piece,pieceMember,rfl⟩
  rcases axis with horizontal | vertical
  · exact (fan_horizontal_core_disjoint orthogonal fanMember edgeMember pieceMember horizontal fanContains coreContains).elim
  · have kind := classifiedCore_vertical_role graph tagged.1 tagged.2 piece pieceMember vertical
    rcases kind with active | boundary
    · have portOrGate : (∃ port, piece.role.activeVerticalPort = some port) ∨
        ∃ index, piece.role = .gateVertical index := by
        cases roleEq : piece.role <;> simp_all [SegmentRole.IsActiveVertical,SegmentRole.activeVerticalPort]
      rcases portOrGate with ⟨port,portRole⟩ | ⟨index,gateRole⟩
      · have contact := fan_port_spine_contact wellFormed orthogonal degree fanMember edgeMember edgeLocal
          pieceMember vertical portRole fanContains coreContains
        have endpoint := core_port_is_endpoint_port graph tagged.1 tagged.2 piece pieceMember port portRole
        refine ⟨contact.2.2,?_⟩
        rcases endpoint with ⟨source,shift⟩ | ⟨target,shift⟩
        · refine Or.inl ⟨contact.1.trans source,?_⟩
          simpa only [shift,Cell.add,add_zero,Prod.eta] using contact.2.1
        · exact Or.inr ⟨contact.1.trans target,by simpa only [shift] using contact.2.1⟩
      · have indexEq := classifiedCore_role_index graph tagged.1 tagged.2 piece pieceMember
        rw [gateRole] at indexEq
        change index = tagged.2 at indexEq
        subst index
        have column := classifiedCore_vertical_column graph tagged.1 tagged.2 edgeLocal piece pieceMember vertical
        simp only [gateRole,verticalBase,verticalShift,mul_zero,add_zero] at column
        have valid : tagged.2 < graph.edges.length := List.snd_lt_of_mem_zipIdx edgeMember
        have gateBounds : 0 ≤ gateX graph tagged.2 ∧ gateX graph tagged.2 < drawingGridSize graph := by
          unfold gateX drawingGridSize
          omega
        have fanBefore := fan_block_finish_bound wellFormed fanMember
        have beforeGate : fanBlockFinish graph fanPort.vertex < gateX graph tagged.2 := by unfold gateX; omega
        exact (fan_outside_vertical_column_disjoint wellFormed orthogonal fanMember vertical gateBounds
          (Or.inl beforeGate) (storedShift := 0) (by simpa using column) fanContains coreContains).elim
    · have column := classifiedCore_vertical_column graph tagged.1 tagged.2 edgeLocal piece pieceMember vertical
      simp only [boundary,verticalBase,verticalShift,zero_add] at column
      have fanBlock := fan_block_bounds wellFormed fanMember
      have gridPositive : (0 : Int) < drawingGridSize graph := by exact_mod_cast drawingGridSize_pos graph
      exact (fan_outside_vertical_column_disjoint wellFormed orthogonal fanMember vertical
        (by omega : (0 : Int) ≤ 0 ∧ (0 : Int) < drawingGridSize graph)
        (Or.inr (by omega : (0 : Int) < fanBlockStart graph fanPort.vertex))
        (storedShift := max tagged.1.offset.1 0) (by simpa using column) fanContains coreContains).elim

end LeanTrominoes.PeriodicOrthocrossing.GeneralPorts
