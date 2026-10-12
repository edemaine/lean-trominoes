/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendParentPorts

/-! # Original target vertices have their parent's target-cell label -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision

theorem nodes_original_target_cell {V : Type*} (drawing : PeriodicGridDrawing) (parent : PeriodicEdge V × Nat)
    {entry : Vertex V × Cell} {value : V}
    (member : entry ∈ (nodes parent (middle drawing parent)).tail) (vertex : entry.1 = .original value) :
    entry.2 = parent.1.offset := by
  simp only [nodes,List.cons_append,List.tail_cons,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at member
  rcases member with member | rfl
  · obtain ⟨point,_,rfl⟩ := List.mem_map.mp member
    cases vertex
  · rfl

theorem chain_original_target_cell {V : Type*} (drawing : PeriodicGridDrawing) (parent : PeriodicEdge V × Nat)
    {edge : PeriodicEdge (Vertex V)} (member : edge ∈ chainEdges (nodes parent (middle drawing parent)))
    {value : V} (target : edge.target = .original value) :
    Cell.add (sourceCell drawing edge.source) edge.offset = parent.1.offset := by
  obtain ⟨first,firstMember,second,secondMember,rfl⟩ := chainEdges_node_pair_tail member
  have firstLabel := nodes_source_labels drawing parent firstMember
  have secondLabel := nodes_original_target_cell drawing parent secondMember target
  rw [firstLabel,← secondLabel]
  apply Prod.ext <;> simp only [Cell.add,Cell.sub] <;> ring

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
