/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendParentPorts

/-! # Original target vertices have their parent's target-cell label -/
namespace LeanTrominoes.PeriodicGraph.BendSubdivision

theorem chainEdges_node_pair_tail {V : Type*} {points : List (V × Cell)} {edge : PeriodicEdge V}
    (member : edge ∈ chainEdges points) :
    ∃ first ∈ points.dropLast, ∃ second ∈ points.tail,
      edge = ⟨first.1,second.1,Cell.sub second.2 first.2⟩ := by
  induction points using List.twoStepInduction with
  | nil | singleton => simp [chainEdges] at member
  | cons_cons first second rest _ induction =>
      simp only [chainEdges,List.mem_cons] at member
      rcases member with rfl | member
      · exact ⟨first,by simp [List.dropLast_cons_cons],second,by simp,rfl⟩
      · obtain ⟨a,aMember,b,bMember,equal⟩ := induction second member
        exact ⟨a,by rw [List.dropLast_cons_cons]; exact List.mem_cons_of_mem _ aMember,
          b,by simpa only [List.tail_cons] using List.mem_of_mem_tail bMember,equal⟩

end LeanTrominoes.PeriodicGraph.BendSubdivision
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
