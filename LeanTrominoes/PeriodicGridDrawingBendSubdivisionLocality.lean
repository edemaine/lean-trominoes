/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendSubdivision
import LeanTrominoes.PeriodicGridDrawingUnitSubdivision

/-! # Locality of the graph obtained by inserting bend vertices -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

theorem internalPoint_mem_route {drawing : PeriodicGridDrawing} {index : Nat} {entry : Cell × Nat}
    (member : entry∈internalPoints drawing index) : entry.1∈drawing.edgeRoute index :=
  List.mem_of_mem_tail (List.mem_of_mem_dropLast (List.fst_mem_of_mem_zipIdx member))

theorem chainEdges_local {V : Type*} {points : List (V × Cell)} {offset : Cell}
    (localOffset : offset.1.natAbs+offset.2.natAbs≤1)
    (labels : ∀ entry∈points, entry.2=(0,0) ∨ entry.2=offset) :
    ∀ edge∈chainEdges points, edge.span≤1 := by
  induction points using List.twoStepInduction with
  | nil | singleton => simp [chainEdges]
  | cons_cons first second rest _ induction =>
      intro edge member
      simp only [chainEdges,List.mem_cons] at member
      rcases member with rfl | member
      · exact InteriorBends.cell_difference_span (labels first (by simp))
          (labels second (by simp)) localOffset
      · exact induction second (fun entry member => labels entry (List.mem_cons_of_mem first member)) _ member

theorem subdivisionGraph_local {V : Type*} [DecidableEq V] {source : PeriodicGraph V}
    {drawing : PeriodicGridDrawing} (planar : drawing.IsRealPlanarDrawing source)
    (localDrawing : drawing.IsRealLocal source) (localGraph : source.IsLocal)
    {factor : Nat} (spacing : 2<(factor:Int)) :
    (subdivisionGraph source drawing factor).IsLocal := by
  intro edge edgeMember
  obtain ⟨tagged,taggedMember,member⟩ := List.mem_flatMap.mp edgeMember
  have localOffset := localGraph tagged.1 (List.fst_mem_of_mem_zipIdx taggedMember)
  apply chainEdges_local localOffset ?_ edge member
  intro entry entryMember
  simp only [nodes,List.mem_append,List.mem_cons,List.not_mem_nil,or_false] at entryMember
  rcases entryMember with (rfl | entryMember) | rfl
  · exact Or.inl rfl
  · obtain ⟨original,originalMember,rfl⟩ := List.mem_map.mp entryMember
    have routeMember := edgeRoute_mem_of_compatible planar.1.1 taggedMember
    have bounds := polygonal_point_in_local_rectangle localDrawing taggedMember
      (planar.1.2.1 _ routeMember).1 (internalPoint_mem_route originalMember)
    exact InteriorBends.cells_allowed spacing localOffset bounds
  · exact Or.inr rfl

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
