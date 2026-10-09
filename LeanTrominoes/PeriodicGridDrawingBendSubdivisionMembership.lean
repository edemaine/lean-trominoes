/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendSubdivisionPointLookup

/-! # Membership and index bounds for the subdivision's vertex table -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

theorem original_vertex_mem {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {factor : Nat} {vertex : V} :
    Vertex.original vertex ∈ (subdivisionGraph source drawing factor).vertices ↔ vertex ∈ source.vertices := by
  constructor
  · intro member
    simp only [subdivisionGraph,graph,List.mem_append] at member
    rcases member with original | bend
    · obtain ⟨actual,actualMember,equal⟩ := List.mem_map.mp original
      exact Vertex.original.inj equal ▸ actualMember
    · obtain ⟨parent,_,member⟩ := List.mem_flatMap.mp bend
      simp only [middle,List.map_map,Function.comp_def] at member
      obtain ⟨entry,_,equal⟩ := List.mem_map.mp member
      cases equal
  · intro member
    apply List.mem_append_left
    exact List.mem_map.mpr ⟨vertex,member,rfl⟩

theorem bend_vertex_mem_data {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {factor edgeIndex pointIndex : Nat}
    (member : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing factor).vertices) :
    ∃ parent ∈ source.edges.zipIdx, ∃ entry ∈ internalPoints drawing parent.2,
      edgeIndex=parent.2 ∧ pointIndex=entry.2 := by
  simp only [subdivisionGraph,graph,List.mem_append] at member
  rcases member with original | bend
  · obtain ⟨actual,_,equal⟩ := List.mem_map.mp original
    cases equal
  · obtain ⟨parent,parentMember,member⟩ := List.mem_flatMap.mp bend
    simp only [middle,List.map_map,Function.comp_def] at member
    obtain ⟨entry,entryMember,equal⟩ := List.mem_map.mp member
    have indices := Vertex.bend.inj equal
    exact ⟨parent,parentMember,entry,entryMember,indices.1.symm,indices.2.symm⟩

theorem bend_vertex_mem_bounds {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible source) {factor edgeIndex pointIndex : Nat}
    (member : Vertex.bend edgeIndex pointIndex ∈ (subdivisionGraph source drawing factor).vertices) :
    edgeIndex < drawing.edgeRoutes.length ∧ 0 < pointIndex ∧ pointIndex+1 < (drawing.edgeRoute edgeIndex).length := by
  obtain ⟨parent,parentMember,entry,entryMember,edgeEq,pointEq⟩ := bend_vertex_mem_data member
  have lookup := internalPoint_lookup entryMember
  rw [edgeEq,pointEq]
  refine ⟨?_,by omega,lookup.2.1⟩
  rw [compatible.2.2.1]
  simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx parentMember

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
