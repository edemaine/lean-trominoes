/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendOrientedCoreData
import LeanTrominoes.GeneralVertexNormalizationEndpointDirections

/-! # Parent provenance and cell labels at raw bend incidences -/
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

theorem chainEdges_node_pair {V : Type*} {points : List (V × Cell)} {edge : PeriodicEdge V}
    (member : edge ∈ chainEdges points) :
    ∃ first ∈ points.dropLast, ∃ second ∈ points,
      edge = ⟨first.1,second.1,Cell.sub second.2 first.2⟩ := by
  obtain ⟨first,firstMember,second,secondMember,equal⟩ := chainEdges_node_pair_tail member
  exact ⟨first,firstMember,second,List.mem_of_mem_tail secondMember,equal⟩

end LeanTrominoes.PeriodicGraph.BendSubdivision
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision OrthogonalDrawingRefinement PeriodicOrthocrossing

theorem nodes_bend_data {V : Type*} (drawing : PeriodicGridDrawing) (parent : PeriodicEdge V × Nat)
    {entry : Vertex V × Cell} {edgeIndex pointIndex : Nat}
    (member : entry ∈ nodes parent (middle drawing parent)) (vertex : entry.1 = .bend edgeIndex pointIndex) :
    parent.2 = edgeIndex ∧ sourceCell drawing entry.1 = entry.2 := by
  simp only [nodes,List.mem_cons,List.mem_append,List.not_mem_nil,or_false] at member
  rcases member with (rfl | member) | rfl
  · cases vertex
  · obtain ⟨point,pointMember,rfl⟩ := List.mem_map.mp member
    have indices := Vertex.bend.inj vertex
    refine ⟨indices.1,?_⟩
    simp only [sourceCell,(BendSubdivision.internalPoint_lookup pointMember).2.2]
  · cases vertex

theorem chain_bend_target_cell {V : Type*} (drawing : PeriodicGridDrawing) (parent : PeriodicEdge V × Nat)
    {edge : PeriodicEdge (Vertex V)} (member : edge ∈ chainEdges (nodes parent (middle drawing parent)))
    {edgeIndex pointIndex : Nat} (target : edge.target = .bend edgeIndex pointIndex) :
    parent.2 = edgeIndex ∧ Cell.add (sourceCell drawing edge.source) edge.offset = sourceCell drawing edge.target := by
  obtain ⟨first,firstMember,second,secondMember,rfl⟩ := chainEdges_node_pair member
  have firstLabel := nodes_source_labels drawing parent firstMember
  have secondData := nodes_bend_data drawing parent secondMember target
  refine ⟨secondData.1,?_⟩
  rw [firstLabel,secondData.2]
  apply Prod.ext <;> simp only [Cell.add,Cell.sub] <;> ring

theorem chain_bend_source_parent {V : Type*} (drawing : PeriodicGridDrawing) (parent : PeriodicEdge V × Nat)
    {edge : PeriodicEdge (Vertex V)} (member : edge ∈ chainEdges (nodes parent (middle drawing parent)))
    {edgeIndex pointIndex : Nat} (sourceVertex : edge.source = .bend edgeIndex pointIndex) : parent.2 = edgeIndex := by
  have sourceMember := (chainEdges_endpoints_mem member).1
  obtain ⟨entry,entryMember,equal⟩ := List.mem_map.mp sourceMember
  exact (nodes_bend_data drawing parent entryMember (equal.trans sourceVertex)).1

theorem bend_port_parent {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {port : GraphPort (Vertex V)} (portMember : port ∈ allPorts (subdivisionGraph source drawing))
    {edgeIndex pointIndex : Nat} (vertex : port.vertex = .bend edgeIndex pointIndex) :
    (recordAt source drawing port.edgeIndex).1.1 = edgeIndex := by
  obtain ⟨tagged,taggedMember,kind⟩ := GeneralVertexNormalization.allPorts_has_edge portMember
  have recordMember := recordAt_mem (source := source) (drawing := drawing)
    (by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx taggedMember)
  obtain ⟨parent,_,piece,pieceMember,recordEqual⟩ := record_provenance recordMember
  have edgeEqual : piece.1 = tagged.1 := (congrArg Prod.snd recordEqual).symm.trans (recordAt_edge taggedMember)
  have chainMember : tagged.1 ∈ chainEdges (nodes parent (middle drawing parent)) :=
    edgeEqual ▸ List.fst_mem_of_mem_zipIdx pieceMember
  rcases kind with rfl | rfl
  · have parentIndex := chain_bend_source_parent drawing parent chainMember vertex
    have key := congrArg (fun record : (Nat × Nat) × PeriodicEdge (Vertex V) => record.1.1) recordEqual
    exact key.trans parentIndex
  · have parentIndex := (chain_bend_target_cell drawing parent chainMember vertex).1
    have key := congrArg (fun record : (Nat × Nat) × PeriodicEdge (Vertex V) => record.1.1) recordEqual
    exact key.trans parentIndex

theorem bend_target_cell {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx)
    {edgeIndex pointIndex : Nat} (target : tagged.1.target = .bend edgeIndex pointIndex) :
    Cell.add (sourceCell drawing tagged.1.source) tagged.1.offset = sourceCell drawing tagged.1.target := by
  have recordMember := recordAt_mem (source := source) (drawing := drawing)
    (by simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx member)
  obtain ⟨parent,_,piece,pieceMember,recordEqual⟩ := record_provenance recordMember
  have edgeEqual : piece.1 = tagged.1 := (congrArg Prod.snd recordEqual).symm.trans (recordAt_edge member)
  exact (chain_bend_target_cell drawing parent (edgeEqual ▸ List.fst_mem_of_mem_zipIdx pieceMember) target).2

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
