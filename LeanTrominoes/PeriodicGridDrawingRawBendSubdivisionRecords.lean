/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingRawBendSubdivisionSegments

/-! # Unique original-piece keys for the raw subdivision -/
namespace LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
open PeriodicGraph.BendSubdivision

def records {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) :
    List ((Nat × Nat) × PeriodicEdge (Vertex V)) :=
  source.edges.zipIdx.flatMap fun parent =>
    (chainEdges (nodes parent (middle drawing parent))).zipIdx.map fun piece => ((parent.2,piece.2),piece.1)

theorem records_edges {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) :
    (records source drawing).map Prod.snd = (subdivisionGraph source drawing).edges := by
  simp only [records,List.map_flatMap,List.map_map,Function.comp_def]
  change (source.edges.zipIdx.flatMap fun parent => (chainEdges (nodes parent (middle drawing parent))).zipIdx.map Prod.fst) = _
  simp only [List.zipIdx_map_fst]
  rfl

theorem records_keys_unique {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) :
    ((records source drawing).map Prod.fst).Nodup := by
  rw [records,List.map_flatMap]
  apply List.nodup_flatMap.mpr
  constructor
  · intro parent _
    have unique := (List.nodup_zipIdx_map_snd (chainEdges (nodes parent (middle drawing parent)))).map
      (f := fun index => (parent.2,index)) (fun _ _ equal => congrArg Prod.snd equal)
    simpa only [List.map_map,Function.comp_def] using unique
  · have indices : source.edges.zipIdx.Pairwise (fun a b => a.2 ≠ b.2) :=
      List.pairwise_map.mp (List.nodup_zipIdx_map_snd source.edges)
    apply indices.imp
    intro a b different key firstMember secondMember
    simp only [List.map_map,Function.comp_def] at firstMember secondMember
    obtain ⟨first,_,rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨second,_,equal⟩ := List.mem_map.mp secondMember
    exact different (congrArg Prod.fst equal).symm

theorem records_length {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) :
    (records source drawing).length = (subdivisionGraph source drawing).edges.length := by
  simpa only [List.length_map] using congrArg List.length (records_edges source drawing)

theorem record_provenance {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {record : (Nat × Nat) × PeriodicEdge (Vertex V)} (member : record ∈ records source drawing) :
    ∃ parent ∈ source.edges.zipIdx, ∃ piece ∈ (chainEdges (nodes parent (middle drawing parent))).zipIdx,
      record = ((parent.2,piece.2),piece.1) := by
  obtain ⟨parent,parentMember,pieceMember⟩ := List.mem_flatMap.mp member
  obtain ⟨piece,pieceMember,equal⟩ := List.mem_map.mp pieceMember
  exact ⟨parent,parentMember,piece,pieceMember,equal.symm⟩

def recordAt {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) (index : Nat) :
    (Nat × Nat) × PeriodicEdge (Vertex V) :=
  (records source drawing).getD index ((0,0),⟨.bend 0 0,.bend 0 0,(0,0)⟩)

theorem recordAt_mem {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {index : Nat}
    (valid : index < (subdivisionGraph source drawing).edges.length) : recordAt source drawing index ∈ records source drawing := by
  have recordValid : index < (records source drawing).length := by rwa [records_length]
  rw [recordAt,List.getD_eq_getElem _ _ recordValid]
  exact List.getElem_mem recordValid

theorem recordAt_edge {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing).edges.zipIdx) :
    (recordAt source drawing tagged.2).2 = tagged.1 := by
  have valid : tagged.2 < (subdivisionGraph source drawing).edges.length := by
    simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx member
  have recordValid : tagged.2 < (records source drawing).length := by rwa [records_length]
  have lookup := congrArg (fun edges => edges[tagged.2]?) (records_edges source drawing)
  rw [List.getElem?_map,List.getElem?_eq_getElem recordValid,List.mem_zipIdx_iff_getElem?.mp member] at lookup
  simp only [Option.map_some] at lookup
  rw [recordAt,List.getD_eq_getElem _ _ recordValid]
  exact Option.some.inj lookup

theorem recordAt_key_injective {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {first second : Nat}
    (firstValid : first < (subdivisionGraph source drawing).edges.length)
    (secondValid : second < (subdivisionGraph source drawing).edges.length)
    (equal : (recordAt source drawing first).1 = (recordAt source drawing second).1) : first = second := by
  rw [← records_length] at firstValid secondValid
  apply ((records_keys_unique source drawing).getElem_inj_iff
    (hi := by simpa only [List.length_map] using firstValid)
    (hj := by simpa only [List.length_map] using secondValid)).mp
  simpa only [List.getElem_map,recordAt,List.getD_eq_getElem _ _ firstValid,
    List.getD_eq_getElem _ _ secondValid] using equal

theorem lifted_record_keys_ne {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing).edges.zipIdx)
    (firstCell secondCell : Cell) (different : (first.2,firstCell) ≠ (second.2,secondCell)) :
    ((recordAt source drawing first.2).1.1,(recordAt source drawing first.2).1.2,Cell.sub firstCell (sourceCell drawing first.1.source)) ≠
      ((recordAt source drawing second.2).1.1,(recordAt source drawing second.2).1.2,Cell.sub secondCell (sourceCell drawing second.1.source)) := by
  intro equal
  have keysEqual : (recordAt source drawing first.2).1 = (recordAt source drawing second.2).1 :=
    Prod.ext (congrArg (fun key : Nat × Nat × Cell => key.1) equal) (congrArg (fun key : Nat × Nat × Cell => key.2.1) equal)
  have indexEq := recordAt_key_injective (by simpa using List.snd_lt_of_mem_zipIdx firstMember)
    (by simpa using List.snd_lt_of_mem_zipIdx secondMember) keysEqual
  have edgeEq : first.1 = second.1 := (recordAt_edge firstMember).symm.trans (by rw [indexEq]; exact recordAt_edge secondMember)
  have copiesEqual := congrArg (fun key : Nat × Nat × Cell => key.2.2) equal
  rw [edgeEq] at copiesEqual
  exact different (Prod.ext indexEq (Cell.sub_right_injective _ copiesEqual))

theorem record_segment_in_original_route {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (valid : drawing.IsRealDrawing source) {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing) :
    (absoluteSegment (position source drawing) drawing.gridSize (sourceCell drawing) record.2,record.1.2) ∈
      (gridPolylineSegments (drawing.edgeRoute record.1.1)).zipIdx := by
  obtain ⟨parent,parentMember,piece,pieceMember,rfl⟩ := record_provenance member
  exact indexed_absolute_segment valid parentMember pieceMember

theorem record_parent_index_valid {V : Type*} [DecidableEq V] {source : PeriodicGraph V} {drawing : PeriodicGridDrawing}
    (compatible : drawing.IsCompatible source) {record : (Nat × Nat) × PeriodicEdge (Vertex V)}
    (member : record ∈ records source drawing) : record.1.1 < drawing.edgeRoutes.length := by
  obtain ⟨parent,parentMember,piece,_,rfl⟩ := record_provenance member
  rw [compatible.2.2.1]
  simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx parentMember

end LeanTrominoes.PeriodicGridDrawing.RawBendSubdivision
