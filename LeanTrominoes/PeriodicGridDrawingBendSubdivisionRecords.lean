/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendSubdivision

/-! # Unique segment occurrence keys for the subdivision presentation -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

private theorem fstIndex {A : Type*} (values : List A) (offset : Nat) : (values.zipIdx offset).map Prod.fst=values := by
  induction values generalizing offset with
  | nil => rfl
  | cons first rest induction => simp only [List.zipIdx_cons,List.map_cons,induction]

def records {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) (factor : Nat) :
    List ((Nat × Nat) × PeriodicEdge (Vertex V)) :=
  source.edges.zipIdx.flatMap fun parent =>
    (chainEdges (nodes parent (middle drawing factor parent))).zipIdx.map fun piece =>
      ((parent.2,piece.2),piece.1)

theorem records_edges {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) (factor : Nat) :
    (records source drawing factor).map Prod.snd=(subdivisionGraph source drawing factor).edges := by
  simp only [records,List.map_flatMap,List.map_map,Function.comp_def]
  change (source.edges.zipIdx.flatMap fun parent =>
    (chainEdges (nodes parent (middle drawing factor parent))).zipIdx.map Prod.fst)=_
  simp only [fstIndex]
  rfl

theorem records_keys_unique {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) (factor : Nat) :
    ((records source drawing factor).map Prod.fst).Nodup := by
  rw [records,List.map_flatMap]
  apply List.nodup_flatMap.mpr
  constructor
  · intro parent _
    have unique := (List.nodup_zipIdx_map_snd (chainEdges (nodes parent (middle drawing factor parent)))).map
      (f := fun index => (parent.2,index)) (fun _ _ equal => congrArg Prod.snd equal)
    simpa only [List.map_map,Function.comp_def] using unique
  · have indices : source.edges.zipIdx.Pairwise (fun a b => a.2≠b.2) :=
      List.pairwise_map.mp (List.nodup_zipIdx_map_snd source.edges)
    apply indices.imp
    intro a b different key firstMember secondMember
    simp only [List.map_map,Function.comp_def] at firstMember secondMember
    obtain ⟨first,_,rfl⟩ := List.mem_map.mp firstMember
    obtain ⟨second,_,equal⟩ := List.mem_map.mp secondMember
    exact different (congrArg Prod.fst equal).symm

theorem records_length {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) (factor : Nat) :
    (records source drawing factor).length=(subdivisionGraph source drawing factor).edges.length := by
  simpa only [List.length_map] using congrArg List.length (records_edges source drawing factor)

theorem record_provenance {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {factor : Nat}
    {record : (Nat × Nat) × PeriodicEdge (Vertex V)} (member : record∈records source drawing factor) :
    ∃ parent∈source.edges.zipIdx, ∃ piece∈(chainEdges (nodes parent (middle drawing factor parent))).zipIdx,
      record=((parent.2,piece.2),piece.1) := by
  obtain ⟨parent,parentMember,pieceMember⟩ := List.mem_flatMap.mp member
  obtain ⟨piece,pieceMember,equal⟩ := List.mem_map.mp pieceMember
  exact ⟨parent,parentMember,piece,pieceMember,equal.symm⟩

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
