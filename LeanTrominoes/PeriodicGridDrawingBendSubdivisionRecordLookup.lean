/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendSubdivisionSegments

/-! # Lookup preserves unique lifted segment occurrence keys -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

def recordAt {V : Type*} (source : PeriodicGraph V) (drawing : PeriodicGridDrawing) (factor index : Nat) :
    (Nat × Nat) × PeriodicEdge (Vertex V) :=
  (records source drawing factor).getD index ((0,0),⟨.bend 0 0,.bend 0 0,(0,0)⟩)

theorem recordAt_mem {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {factor index : Nat}
    (valid : index < (subdivisionGraph source drawing factor).edges.length) :
    recordAt source drawing factor index ∈ records source drawing factor := by
  have recordValid : index < (records source drawing factor).length := by rwa [records_length]
  rw [recordAt,List.getD_eq_getElem _ _ recordValid]
  exact List.getElem_mem recordValid

theorem recordAt_edge {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {factor : Nat}
    {tagged : PeriodicEdge (Vertex V) × Nat} (member : tagged ∈ (subdivisionGraph source drawing factor).edges.zipIdx) :
    (recordAt source drawing factor tagged.2).2=tagged.1 := by
  have valid : tagged.2 < (subdivisionGraph source drawing factor).edges.length := by
    simpa only [Nat.add_zero] using List.snd_lt_of_mem_zipIdx member
  have recordValid : tagged.2 < (records source drawing factor).length := by rwa [records_length]
  have lookup := congrArg (fun edges => edges[tagged.2]?) (records_edges source drawing factor)
  rw [List.getElem?_map,List.getElem?_eq_getElem recordValid,List.mem_zipIdx_iff_getElem?.mp member] at lookup
  simp only [Option.map_some] at lookup
  rw [recordAt,List.getD_eq_getElem _ _ recordValid]
  exact Option.some.inj lookup

theorem recordAt_key_injective {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {factor first second : Nat}
    (firstValid : first < (subdivisionGraph source drawing factor).edges.length)
    (secondValid : second < (subdivisionGraph source drawing factor).edges.length)
    (equal : (recordAt source drawing factor first).1=(recordAt source drawing factor second).1) : first=second := by
  have firstRecordValid : first < (records source drawing factor).length := by rwa [records_length]
  have secondRecordValid : second < (records source drawing factor).length := by rwa [records_length]
  let keys := (records source drawing factor).map Prod.fst
  let firstIndex : Fin keys.length := ⟨first,by simp only [keys,List.length_map]; exact firstRecordValid⟩
  let secondIndex : Fin keys.length := ⟨second,by simp only [keys,List.length_map]; exact secondRecordValid⟩
  have firstGet : keys.get firstIndex=(recordAt source drawing factor first).1 := by
    simp only [keys,firstIndex,List.get_eq_getElem,List.getElem_map,recordAt,List.getD_eq_getElem _ _ firstRecordValid]
  have secondGet : keys.get secondIndex=(recordAt source drawing factor second).1 := by
    simp only [keys,secondIndex,List.get_eq_getElem,List.getElem_map,recordAt,List.getD_eq_getElem _ _ secondRecordValid]
  have indices := List.nodup_iff_injective_get.mp (records_keys_unique source drawing factor)
    (firstGet.trans (equal.trans secondGet.symm))
  exact congrArg Fin.val indices

theorem lifted_record_keys_ne {V : Type*} {source : PeriodicGraph V} {drawing : PeriodicGridDrawing} {factor : Nat}
    {first second : PeriodicEdge (Vertex V) × Nat}
    (firstMember : first ∈ (subdivisionGraph source drawing factor).edges.zipIdx)
    (secondMember : second ∈ (subdivisionGraph source drawing factor).edges.zipIdx)
    (firstCell secondCell : Cell) (different : (first.2,firstCell)≠(second.2,secondCell)) :
    ((recordAt source drawing factor first.2).1.1,(recordAt source drawing factor first.2).1.2,
      Cell.sub firstCell (sourceCell drawing factor first.1.source))≠
    ((recordAt source drawing factor second.2).1.1,(recordAt source drawing factor second.2).1.2,
      Cell.sub secondCell (sourceCell drawing factor second.1.source)) := by
  intro equal
  have keysEqual : (recordAt source drawing factor first.2).1=(recordAt source drawing factor second.2).1 :=
    Prod.ext (congrArg (fun key : Nat × Nat × Cell => key.1) equal)
      (congrArg (fun key : Nat × Nat × Cell => key.2.1) equal)
  have indexEq := recordAt_key_injective (by simpa using List.snd_lt_of_mem_zipIdx firstMember)
    (by simpa using List.snd_lt_of_mem_zipIdx secondMember) keysEqual
  have edgeEq : first.1=second.1 := (recordAt_edge firstMember).symm.trans
    (by rw [indexEq]; exact recordAt_edge secondMember)
  have copiesEqual := congrArg (fun key : Nat × Nat × Cell => key.2.2) equal
  rw [edgeEq] at copiesEqual
  have cellEq : firstCell=secondCell := by
    have x := congrArg Prod.fst copiesEqual
    have y := congrArg Prod.snd copiesEqual
    exact Prod.ext (by simp only [Cell.sub] at x; omega) (by simp only [Cell.sub] at y; omega)
  exact different (Prod.ext indexEq cellEq)

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
