/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRealSimpleEndpointIndices

/-! # A simple polygonal route visits every internal point only once -/
namespace LeanTrominoes.GridPolyline

theorem indexed_segment_at_point {route : List Cell} {index : Nat} (valid : index+1<route.length) :
    ∃ segment : GridSegment, (segment,index)∈(gridPolylineSegments route).zipIdx ∧
      segment.start=route[index] ∧ segment.finish=route[index+1] := by
  let segment : GridSegment := ⟨route[index]'(by omega),route[index+1]⟩
  refine ⟨segment,?_,rfl,rfl⟩
  rw [List.mem_zipIdx_iff_getElem?,gridPolylineSegments_getElem?_eq_some_iff]
  exact ⟨List.getElem?_eq_getElem (by omega),List.getElem?_eq_getElem valid⟩

theorem IsRealSimple.point_indices_eq {route : List Cell} (simple : IsRealSimple route)
    {first second : Nat} (firstValid : first+1<route.length) (secondValid : second+1<route.length)
    (same : route[first]=route[second]) : first=second := by
  have orderedImpossible {a b : Nat} (av : a+1<route.length) (bv : b+1<route.length)
      (ordered : a<b) (same : route[a]=route[b]) : False := by
    obtain ⟨first,fm,fs,_⟩ := indexed_segment_at_point av
    obtain ⟨second,sm,ss,_⟩ := indexed_segment_at_point bv
    have starts : first.start=second.start := fs.trans (same.trans ss.symm)
    have firstContains := GridSegment.realContains_start first
    have secondContains : second.RealContains (realCell first.start) := by
      rw [starts]
      exact GridSegment.realContains_start second
    rcases simple.2.2 (first,a) fm (second,b) sm ordered (realCell first.start) firstContains secondContains with adjacent | closed
    · exact simple.2.1 first (List.fst_mem_of_mem_zipIdx fm) (realCell_injective adjacent.2)
    · exact simple.2.1 second (List.fst_mem_of_mem_zipIdx sm)
        (starts.symm.trans (realCell_injective closed.2.2.2))
  rcases lt_trichotomy first second with ordered | equal | ordered
  · exact (orderedImpossible firstValid secondValid ordered same).elim
  · exact equal
  · exact (orderedImpossible secondValid firstValid ordered same.symm).elim

theorem IsRealSimple.dropLast_nodup {route : List Cell} (simple : IsRealSimple route) : route.dropLast.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro first second equal
  have firstValid : first.val+1<route.length := by have := first.isLt; simp only [List.length_dropLast] at this; omega
  have secondValid : second.val+1<route.length := by have := second.isLt; simp only [List.length_dropLast] at this; omega
  have pointsEqual : route[first.val]=route[second.val] := by
    simpa only [List.get_eq_getElem,List.getElem_dropLast] using equal
  exact Fin.ext (simple.point_indices_eq firstValid secondValid pointsEqual)

theorem IsRealSimple.internal_point_not_endpoint {route : List Cell} (simple : IsRealSimple route)
    {index : Nat} (positive : 0 < index) (valid : index+1<route.length) :
    ¬RealIsEndpoint route (realCell route[index]) := by
  intro endpoint
  obtain ⟨segment,member,start,_⟩ := indexed_segment_at_point valid
  have contains : segment.RealContains (realCell route[index]) := by rw [← start]; exact GridSegment.realContains_start segment
  rcases simple.endpoint_contact_piece endpoint member contains with atHead | atLast
  · omega
  · exact simple.2.1 segment (List.fst_mem_of_mem_zipIdx member) (start.trans atLast.2.symm)

end LeanTrominoes.GridPolyline
