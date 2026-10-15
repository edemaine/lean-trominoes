/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealOpenSimple

/-! # Only the first and last pieces of a simple route can visit an endpoint -/
namespace LeanTrominoes.GridPolyline

theorem IsRealSimple.head_contact_piece {route : List Cell} (simple : IsRealSimple route)
    {endpoint : Cell} (head : route.head? = some endpoint)
    {tagged : GridSegment × Nat} (member : tagged ∈ (gridPolylineSegments route).zipIdx)
    (contains : tagged.1.RealContains (realCell endpoint)) :
    (tagged.2 = 0 ∧ tagged.1.start = endpoint) ∨
      (tagged.2+1 = (gridPolylineSegments route).length ∧ tagged.1.finish = endpoint) := by
  by_cases first : tagged.2 = 0
  · have atHead := indexed_gridPolylineSegment_head member first
    exact Or.inl ⟨first,Option.some.inj (atHead.symm.trans head)⟩
  · have long := simple.1
    have positive : 0 < (gridPolylineSegments route).length := by rw [gridPolylineSegments_length]; omega
    let firstSegment := (gridPolylineSegments route)[0]'positive
    have firstMember : (firstSegment,0) ∈ (gridPolylineSegments route).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem positive]
    have atHead := indexed_gridPolylineSegment_head firstMember rfl
    have source : firstSegment.start = endpoint := Option.some.inj (atHead.symm.trans head)
    have contact := simple.2.2 (firstSegment,0) firstMember tagged member (by omega)
      (realCell endpoint) (by simpa [realCell,source] using GridSegment.realContains_start firstSegment) contains
    rcases contact with adjacent | closed
    · have finish := realCell_injective adjacent.2
      exact (simple.2.1 firstSegment (List.fst_mem_of_mem_zipIdx firstMember) (source.trans finish)).elim
    · exact Or.inr ⟨closed.2.1,(realCell_injective closed.2.2.2).symm⟩

theorem IsRealSimple.last_contact_piece {route : List Cell} (simple : IsRealSimple route)
    {endpoint : Cell} (last : route.getLast? = some endpoint)
    {tagged : GridSegment × Nat} (member : tagged ∈ (gridPolylineSegments route).zipIdx)
    (contains : tagged.1.RealContains (realCell endpoint)) :
    (tagged.2 = 0 ∧ tagged.1.start = endpoint) ∨
      (tagged.2+1 = (gridPolylineSegments route).length ∧ tagged.1.finish = endpoint) := by
  by_cases final : tagged.2+1 = (gridPolylineSegments route).length
  · have atLast := indexed_gridPolylineSegment_last member final
    exact Or.inr ⟨final,Option.some.inj (atLast.symm.trans last)⟩
  · have long := simple.1
    have positive : 0 < (gridPolylineSegments route).length := by rw [gridPolylineSegments_length]; omega
    let index := (gridPolylineSegments route).length-1
    have valid : index < (gridPolylineSegments route).length := by dsimp only [index]; omega
    let lastSegment := (gridPolylineSegments route)[index]'valid
    have lastMember : (lastSegment,index) ∈ (gridPolylineSegments route).zipIdx := by
      rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem valid]
    have lastIndex : index+1 = (gridPolylineSegments route).length := by dsimp only [index]; omega
    have atLast := indexed_gridPolylineSegment_last lastMember lastIndex
    have target : lastSegment.finish = endpoint := Option.some.inj (atLast.symm.trans last)
    have bound := List.snd_lt_of_mem_zipIdx member
    have ordered : tagged.2 < index := by omega
    have contact := simple.2.2 tagged member (lastSegment,index) lastMember ordered (realCell endpoint)
      contains (by simpa [realCell,target] using GridSegment.realContains_finish lastSegment)
    rcases contact with adjacent | closed
    · have boundary := indexed_gridPolylineSegments_consecutive member lastMember adjacent.1
      have finish := realCell_injective adjacent.2
      exact (simple.2.1 lastSegment (List.fst_mem_of_mem_zipIdx lastMember)
        (boundary.symm.trans (finish.symm.trans target.symm))).elim
    · exact Or.inl ⟨closed.1,(realCell_injective closed.2.2.1).symm⟩

theorem IsRealSimple.endpoint_contact_piece {route : List Cell} (simple : IsRealSimple route)
    {endpoint : Cell} (isEndpoint : RealIsEndpoint route (realCell endpoint))
    {tagged : GridSegment × Nat} (member : tagged ∈ (gridPolylineSegments route).zipIdx)
    (contains : tagged.1.RealContains (realCell endpoint)) :
    (tagged.2 = 0 ∧ tagged.1.start = endpoint) ∨
      (tagged.2+1 = (gridPolylineSegments route).length ∧ tagged.1.finish = endpoint) := by
  rcases isEndpoint with ⟨actual,head,equal⟩ | ⟨actual,last,equal⟩
  · have same := realCell_injective equal
    subst actual
    exact simple.head_contact_piece head member contains
  · have same := realCell_injective equal
    subst actual
    exact simple.last_contact_piece last member contains

end LeanTrominoes.GridPolyline
