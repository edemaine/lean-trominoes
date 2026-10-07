/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRealSimpleCertificate
import LeanTrominoes.GridPolylineSegmentIndices

/-! # Simple open routes and rigidity of their endpoint contacts -/
namespace LeanTrominoes

theorem realCell_injective : Function.Injective realCell := by
  intro first second equal
  have x := congrArg Prod.fst equal
  have y := congrArg Prod.snd equal
  simp only [realCell,Prod.fst,Prod.snd] at x y
  exact Prod.ext (by exact_mod_cast x) (by exact_mod_cast y)

namespace GridPolyline

def IsRealOpenSimple (route : List Cell) : Prop :=
  2 ≤ route.length ∧
    (∀ segment ∈ gridPolylineSegments route, segment.start ≠ segment.finish) ∧
    ∀ first ∈ (gridPolylineSegments route).zipIdx,
      ∀ second ∈ (gridPolylineSegments route).zipIdx, first.2 < second.2 →
        ∀ point : ℝ × ℝ, first.1.RealContains point → second.1.RealContains point →
          first.2+1 = second.2 ∧ point = realCell first.1.finish

theorem isRealOpenSimple_of_box_certificate {route : List Cell} (certificate : SimpleBoxCertificate route) :
    IsRealOpenSimple route := by
  refine ⟨certificate.1,certificate.2.1,?_⟩
  intro first firstMember second secondMember ordered point firstContains secondContains
  have checked := certificate.2.2 first firstMember second secondMember ordered
    (GridSegment.real_boxes_overlap_of_real_contacts firstContains secondContains)
  exact ⟨checked.1,GridSegment.real_intersection_eq_of_box_certificate checked.2 firstContains secondContains⟩

theorem IsRealOpenSimple.isRealSimple {route : List Cell} (simple : IsRealOpenSimple route) : IsRealSimple route := by
  refine ⟨simple.1,simple.2.1,?_⟩
  intro first firstMember second secondMember ordered point firstContains secondContains
  exact Or.inl (simple.2.2 first firstMember second secondMember ordered point firstContains secondContains)

theorem IsRealOpenSimple.head_contact_index {route : List Cell} (simple : IsRealOpenSimple route)
    {firstSegment : GridSegment} (firstMember : (firstSegment,0) ∈ (gridPolylineSegments route).zipIdx)
    {tagged : GridSegment × Nat} (member : tagged ∈ (gridPolylineSegments route).zipIdx)
    (contains : tagged.1.RealContains (realCell firstSegment.start)) : tagged.2 = 0 := by
  by_contra different
  have contact := simple.2.2 (firstSegment,0) firstMember tagged member (by omega)
    (realCell firstSegment.start) (GridSegment.realContains_start firstSegment) contains
  have equal : firstSegment.start = firstSegment.finish := realCell_injective contact.2
  exact simple.2.1 firstSegment (List.fst_mem_of_mem_zipIdx firstMember) equal

theorem IsRealOpenSimple.last_contact_index {route : List Cell} (simple : IsRealOpenSimple route)
    {lastTagged : GridSegment × Nat} (lastMember : lastTagged ∈ (gridPolylineSegments route).zipIdx)
    (lastIndex : lastTagged.2+1 = (gridPolylineSegments route).length)
    {tagged : GridSegment × Nat} (member : tagged ∈ (gridPolylineSegments route).zipIdx)
    (contains : tagged.1.RealContains (realCell lastTagged.1.finish)) : tagged.2 = lastTagged.2 := by
  have valid : tagged.2 < (gridPolylineSegments route).length := List.snd_lt_of_mem_zipIdx member
  by_contra different
  have ordered : tagged.2 < lastTagged.2 := by omega
  have contact := simple.2.2 tagged member lastTagged lastMember ordered (realCell lastTagged.1.finish)
    contains (GridSegment.realContains_finish lastTagged.1)
  have boundary := indexed_gridPolylineSegments_consecutive member lastMember contact.1
  rw [boundary] at contact
  have equal : lastTagged.1.start = lastTagged.1.finish := realCell_injective contact.2.symm
  exact simple.2.1 lastTagged.1 (List.fst_mem_of_mem_zipIdx lastMember) equal

theorem IsRealOpenSimple.head_contact_index_of_head {route : List Cell} (simple : IsRealOpenSimple route)
    {endpoint : Cell} (head : route.head? = some endpoint)
    {tagged : GridSegment × Nat} (member : tagged ∈ (gridPolylineSegments route).zipIdx)
    (contains : tagged.1.RealContains (realCell endpoint)) : tagged.2 = 0 := by
  have long := simple.1
  have positive : 0 < (gridPolylineSegments route).length := by rw [gridPolylineSegments_length]; omega
  let firstSegment := (gridPolylineSegments route)[0]'positive
  have firstMember : (firstSegment,0) ∈ (gridPolylineSegments route).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem positive]
  have firstEnds := indexed_gridPolylineSegment_endpoints firstMember
  have zeroGet : route[0]? = route.head? := by cases route <;> rfl
  rw [zeroGet,head] at firstEnds
  have endpointEq : endpoint = firstSegment.start := Option.some.inj firstEnds.1
  rw [endpointEq] at contains
  exact simple.head_contact_index firstMember member contains

theorem IsRealOpenSimple.last_contact_index_of_last {route : List Cell} (simple : IsRealOpenSimple route)
    {endpoint : Cell} (last : route.getLast? = some endpoint)
    {tagged : GridSegment × Nat} (member : tagged ∈ (gridPolylineSegments route).zipIdx)
    (contains : tagged.1.RealContains (realCell endpoint)) : tagged.2+1 = (gridPolylineSegments route).length := by
  have long := simple.1
  have positive : 0 < (gridPolylineSegments route).length := by rw [gridPolylineSegments_length]; omega
  let index := (gridPolylineSegments route).length-1
  have valid : index < (gridPolylineSegments route).length := by dsimp only [index]; omega
  let lastSegment := (gridPolylineSegments route)[index]'valid
  have lastMember : (lastSegment,index) ∈ (gridPolylineSegments route).zipIdx := by
    rw [List.mem_zipIdx_iff_getElem?,List.getElem?_eq_getElem valid]
  have lastIndex : index+1 = (gridPolylineSegments route).length := by dsimp only [index]; omega
  have lastEnds := indexed_gridPolylineSegment_endpoints lastMember
  have endpointIndex : route.length-1 = index+1 := by rw [lastIndex,gridPolylineSegments_length]
  have lastGet : route.getLast? = some lastSegment.finish := by
    rw [List.getLast?_eq_getElem?,endpointIndex]
    exact lastEnds.2
  have endpointEq : endpoint = lastSegment.finish := Option.some.inj (last.symm.trans lastGet)
  rw [endpointEq] at contains
  have indexEq := simple.last_contact_index lastMember lastIndex member contains
  simpa only [indexEq] using lastIndex

end GridPolyline
end LeanTrominoes
