/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealOpenSimple
import LeanTrominoes.Common.Geometry.GridPolylineRealAlgebra
import LeanTrominoes.Common.List.ListZipIdxStart

/-! # Joining simple open routes at their sole common point -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

theorem isRealOpenSimple_join {first second : List Cell} {joint : Cell}
    (firstSimple : IsRealOpenSimple first) (secondSimple : IsRealOpenSimple second)
    (firstLast : first.getLast? = some joint) (secondHead : second.head? = some joint)
    (contacts : ∀ point, RealContains first point → RealContains second point → point = realCell joint) :
    IsRealOpenSimple (joinPolylines first second) := by
  have parts := gridPolylineSegments_joinPolylines firstLast secondHead
  refine ⟨?_,?_,?_⟩
  · simp only [joinPolylines,List.length_append,List.length_tail]
    have firstLong := firstSimple.1
    have secondLong := secondSimple.1
    omega
  · intro segment member
    rw [parts] at member
    rcases List.mem_append.mp member with member | member
    · exact firstSimple.2.1 segment member
    · exact secondSimple.2.1 segment member
  · intro firstTagged firstMember secondTagged secondMember ordered point firstContains secondContains
    rw [parts,List.zipIdx_append,Nat.zero_add,
      list_zipIdx_start_eq (gridPolylineSegments second) (gridPolylineSegments first).length]
      at firstMember secondMember
    rcases List.mem_append.mp firstMember with firstA | firstB
    · rcases List.mem_append.mp secondMember with secondA | secondB
      · exact firstSimple.2.2 firstTagged firstA secondTagged secondA ordered point firstContains secondContains
      · obtain ⟨second,secondBM,rfl⟩ := List.mem_map.mp secondB
        have contact := contacts point
          ⟨firstTagged.1,List.fst_mem_of_mem_zipIdx firstA,firstContains⟩
          ⟨second.1,List.fst_mem_of_mem_zipIdx secondBM,secondContains⟩
        have firstEnd := firstSimple.last_contact_index_of_last firstLast firstA (by rw [← contact]; exact firstContains)
        have secondStart := secondSimple.head_contact_index_of_head secondHead secondBM (by rw [← contact]; exact secondContains)
        have endAt := indexed_gridPolylineSegment_last firstA firstEnd
        have endpointEq := Option.some.inj (firstLast.symm.trans endAt)
        exact ⟨by dsimp only [Prod.snd]; omega,by simpa only [endpointEq] using contact⟩
    · obtain ⟨first,firstBM,rfl⟩ := List.mem_map.mp firstB
      rcases List.mem_append.mp secondMember with secondA | secondB
      · have valid := List.snd_lt_of_mem_zipIdx secondA
        dsimp only [Prod.snd] at ordered
        omega
      · obtain ⟨second,secondBM,rfl⟩ := List.mem_map.mp secondB
        have originalOrder : first.2 < second.2 := by dsimp only [Prod.snd] at ordered; omega
        have contact := secondSimple.2.2 first firstBM second secondBM originalOrder point firstContains secondContains
        exact ⟨by dsimp only [Prod.snd]; omega,contact.2⟩

end LeanTrominoes.GridPolyline
