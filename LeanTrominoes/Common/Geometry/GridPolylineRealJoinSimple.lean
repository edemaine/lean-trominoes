/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealJoinOpenSimple

/-! # Closing two open simple routes at their two common endpoints -/
namespace LeanTrominoes.GridPolyline
open PeriodicOrthocrossing

theorem isRealSimple_join_closed {first second : List Cell} {joint outer : Cell}
    (firstSimple : IsRealOpenSimple first) (secondSimple : IsRealOpenSimple second)
    (firstLast : first.getLast? = some joint) (secondHead : second.head? = some joint)
    (firstHead : first.head? = some outer) (secondLast : second.getLast? = some outer)
    (contacts : ∀ point, RealContains first point → RealContains second point →
      point=realCell joint ∨ point=realCell outer) :
    IsRealSimple (joinPolylines first second) := by
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
      · exact Or.inl (firstSimple.2.2 firstTagged firstA secondTagged secondA ordered point firstContains secondContains)
      · obtain ⟨secondPiece,secondBM,rfl⟩ := List.mem_map.mp secondB
        have contact := contacts point
          ⟨firstTagged.1,List.fst_mem_of_mem_zipIdx firstA,firstContains⟩
          ⟨secondPiece.1,List.fst_mem_of_mem_zipIdx secondBM,secondContains⟩
        rcases contact with atJoint | atOuter
        · have firstEnd := firstSimple.last_contact_index_of_last firstLast firstA (by rw [← atJoint]; exact firstContains)
          have secondStart := secondSimple.head_contact_index_of_head secondHead secondBM (by rw [← atJoint]; exact secondContains)
          have endAt := indexed_gridPolylineSegment_last firstA firstEnd
          have endpointEq := Option.some.inj (firstLast.symm.trans endAt)
          exact Or.inl ⟨by dsimp only [Prod.snd]; omega,by simpa only [endpointEq] using atJoint⟩
        · have firstStart := firstSimple.head_contact_index_of_head firstHead firstA (by rw [← atOuter]; exact firstContains)
          have secondEnd := secondSimple.last_contact_index_of_last secondLast secondBM (by rw [← atOuter]; exact secondContains)
          have startAt := indexed_gridPolylineSegment_head firstA firstStart
          have endAt := indexed_gridPolylineSegment_last secondBM secondEnd
          have sourceEq := Option.some.inj (firstHead.symm.trans startAt)
          have targetEq := Option.some.inj (secondLast.symm.trans endAt)
          exact Or.inr ⟨firstStart,by rw [parts,List.length_append]; dsimp only [Prod.snd]; omega,
            by simpa only [sourceEq] using atOuter,by simpa only [targetEq] using atOuter⟩
    · obtain ⟨firstPiece,firstBM,rfl⟩ := List.mem_map.mp firstB
      rcases List.mem_append.mp secondMember with secondA | secondB
      · have valid := List.snd_lt_of_mem_zipIdx secondA
        dsimp only [Prod.snd] at ordered
        omega
      · obtain ⟨secondPiece,secondBM,rfl⟩ := List.mem_map.mp secondB
        have originalOrder : firstPiece.2 < secondPiece.2 := by dsimp only [Prod.snd] at ordered; omega
        have contact := secondSimple.2.2 firstPiece firstBM secondPiece secondBM originalOrder point firstContains secondContains
        exact Or.inl ⟨by dsimp only [Prod.snd]; omega,contact.2⟩

end LeanTrominoes.GridPolyline
