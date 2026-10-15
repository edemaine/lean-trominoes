/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealOpenSimple
import LeanTrominoes.Common.List.ListZipIdxStart

/-! # Gluing three simple open pieces, with optional closure at the outer endpoints -/
namespace LeanTrominoes.GridPolyline

theorem isRealSimple_of_three_parts {first middle last full : List Cell}
    (firstSimple : IsRealOpenSimple first) (middleSimple : IsRealOpenSimple middle) (lastSimple : IsRealOpenSimple last)
    (fullLong : 2 ≤ full.length)
    (parts : gridPolylineSegments full =
      (gridPolylineSegments first ++ gridPolylineSegments middle) ++ gridPolylineSegments last)
    {source firstJoint secondJoint target : Cell}
    (firstHead : first.head? = some source) (firstLast : first.getLast? = some firstJoint)
    (middleHead : middle.head? = some firstJoint) (middleLast : middle.getLast? = some secondJoint)
    (lastHead : last.head? = some secondJoint) (lastLast : last.getLast? = some target)
    (firstMiddleContact : ∀ point, RealContains first point → RealContains middle point → point = realCell firstJoint)
    (middleLastContact : ∀ point, RealContains middle point → RealContains last point → point = realCell secondJoint)
    (outerContact : ∀ point, RealContains first point → RealContains last point →
      point = realCell source ∧ point = realCell target) : IsRealSimple full := by
  have atHead {points : List Cell} {tagged : GridSegment × Nat} {endpoint : Cell} {point : ℝ × ℝ}
      (member : tagged ∈ (gridPolylineSegments points).zipIdx) (head : points.head? = some endpoint)
      (firstIndex : tagged.2 = 0) (equal : point = realCell endpoint) : point = realCell tagged.1.start := by
    have found := indexed_gridPolylineSegment_head member firstIndex
    have endpointEq := Option.some.inj (head.symm.trans found)
    simpa only [endpointEq] using equal
  have atLast {points : List Cell} {tagged : GridSegment × Nat} {endpoint : Cell} {point : ℝ × ℝ}
      (member : tagged ∈ (gridPolylineSegments points).zipIdx) (last : points.getLast? = some endpoint)
      (lastIndex : tagged.2+1 = (gridPolylineSegments points).length) (equal : point = realCell endpoint) :
      point = realCell tagged.1.finish := by
    have found := indexed_gridPolylineSegment_last member lastIndex
    have endpointEq := Option.some.inj (last.symm.trans found)
    simpa only [endpointEq] using equal
  have count : (gridPolylineSegments full).length = (gridPolylineSegments first).length+
      (gridPolylineSegments middle).length+(gridPolylineSegments last).length := by rw [parts]; simp; omega
  refine ⟨fullLong,?_,?_⟩
  · intro segment member
    rw [parts] at member
    rcases List.mem_append.mp member with member | member
    · rcases List.mem_append.mp member with member | member
      · exact firstSimple.2.1 segment member
      · exact middleSimple.2.1 segment member
    · exact lastSimple.2.1 segment member
  · intro firstTagged firstMember secondTagged secondMember ordered point firstContains secondContains
    rw [parts,List.zipIdx_append,List.zipIdx_append,List.length_append,Nat.zero_add] at firstMember secondMember
    simp only [Nat.zero_add] at firstMember secondMember
    rw [list_zipIdx_start_eq (gridPolylineSegments middle) (gridPolylineSegments first).length,
      list_zipIdx_start_eq (gridPolylineSegments last) ((gridPolylineSegments first).length+(gridPolylineSegments middle).length)]
      at firstMember secondMember
    rcases List.mem_append.mp firstMember with firstAB | firstC
    · rcases List.mem_append.mp firstAB with firstA | firstB
      · rcases List.mem_append.mp secondMember with secondAB | secondC
        · rcases List.mem_append.mp secondAB with secondA | secondB
          · exact Or.inl (firstSimple.2.2 firstTagged firstA secondTagged secondA ordered point firstContains secondContains)
          · obtain ⟨second,secondBM,rfl⟩ := List.mem_map.mp secondB
            have contact := firstMiddleContact point
              ⟨firstTagged.1,List.fst_mem_of_mem_zipIdx firstA,firstContains⟩
              ⟨second.1,List.fst_mem_of_mem_zipIdx secondBM,secondContains⟩
            have firstEnd := firstSimple.last_contact_index_of_last firstLast firstA (by rw [← contact]; exact firstContains)
            have secondStart := middleSimple.head_contact_index_of_head middleHead secondBM (by rw [← contact]; exact secondContains)
            exact Or.inl ⟨by dsimp only [Prod.snd]; omega,atLast firstA firstLast firstEnd contact⟩
        · obtain ⟨second,secondCM,rfl⟩ := List.mem_map.mp secondC
          have contact := outerContact point
            ⟨firstTagged.1,List.fst_mem_of_mem_zipIdx firstA,firstContains⟩
            ⟨second.1,List.fst_mem_of_mem_zipIdx secondCM,secondContains⟩
          have firstStart := firstSimple.head_contact_index_of_head firstHead firstA (by rw [← contact.1]; exact firstContains)
          have secondEnd := lastSimple.last_contact_index_of_last lastLast secondCM (by rw [← contact.2]; exact secondContains)
          exact Or.inr ⟨firstStart,by dsimp only [Prod.snd]; omega,
            atHead firstA firstHead firstStart contact.1,atLast (tagged := second) secondCM lastLast secondEnd contact.2⟩
      · obtain ⟨first,firstBM,rfl⟩ := List.mem_map.mp firstB
        rcases List.mem_append.mp secondMember with secondAB | secondC
        · rcases List.mem_append.mp secondAB with secondA | secondB
          · have secondBound := List.snd_lt_of_mem_zipIdx secondA
            dsimp only [Prod.snd] at ordered
            omega
          · obtain ⟨second,secondBM,rfl⟩ := List.mem_map.mp secondB
            have originalOrder : first.2 < second.2 := by dsimp only [Prod.snd] at ordered; omega
            have contact := middleSimple.2.2 first firstBM second secondBM originalOrder point firstContains secondContains
            exact Or.inl ⟨by dsimp only [Prod.snd]; omega,contact.2⟩
        · obtain ⟨second,secondCM,rfl⟩ := List.mem_map.mp secondC
          have contact := middleLastContact point
            ⟨first.1,List.fst_mem_of_mem_zipIdx firstBM,firstContains⟩
            ⟨second.1,List.fst_mem_of_mem_zipIdx secondCM,secondContains⟩
          have firstEnd := middleSimple.last_contact_index_of_last middleLast firstBM (by rw [← contact]; exact firstContains)
          have secondStart := lastSimple.head_contact_index_of_head lastHead secondCM (by rw [← contact]; exact secondContains)
          exact Or.inl ⟨by dsimp only [Prod.snd]; omega,atLast (tagged := first) firstBM middleLast firstEnd contact⟩
    · obtain ⟨first,firstCM,rfl⟩ := List.mem_map.mp firstC
      rcases List.mem_append.mp secondMember with secondAB | secondC
      · rcases List.mem_append.mp secondAB with secondA | secondB
        · have secondBound := List.snd_lt_of_mem_zipIdx secondA
          dsimp only [Prod.snd] at ordered
          omega
        · obtain ⟨second,secondBM,rfl⟩ := List.mem_map.mp secondB
          have secondBound := List.snd_lt_of_mem_zipIdx secondBM
          dsimp only [Prod.snd] at ordered
          omega
      · obtain ⟨second,secondCM,rfl⟩ := List.mem_map.mp secondC
        have originalOrder : first.2 < second.2 := by dsimp only [Prod.snd] at ordered; omega
        have contact := lastSimple.2.2 first firstCM second secondCM originalOrder point firstContains secondContains
        exact Or.inl ⟨by dsimp only [Prod.snd]; omega,contact.2⟩

end LeanTrominoes.GridPolyline
