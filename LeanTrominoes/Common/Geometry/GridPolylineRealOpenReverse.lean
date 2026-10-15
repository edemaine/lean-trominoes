/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealOpenSimple
import LeanTrominoes.Common.Geometry.GridPolylineRealAlgebra

/-! # Reversing an open simple route preserves its geometric simplicity -/
namespace LeanTrominoes

theorem indexed_gridPolylineSegment_reverse {route : List Cell} {tagged : GridSegment × Nat}
    (member : tagged ∈ (gridPolylineSegments route.reverse).zipIdx) :
    (tagged.1.reverse,(gridPolylineSegments route).length-1-tagged.2) ∈ (gridPolylineSegments route).zipIdx := by
  have valid := List.snd_lt_of_mem_zipIdx member
  rw [gridPolylineSegments_reverse] at valid
  simp only [List.length_map,List.length_reverse] at valid
  have element := List.mem_zipIdx_iff_getElem?.mp member
  rw [gridPolylineSegments_reverse,List.getElem?_map,List.getElem?_reverse valid] at element
  have reversed := congrArg (Option.map GridSegment.reverse) element
  simp only [Option.map_map,Option.map_some] at reversed
  have involutive : GridSegment.reverse ∘ GridSegment.reverse = id := by
    funext segment
    cases segment
    rfl
  rw [involutive,Option.map_id] at reversed
  exact List.mem_zipIdx_iff_getElem?.mpr reversed

namespace GridPolyline

theorem IsRealOpenSimple.reverse {route : List Cell} (simple : IsRealOpenSimple route) : IsRealOpenSimple route.reverse := by
  refine ⟨by simpa using simple.1,?_,?_⟩
  · intro segment member
    rw [gridPolylineSegments_reverse] at member
    obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
    intro equal
    exact simple.2.1 old (List.mem_reverse.mp oldMember) (by simpa only [GridSegment.reverse] using equal.symm)
  · intro first firstMember last lastMember ordered point firstContains lastContains
    have firstOld := indexed_gridPolylineSegment_reverse firstMember
    have lastOld := indexed_gridPolylineSegment_reverse lastMember
    have firstValid := List.snd_lt_of_mem_zipIdx firstMember
    have lastValid := List.snd_lt_of_mem_zipIdx lastMember
    rw [gridPolylineSegments_reverse] at firstValid lastValid
    simp only [List.length_map,List.length_reverse] at firstValid lastValid
    have oldOrder : (gridPolylineSegments route).length-1-last.2 < (gridPolylineSegments route).length-1-first.2 := by omega
    have contact := simple.2.2 _ lastOld _ firstOld oldOrder point
      ((GridSegment.realContains_reverse _ _).mpr lastContains) ((GridSegment.realContains_reverse _ _).mpr firstContains)
    have adjacent : first.2+1 = last.2 := by omega
    have joint := indexed_gridPolylineSegments_consecutive firstMember lastMember adjacent
    refine ⟨adjacent,?_⟩
    simpa only [GridSegment.reverse,← joint] using contact.2

end GridPolyline
end LeanTrominoes
