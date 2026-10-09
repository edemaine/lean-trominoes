/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRealSimpleEndpointIndices

/-! # Transporting the contact order of a simple route to replacement pieces -/
namespace LeanTrominoes.GridPolyline

theorem realEndpoint_of_prescribed_endpoints {route : List Cell} {first last : Cell}
    (head : route.head?=some first) (finish : route.getLast?=some last) {p : ℝ × ℝ}
    (endpoint : RealIsEndpoint route p) : p=realCell first ∨ p=realCell last := by
  rcases endpoint with ⟨actual,atHead,equal⟩ | ⟨actual,atLast,equal⟩
  · exact Or.inl (equal.trans (congrArg realCell (Option.some.inj (atHead.symm.trans head))))
  · exact Or.inr (equal.trans (congrArg realCell (Option.some.inj (atLast.symm.trans finish))))

theorem IsRealSimple.replacement_contacts {route : List Cell} (simple : IsRealSimple route)
    (transform : Cell → Cell) (injective : Function.Injective transform)
    {first second : GridSegment × Nat}
    (firstMember : first ∈ (gridPolylineSegments route).zipIdx)
    (secondMember : second ∈ (gridPolylineSegments route).zipIdx) (ordered : first.2 < second.2)
    {p : ℝ × ℝ}
    (firstEndpoint : p=realCell (transform first.1.start) ∨ p=realCell (transform first.1.finish))
    (secondEndpoint : p=realCell (transform second.1.start) ∨ p=realCell (transform second.1.finish)) :
    (first.2+1=second.2 ∧ p=realCell (transform first.1.finish)) ∨
      (first.2=0 ∧ second.2+1=(gridPolylineSegments route).length ∧
        p=realCell (transform first.1.start) ∧ p=realCell (transform second.1.finish)) := by
  obtain ⟨a,firstContains,pointEq⟩ : ∃ a : Cell,first.1.RealContains (realCell a) ∧ p=realCell (transform a) := by
    rcases firstEndpoint with atStart | atFinish
    · exact ⟨first.1.start,GridSegment.realContains_start first.1,atStart⟩
    · exact ⟨first.1.finish,GridSegment.realContains_finish first.1,atFinish⟩
  have secondContains : second.1.RealContains (realCell a) := by
    rcases secondEndpoint with atStart | atFinish
    · have equal := injective (realCell_injective (pointEq.symm.trans atStart))
      rw [equal]
      exact GridSegment.realContains_start second.1
    · have equal := injective (realCell_injective (pointEq.symm.trans atFinish))
      rw [equal]
      exact GridSegment.realContains_finish second.1
  rcases simple.2.2 first firstMember second secondMember ordered (realCell a) firstContains secondContains with adjacent | closed
  · exact Or.inl ⟨adjacent.1,pointEq.trans (congrArg (fun cell => realCell (transform cell))
      (realCell_injective adjacent.2))⟩
  · exact Or.inr ⟨closed.1,closed.2.1,
      pointEq.trans (congrArg (fun cell => realCell (transform cell)) (realCell_injective closed.2.2.1)),
      pointEq.trans (congrArg (fun cell => realCell (transform cell)) (realCell_injective closed.2.2.2))⟩

end LeanTrominoes.GridPolyline
