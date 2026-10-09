/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingBendSubdivision

/-! # Exact coordinate lookup for inserted bend vertices -/
namespace LeanTrominoes.PeriodicGridDrawing.BendSubdivision
open PeriodicGraph.BendSubdivision

theorem internalPoint_lookup {drawing : PeriodicGridDrawing} {index : Nat} {entry : Cell × Nat}
    (member : entry∈internalPoints drawing index) :
    1≤entry.2 ∧ entry.2+1<(drawing.edgeRoute index).length ∧
      (drawing.edgeRoute index).getD entry.2 (0,0)=entry.1 := by
  obtain ⟨i,valid,equal⟩ := List.exists_mem_zipIdx.mp ⟨entry,member,rfl⟩
  subst entry
  have routeValid : 1+i<(drawing.edgeRoute index).length := by
    simp only [List.length_dropLast,List.length_tail] at valid
    omega
  refine ⟨by omega,?_,?_⟩
  · simp only [List.length_dropLast,List.length_tail] at valid
    omega
  · rw [List.getD_eq_getElem _ _ routeValid]
    simp only [List.getElem_dropLast,List.getElem_tail,Nat.add_comm]

theorem position_middle {V : Type*} [DecidableEq V] (source : PeriodicGraph V)
    (drawing : PeriodicGridDrawing) (factor : Nat) (tagged : PeriodicEdge V × Nat)
    {entry : Cell × Nat} (member : entry∈internalPoints drawing tagged.2) :
    position source drawing factor (.bend tagged.2 entry.2)=
      InteriorBends.representative drawing.gridSize factor entry.1 := by
  simp only [position,(internalPoint_lookup member).2.2]

theorem route_eq_endpoints_and_internal {route : List Cell} {first last : Cell}
    (length : 2≤route.length) (head : route.head?=some first) (tail : route.getLast?=some last) :
    route=first::route.tail.dropLast++[last] := by
  cases route with
  | nil => simp at length
  | cons actual rest =>
      have same : actual=first := Option.some.inj head
      subst actual
      have nonempty : rest≠[] := by intro equal; simp [equal] at length
      have lastLookup : rest.getLast?=some last := by simpa only [List.getLast?_cons_of_ne_nil nonempty] using tail
      rw [List.tail_cons]
      have reconstructed := List.dropLast_append_getLast? (l := rest) last (by simp only [lastLookup,Option.mem_some_iff])
      simp only [List.cons_append,reconstructed]

end LeanTrominoes.PeriodicGridDrawing.BendSubdivision
