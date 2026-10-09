/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GridPolylineRealOpenSimple

/-! # Endpoint lookup through arbitrary point maps -/
namespace LeanTrominoes.GridPolyline

theorem RealIsEndpoint.map_at_cell {route : List Cell} {cell : Cell}
    (endpoint : RealIsEndpoint route (realCell cell)) (transform : Cell → Cell) :
    RealIsEndpoint (route.map transform) (realCell (transform cell)) := by
  rcases endpoint with ⟨actual,head,equal⟩ | ⟨actual,last,equal⟩
  · have same := realCell_injective equal
    subst actual
    exact Or.inl ⟨transform cell,by rw [List.head?_map,head]; rfl,rfl⟩
  · have same := realCell_injective equal
    subst actual
    exact Or.inr ⟨transform cell,by rw [List.getLast?_map,last]; rfl,rfl⟩

theorem realIsEndpoint_map_at_cell_iff {route : List Cell} {cell : Cell}
    (transform : Cell → Cell) (injective : Function.Injective transform) :
    RealIsEndpoint (route.map transform) (realCell (transform cell)) ↔ RealIsEndpoint route (realCell cell) := by
  constructor
  · intro endpoint
    rcases endpoint with ⟨actual,head,equal⟩ | ⟨actual,last,equal⟩
    · rw [List.head?_map] at head
      obtain ⟨old,oldHead,rfl⟩ := Option.map_eq_some_iff.mp head
      have same := injective (realCell_injective equal)
      subst old
      exact Or.inl ⟨cell,oldHead,rfl⟩
    · rw [List.getLast?_map] at last
      obtain ⟨old,oldLast,rfl⟩ := Option.map_eq_some_iff.mp last
      have same := injective (realCell_injective equal)
      subst old
      exact Or.inr ⟨cell,oldLast,rfl⟩
  · exact fun endpoint => endpoint.map_at_cell transform

end LeanTrominoes.GridPolyline
