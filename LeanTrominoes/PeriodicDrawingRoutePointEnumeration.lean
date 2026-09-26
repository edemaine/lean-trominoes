/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.PeriodicGridDrawingEndpointContacts
import Mathlib.Data.List.Enum

/-! # Bounded index quantifiers for all stored route-point occurrences -/
namespace LeanTrominoes.PeriodicGridDrawing

def routePointAt (d : PeriodicGridDrawing) (i : Nat) (hi : i<d.edgeRoutes.length)
    (j : Nat) (hj : j<d.edgeRoutes[i].length) : IndexedRoutePoint :=
  ⟨i,j,d.edgeRoutes[i].length,d.edgeRoutes[i][j]⟩

theorem mem_indexedRoutePoints_iff (d : PeriodicGridDrawing) (point : IndexedRoutePoint) :
    point ∈ d.indexedRoutePoints ↔ ∃ i, ∃ hi : i<d.edgeRoutes.length,
      ∃ j, ∃ hj : j<d.edgeRoutes[i].length, point=d.routePointAt i hi j hj := by
  simp only [indexedRoutePoints,List.mem_flatMap,List.mem_map,List.exists_mem_zipIdx',routePointAt]
  constructor
  · rintro ⟨i,hi,j,hj,h⟩
    exact ⟨i,hi,j,hj,h.symm⟩
  · rintro ⟨i,hi,j,hj,h⟩
    exact ⟨i,hi,j,hj,h.symm⟩

theorem forall_indexedRoutePoints_iff (d : PeriodicGridDrawing) (P : IndexedRoutePoint → Prop) :
    (∀ point ∈ d.indexedRoutePoints, P point) ↔
      ∀ i (hi : i<d.edgeRoutes.length), ∀ j (hj : j<d.edgeRoutes[i].length), P (d.routePointAt i hi j hj) := by
  constructor
  · intro h i hi j hj
    exact h _ ((mem_indexedRoutePoints_iff d _).mpr ⟨i,hi,j,hj,rfl⟩)
  · intro h point hp
    obtain ⟨i,hi,j,hj,rfl⟩ := (mem_indexedRoutePoints_iff d point).mp hp
    exact h i hi j hj

end LeanTrominoes.PeriodicGridDrawing
