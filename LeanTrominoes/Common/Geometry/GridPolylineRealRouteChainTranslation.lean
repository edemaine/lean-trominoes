/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Common.Geometry.GridPolylineRealRouteChain

/-! # Provenance of translated finite route chains -/
namespace LeanTrominoes.GridPolyline

theorem routeChain_map {routes : List (List Cell)}
    (chain : routes.IsChain (fun first second => first.getLast?=second.head?)) (transform : Cell → Cell) :
    (routes.map (List.map transform)).IsChain (fun first second => first.getLast?=second.head?) := by
  rw [List.isChain_map]
  apply chain.imp
  intro first second equal
  simp only [List.getLast?_map,List.head?_map,equal]

theorem joinRouteChain_map_contains {routes : List (List Cell)}
    (chain : routes.IsChain (fun first second => first.getLast?=second.head?))
    (long : ∀ route∈routes, 2≤route.length) (transform : Cell → Cell) {p : ℝ × ℝ}
    (contains : RealContains ((joinRouteChain routes).map transform) p) :
    ∃ route∈routes, RealContains (route.map transform) p := by
  rw [← joinRouteChain_map] at contains
  have mappedLong : ∀ route∈routes.map (List.map transform),2≤route.length := by
    intro route member
    obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
    simpa only [List.length_map] using long old oldMember
  obtain ⟨route,member,routeContains⟩ := joinRouteChain_contains (routeChain_map chain transform) mappedLong contains
  obtain ⟨old,oldMember,rfl⟩ := List.mem_map.mp member
  exact ⟨old,oldMember,routeContains⟩

end LeanTrominoes.GridPolyline
