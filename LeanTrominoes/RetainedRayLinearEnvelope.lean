/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 6.1
-/
import LeanTrominoes.RetainedAngularFanDirectSourceTailSeparation

/-! Linear envelope bounds for a repeated ray's first and final primitive blocks. -/
namespace LeanTrominoes.PeriodicEightOccurrenceSplit

private theorem foldl_max_le (normal : Cell) (route : List Cell) (initial upper : Int)
    (initialBound : initial ≤ upper)
    (bounded : ∀ point ∈ route, Cell.linearValue normal point ≤ upper) :
    route.foldl (fun bound point => max bound (Cell.linearValue normal point)) initial ≤ upper := by
  induction route generalizing initial with
  | nil => exact initialBound
  | cons head tail ih =>
    exact ih _ (max_le initialBound (bounded _ (by simp)))
      (fun point member => bounded _ (by simp [member]))

private theorem foldl_min_ge (normal : Cell) (route : List Cell) (initial lower : Int)
    (initialBound : lower ≤ initial)
    (bounded : ∀ point ∈ route, lower ≤ Cell.linearValue normal point) :
    lower ≤ route.foldl (fun bound point => min bound (Cell.linearValue normal point)) initial := by
  induction route generalizing initial with
  | nil => exact initialBound
  | cons head tail ih =>
    exact ih _ (le_min initialBound (bounded _ (by simp)))
      (fun point member => bounded _ (by simp [member]))

private theorem maximum_le_of_bounded (normal : Cell) (route : List Cell) (upper : Int)
    (nonempty : route ≠ [])
    (bounded : ∀ point ∈ route, Cell.linearValue normal point ≤ upper) :
    routeLinearMaximum normal route ≤ upper := by
  cases route with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
    exact foldl_max_le normal (head :: tail) _ upper
      (bounded _ (by simp)) bounded

private theorem minimum_ge_of_bounded (normal : Cell) (route : List Cell) (lower : Int)
    (nonempty : route ≠ [])
    (bounded : ∀ point ∈ route, lower ≤ Cell.linearValue normal point) :
    lower ≤ routeLinearMinimum normal route := by
  cases route with
  | nil => exact False.elim (nonempty rfl)
  | cons head tail =>
    exact foldl_min_ge normal (head :: tail) _ lower
      (bounded _ (by simp)) bounded

theorem RetainedRay.rasterize_envelope_of_hull (ray : RetainedRay) (start normal : Cell) :
    routeLinearMaximum normal (ray.rasterize start) ≤ routeLinearMaximum normal (ray.linearHull start) ∧
    routeLinearMinimum normal (ray.linearHull start) ≤ routeLinearMinimum normal (ray.rasterize start) := by
  have nonempty : ray.rasterize start ≠ [] := by
    intro empty
    have head := ray.rasterize_head? start
    simp [empty] at head
  have bounded (p : Cell) (hp : p ∈ ray.rasterize start) :=
    ray.rasterize_linearBounds_of_hull start normal
      (routeLinearMinimum normal (ray.linearHull start))
      (routeLinearMaximum normal (ray.linearHull start))
      (fun q hq => ⟨routeLinearMinimum_le_linearValue normal _ hq,
        linearValue_le_routeLinearMaximum normal _ hq⟩) hp
  exact ⟨maximum_le_of_bounded _ _ _ nonempty (fun p hp => (bounded p hp).2),
    minimum_ge_of_bounded _ _ _ nonempty (fun p hp => (bounded p hp).1)⟩

end LeanTrominoes.PeriodicEightOccurrenceSplit
