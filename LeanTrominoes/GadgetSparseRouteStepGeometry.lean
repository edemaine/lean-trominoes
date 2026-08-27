/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetSparseRouteStepData
import LeanTrominoes.PeriodicGridDrawingScaling

/-! # Affine geometry of exact route-step streams -/

namespace LeanTrominoes
namespace Gadget

/-- Translating both endpoints of an edge leaves its exact offset unchanged. -/
@[simp]
theorem stepOffset_add_left (offset first second : Cell) :
    Cell.sub (Cell.add offset second) (Cell.add offset first) =
      Cell.sub second first := by
  rcases offset with ⟨offsetX, offsetY⟩
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp [Cell.add, Cell.sub]

/-- Translation leaves the complete exact-offset stream unchanged. -/
@[simp]
theorem routeStepOffsets_translatePolyline
    (offset : Cell) (points : List Cell) :
    routeStepOffsets
        (PeriodicOrthocrossing.translatePolyline offset points) =
      routeStepOffsets points := by
  unfold PeriodicOrthocrossing.translatePolyline
  induction points using List.twoStepInduction with
  | nil | singleton => simp [routeStepOffsets]
  | cons_cons first second rest _ induction =>
      simp only [List.map_cons, routeStepOffsets, stepOffset_add_left]
      congr 1
      simpa only [List.map_cons] using induction second

/-- Translation also leaves every computed cardinal direction unchanged. -/
@[simp]
theorem routeStepDirections_translatePolyline
    (offset : Cell) (points : List Cell) :
    routeStepDirections
        (PeriodicOrthocrossing.translatePolyline offset points) =
      routeStepDirections points := by
  unfold PeriodicOrthocrossing.translatePolyline
  induction points using List.twoStepInduction with
  | nil | singleton => simp [routeStepDirections]
  | cons_cons first second rest _ induction =>
      simp only [List.map_cons, routeStepDirections,
        AxisDirection.between_add_left]
      congr 1
      simpa only [List.map_cons] using induction second

/-- Scaling both endpoints scales their exact offset by the same factor. -/
@[simp]
theorem stepOffset_scale (factor : Int) (first second : Cell) :
    Cell.sub (Cell.scale factor second) (Cell.scale factor first) =
      Cell.scale factor (Cell.sub second first) := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [Cell.scale, Cell.sub, Prod.mk.injEq]
  constructor <;> ring

/-- Scaling a route maps the same scale over its exact-offset stream. -/
@[simp]
theorem routeStepOffsets_scalePolyline
    (factor : Int) (points : List Cell) :
    routeStepOffsets (scalePolyline factor points) =
      (routeStepOffsets points).map (Cell.scale factor) := by
  induction points using List.twoStepInduction with
  | nil | singleton => simp [routeStepOffsets]
  | cons_cons first second rest _ induction =>
      simp only [scalePolyline_cons, routeStepOffsets, List.map_cons,
        stepOffset_scale]
      congr 1
      simpa only [scalePolyline_cons] using induction second

end Gadget
end LeanTrominoes
