/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineUnitSubdivision

/-! # Direction-stream descriptions of unit routes

A nonempty unit orthogonal route is represented losslessly by its first cell
and the direction of each subsequent step.  This representation lets the
sparse strip compiler stream local route triples while retaining only a
constant-size cursor.
-/

namespace LeanTrominoes
namespace Gadget

/-- The cardinal direction of every consecutive edge of a route. -/
def routeStepDirections : List Cell → List AxisDirection
  | first :: second :: rest =>
      AxisDirection.between first second ::
        routeStepDirections (second :: rest)
  | _ => []
termination_by points => points.length

/-- Reconstruct a nonempty route from its first cell and successive steps. -/
def rebuildRoute : Cell → List AxisDirection → List Cell
  | first, [] => [first]
  | first, direction :: directions =>
      first ::
        rebuildRoute
          (Cell.add first (AxisDirection.step direction)) directions

@[simp]
theorem routeStepDirections_length (first : Cell) (rest : List Cell) :
    (routeStepDirections (first :: rest)).length = rest.length := by
  induction rest generalizing first with
  | nil => simp [routeStepDirections]
  | cons second rest induction =>
      simp only [routeStepDirections, List.length_cons]
      rw [induction]

@[simp]
theorem rebuildRoute_length (first : Cell)
    (directions : List AxisDirection) :
    (rebuildRoute first directions).length = directions.length + 1 := by
  induction directions generalizing first with
  | nil => rfl
  | cons direction directions induction =>
      simp only [rebuildRoute, List.length_cons]
      rw [induction]

/-- A unit route is recovered exactly from its computed direction stream. -/
theorem rebuildRoute_routeStepDirections
    (first : Cell) (rest : List Cell)
    (unitSteps :
      (first :: rest).IsChain AxisDirection.IsUnitAxisStep) :
    rebuildRoute first (routeStepDirections (first :: rest)) =
      first :: rest := by
  induction rest generalizing first with
  | nil => simp [routeStepDirections, rebuildRoute]
  | cons second rest induction =>
      have firstUnit : AxisDirection.IsUnitAxisStep first second :=
        (List.isChain_cons_cons.mp unitSteps).1
      have remainingUnitSteps :
          (second :: rest).IsChain AxisDirection.IsUnitAxisStep :=
        (List.isChain_cons_cons.mp unitSteps).2
      simp only [routeStepDirections, rebuildRoute]
      rw [← AxisDirection.add_between_step_eq_of_unitAxisStep firstUnit]
      rw [induction second remainingUnitSteps]

/-- The coordinate offset of every consecutive route edge.  Unlike the
cardinal-direction representation above, this representation is lossless for
arbitrary route data and therefore needs no validity hypothesis. -/
def routeStepOffsets : List Cell → List Cell
  | first :: second :: rest =>
      Cell.sub second first :: routeStepOffsets (second :: rest)
  | _ => []
termination_by points => points.length

/-- Reconstruct a route from its first cell and successive coordinate
offsets. -/
def rebuildRouteFromOffsets : Cell → List Cell → List Cell
  | first, [] => [first]
  | first, offset :: offsets =>
      first :: rebuildRouteFromOffsets (Cell.add first offset) offsets

/-- Adding the exact offset from `first` to `second` reaches `second`. -/
@[simp]
theorem add_stepOffset (first second : Cell) :
    Cell.add first (Cell.sub second first) = second := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp [Cell.add, Cell.sub]

@[simp]
theorem routeStepOffsets_length (first : Cell) (rest : List Cell) :
    (routeStepOffsets (first :: rest)).length = rest.length := by
  induction rest generalizing first with
  | nil => simp [routeStepOffsets]
  | cons second rest induction =>
      simp only [routeStepOffsets, List.length_cons]
      rw [induction]

@[simp]
theorem rebuildRouteFromOffsets_length (first : Cell)
    (offsets : List Cell) :
    (rebuildRouteFromOffsets first offsets).length = offsets.length + 1 := by
  induction offsets generalizing first with
  | nil => rfl
  | cons offset offsets induction =>
      simp only [rebuildRouteFromOffsets, List.length_cons]
      rw [induction]

/-- Every nonempty route is recovered exactly from its coordinate offsets. -/
theorem rebuildRouteFromOffsets_routeStepOffsets
    (first : Cell) (rest : List Cell) :
    rebuildRouteFromOffsets first (routeStepOffsets (first :: rest)) =
      first :: rest := by
  induction rest generalizing first with
  | nil => simp [routeStepOffsets, rebuildRouteFromOffsets]
  | cons second rest induction =>
      simp only [routeStepOffsets, rebuildRouteFromOffsets]
      rw [add_stepOffset]
      rw [induction]

/-- Total first-cell projection used by proof-free route compilers. -/
def routeStart : List Cell → Cell
  | first :: _ => first
  | [] => (0, 0)

/-- The total start/offset representation also reconstructs the empty route
up to the irrelevant singleton fallback; both have no internal triples. -/
theorem rebuildRouteFromOffsets_routeStart
    (route : List Cell) :
    route = [] ∨
      rebuildRouteFromOffsets (routeStart route) (routeStepOffsets route) =
        route := by
  cases route with
  | nil => exact Or.inl rfl
  | cons first rest =>
      exact Or.inr (rebuildRouteFromOffsets_routeStepOffsets first rest)

end Gadget
end LeanTrominoes
