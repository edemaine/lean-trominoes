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

/-- A route whose computed direction is constant on every edge has a constant
direction word of the expected length. -/
theorem routeStepDirections_eq_replicate_of_constant
    (first : Cell) (rest : List Cell) (direction : AxisDirection)
    (constant :
      (first :: rest).IsChain fun source target =>
        AxisDirection.between source target = direction) :
    routeStepDirections (first :: rest) =
      List.replicate rest.length direction := by
  induction rest generalizing first with
  | nil => simp [routeStepDirections]
  | cons second rest induction =>
      have firstDirection :
          AxisDirection.between first second = direction :=
        (List.isChain_cons_cons.mp constant).1
      have remainingConstant :
          (second :: rest).IsChain fun source target =>
            AxisDirection.between source target = direction :=
        (List.isChain_cons_cons.mp constant).2
      simp only [routeStepDirections, List.length_cons]
      rw [firstDirection, induction second remainingConstant,
        List.replicate_succ]

/-- Unit subdivision of one axis-aligned segment is a repeated finite
cardinal-direction block. -/
theorem routeStepDirections_unitSegmentPoints
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    routeStepDirections (AxisDirection.unitSegmentPoints first second) =
      List.replicate (AxisDirection.segmentLength first second)
        (AxisDirection.between first second) := by
  cases pointsEq : AxisDirection.unitSegmentPoints first second with
  | nil =>
      have head := AxisDirection.unitSegmentPoints_head? first second
      simp [pointsEq] at head
  | cons actualFirst rest =>
      have actualFirstEq : actualFirst = first := by
        have head := AxisDirection.unitSegmentPoints_head? first second
        rw [pointsEq] at head
        exact Option.some.inj head
      subst actualFirst
      have constant :
          (first :: rest).IsChain fun source target =>
            AxisDirection.between source target =
              AxisDirection.between first second := by
        simpa [pointsEq] using
          AxisDirection.unitSegmentPoints_direction aligned
      have length :
          rest.length = AxisDirection.segmentLength first second := by
        have total := AxisDirection.unitSegmentPoints_length first second
        rw [pointsEq] at total
        simp only [List.length_cons] at total
        omega
      rw [routeStepDirections_eq_replicate_of_constant
        first rest (AxisDirection.between first second) constant]
      rw [length]

/-- On a unit step, its exact coordinate offset is its computed cardinal
step vector. -/
theorem stepOffset_eq_between_step_of_unitAxisStep
    {source target : Cell}
    (unit : AxisDirection.IsUnitAxisStep source target) :
    Cell.sub target source =
      (AxisDirection.between source target).step := by
  rcases unit with ⟨direction, genuine, rfl⟩
  rw [AxisDirection.between_add_step source genuine]
  rcases source with ⟨sourceX, sourceY⟩
  cases direction <;>
    simp_all [AxisDirection.IsGenuine, AxisDirection.step,
      Cell.add, Cell.sub]

/-- Exact offsets and finite cardinal directions coincide along every unit
route. -/
theorem routeStepOffsets_eq_map_routeStepDirections
    (first : Cell) (rest : List Cell)
    (unitSteps :
      (first :: rest).IsChain AxisDirection.IsUnitAxisStep) :
    routeStepOffsets (first :: rest) =
      (routeStepDirections (first :: rest)).map AxisDirection.step := by
  induction rest generalizing first with
  | nil => simp [routeStepOffsets, routeStepDirections]
  | cons second rest induction =>
      have firstUnit : AxisDirection.IsUnitAxisStep first second :=
        (List.isChain_cons_cons.mp unitSteps).1
      have remainingUnitSteps :
          (second :: rest).IsChain AxisDirection.IsUnitAxisStep :=
        (List.isChain_cons_cons.mp unitSteps).2
      simp only [routeStepOffsets, routeStepDirections, List.map_cons,
        List.cons.injEq]
      exact ⟨stepOffset_eq_between_step_of_unitAxisStep firstUnit,
        induction second remainingUnitSteps⟩

/-- Thus one subdivided axis-aligned segment has a repeated exact unit-offset
word. -/
theorem routeStepOffsets_unitSegmentPoints
    {first second : Cell}
    (aligned : (GridSegment.mk first second).IsAxisAligned) :
    routeStepOffsets (AxisDirection.unitSegmentPoints first second) =
      List.replicate (AxisDirection.segmentLength first second)
        (AxisDirection.between first second).step := by
  cases pointsEq : AxisDirection.unitSegmentPoints first second with
  | nil =>
      have head := AxisDirection.unitSegmentPoints_head? first second
      simp [pointsEq] at head
  | cons actualFirst rest =>
      have unitSteps :
          (actualFirst :: rest).IsChain AxisDirection.IsUnitAxisStep := by
        simpa [pointsEq] using
          AxisDirection.unitSegmentPoints_unitSteps aligned
      rw [routeStepOffsets_eq_map_routeStepDirections
        actualFirst rest unitSteps]
      rw [← pointsEq, routeStepDirections_unitSegmentPoints aligned]
      simp

end Gadget
end LeanTrominoes
