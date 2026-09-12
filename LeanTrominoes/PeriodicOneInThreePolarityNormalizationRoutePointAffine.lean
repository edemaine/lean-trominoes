/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.UnitRouteInitialCoordinates
import LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteDirectionData

/-! # Affine positions of polarity subdivision vertices -/

namespace LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
open Gadget PeriodicOrthocrossing

/-- Threefold refinement reserves two collinear unit steps at the beginning
of a source route. Its first direction and clause origin determine both new
vertex coordinates exactly. -/
theorem refinedRoute_initial_positions
    (routes : PositionedPeriodicCNF.IncidenceRoutes) (clauseIndex literalIndex : Nat)
    (origin : Cell) (direction : AxisDirection)
    (head : (routes clauseIndex literalIndex).head? = some origin)
    (orthogonal : OrthogonalPolyline (routes clauseIndex literalIndex))
    (firstDirection : (unitSubdivisionDirections (routes clauseIndex literalIndex)).head? = some direction) :
    (refinedRoute routes clauseIndex literalIndex).getD 1 (0, 0) =
        Cell.add (Cell.scale 3 origin) direction.step ∧
      (refinedRoute routes clauseIndex literalIndex).getD 2 (0, 0) =
        Cell.add (Cell.scale 3 origin) (Cell.scale 2 direction.step) := by
  have scaledHead : (scalePolyline refinementFactor (routes clauseIndex literalIndex)).head? =
      some (Cell.scale 3 origin) := by
    rw [scalePolyline_head?, head]
    rfl
  have scaledNonempty : scalePolyline refinementFactor (routes clauseIndex literalIndex) ≠ [] := by
    intro empty
    rw [empty] at scaledHead
    cases scaledHead
  have refinedHead : (refinedRoute routes clauseIndex literalIndex).head? = some (Cell.scale 3 origin) := by
    rw [refinedRoute, AxisDirection.unitSubdividePolyline_head? scaledNonempty]
    exact scaledHead
  have repeatedHead :
      (repeatDirections refinementFactor (unitSubdivisionDirections (routes clauseIndex literalIndex)))[0]? = some direction ∧
      (repeatDirections refinementFactor (unitSubdivisionDirections (routes clauseIndex literalIndex)))[1]? = some direction := by
    cases wordEq : unitSubdivisionDirections (routes clauseIndex literalIndex) with
    | nil => simp [wordEq] at firstDirection
    | cons first rest =>
        have firstEq : first = direction := by simpa only [wordEq, List.head?_cons, Option.some.injEq] using firstDirection
        simp [firstEq, repeatDirections, refinementFactor, List.replicate_succ]
  apply initial_two_unit_positions _ _ _ refinedHead (refinedRoute_unitSteps routes clauseIndex literalIndex orthogonal)
  · rw [refinedRoute_directionWord routes clauseIndex literalIndex orthogonal]
    exact repeatedHead.1
  · rw [refinedRoute_directionWord routes clauseIndex literalIndex orthogonal]
    exact repeatedHead.2

/-- The actual fresh-variable and complement-clause selectors use precisely
those two affine points at their retained source-incidence indices. -/
theorem routePoint_one_two_eq_affine
    {Variable : Type*} (routes : PositionedPeriodicCNF.IncidenceRoutes)
    (fresh : FreshOccurrence Variable) (origin : Cell) (direction : AxisDirection)
    (head : (routes fresh.1.1 fresh.1.2).head? = some origin)
    (orthogonal : OrthogonalPolyline (routes fresh.1.1 fresh.1.2))
    (firstDirection : (unitSubdivisionDirections (routes fresh.1.1 fresh.1.2)).head? = some direction) :
    routePoint routes fresh 1 = Cell.add (Cell.scale 3 origin) direction.step ∧
      routePoint routes fresh 2 = Cell.add (Cell.scale 3 origin) (Cell.scale 2 direction.step) :=
  refinedRoute_initial_positions routes fresh.1.1 fresh.1.2 origin direction head orthogonal firstDirection

end LeanTrominoes.PeriodicOneInThreePolarityNormalizationRouteSubdivision
