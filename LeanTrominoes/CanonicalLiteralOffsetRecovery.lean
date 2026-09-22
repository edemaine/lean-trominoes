/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.UnitRouteEndpointDisplacement
import LeanTrominoes.PositionedPeriodicCNFOrthogonalIncidenceRoutes

/-! # Recovering anchored literal offsets from canonical route geometry -/
namespace LeanTrominoes.DelimitedDirectionDisplacement

/-- Canonical clause origin plus route displacement minus the variable position
is precisely the physical translation of the anchored literal offset. -/
theorem canonical_offset_scaled {Variable : Type*}
    (horizontal : Bool) (placement : PeriodicVariablePlacement Variable)
    (clause : PositionedPeriodicClause Variable) (literal : PeriodicLiteral Variable)
    (points : List Cell)
    (head : points.head? = some (PositionedPeriodicCNF.canonicalClausePosition placement clause))
    (last : points.getLast? = some (PositionedPeriodicCNF.canonicalLiteralPosition placement clause literal))
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    component horizontal (PositionedPeriodicCNF.canonicalClausePosition placement clause) +
        displacement horizontal (Gadget.unitSubdivisionDirections points) -
        component horizontal (placement.position literal.atom) =
      (placement.period : Int) * component horizontal
        (Cell.sub literal.offset (PeriodicCNF.clauseAnchor clause.literals)) := by
  rw [displacement_unitSubdivisionDirections horizontal points _ _ head last unitSteps]
  unfold PositionedPeriodicCNF.canonicalLiteralPosition PeriodicVariablePlacement.translation
  cases horizontal <;> simp [component, Cell.add, Cell.scale]

/-- Dividing by the positive drawing period recovers the exact semantic offset. -/
theorem canonical_offset_recovery {Variable : Type*}
    (horizontal : Bool) (placement : PeriodicVariablePlacement Variable)
    (positive : 0 < placement.period)
    (clause : PositionedPeriodicClause Variable) (literal : PeriodicLiteral Variable)
    (points : List Cell)
    (head : points.head? = some (PositionedPeriodicCNF.canonicalClausePosition placement clause))
    (last : points.getLast? = some (PositionedPeriodicCNF.canonicalLiteralPosition placement clause literal))
    (unitSteps : points.IsChain AxisDirection.IsUnitAxisStep) :
    (component horizontal (PositionedPeriodicCNF.canonicalClausePosition placement clause) +
        displacement horizontal (Gadget.unitSubdivisionDirections points) -
        component horizontal (placement.position literal.atom)) / (placement.period : Int) =
      component horizontal (Cell.sub literal.offset (PeriodicCNF.clauseAnchor clause.literals)) := by
  apply Int.ediv_eq_of_eq_mul_left (by omega)
  rw [canonical_offset_scaled horizontal placement clause literal points head last unitSteps]
  exact mul_comm _ _

end LeanTrominoes.DelimitedDirectionDisplacement
