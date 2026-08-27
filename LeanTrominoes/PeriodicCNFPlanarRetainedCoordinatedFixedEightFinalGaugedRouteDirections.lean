/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightFinalGaugedRoutesComputability
import LeanTrominoes.PositionedPeriodicCNFVariableGaugeDirectionData

/-! # Directions through the final fixed-eight variable gauge -/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open Gadget

/-- The final fixed-eight gauge changes route coordinates but not directions. -/
theorem
    retainedOrderedFixedEightFinalGauged_directionWord_of_clause_mem
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    {clause : PositionedPeriodicClause
      (OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable))}
    {clauseIndex literalIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed
          source).clauses.zipIdx) :
    unitSubdivisionDirections
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
          source clauseIndex literalIndex) =
      unitSubdivisionDirections
        (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutesComputed
          source clauseIndex literalIndex) := by
  unfold
    retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGaugedIncidenceRoutesComputed
  exact
    PositionedPeriodicCNF.unitSubdivisionDirections_variableGaugeCanonicalIncidenceRoutes_of_clause_mem
      (retainedOrderedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFinalClockwiseFormulaComputed
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalGauge
        source)
      (retainedOrderedFixedEightPeriodicPlanarOneInThreeNoUnitsFinalClockwiseIncidenceRoutesComputed
        source)
      clauseMember

end PeriodicOrthocrossing
end LeanTrominoes
