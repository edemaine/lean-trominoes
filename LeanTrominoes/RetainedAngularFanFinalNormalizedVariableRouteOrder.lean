import LeanTrominoes.PeriodicGridDrawingLoopErasureRouteOrders
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteLength
import LeanTrominoes.RetainedAngularFanFinalNormalizedRouteFamily
import LeanTrominoes.RetainedAngularFanFinalRouteEndpointIsolation

/-!
# Variable route order after final fixed-eight normalization

The final coordinated routes already follow occurrence order.  Their
nondegeneracy, orthogonality, and variable-endpoint isolation ensure that
verified unit subdivision and loop erasure preserve every terminal direction,
so the normalized simple route family has the same clockwise order.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

/-- Pointwise normalization preserves the clockwise occurrence order of the
final coordinated fixed-eight route family. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_variableRoutesInOccurrenceOrder
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.VariableRoutesInOccurrenceOrder
      (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
        source)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        source) := by
  apply
    (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_variableRoutesInOccurrenceOrder
      source sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty).normalizeOrthogonalIncidenceRoutes_of_lastNotInDropLast
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_length_ge_two
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2.2
  · intro clause clauseIndex clauseMember
      literal literalIndex literalMember
    exact
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_lastNotInDropLast
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember

end PeriodicOrthocrossing
end LeanTrominoes
