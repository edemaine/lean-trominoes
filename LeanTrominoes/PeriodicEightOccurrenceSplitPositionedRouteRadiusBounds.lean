import LeanTrominoes.PeriodicEightOccurrenceSplitAngularBoundaryRoutes
import LeanTrominoes.OrthogonalPolylineCoordinateRadiusBounds

/-!
# Variable-centered radius bounds for positioned fixed-eight splitting

Each occurrence copy is displaced by at most six cells from the factor-36
refinement of its source literal center.  This small local displacement is
the bridge between source-route radius certificates and the final copied
variable representatives.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplitPositioned

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplit

/-- A copied literal's canonical position is within coordinate radius six
of the factor-36 refinement of its source literal's canonical position. -/
theorem occurrenceLiteralPosition_within_scaledSourceLiteral
    {Variable : Type*}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (occurrencePorts : OccurrencePorts)
    (clauseIndex literalIndex : Nat)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable) :
    WithinCoordinateRadius 6
      (Cell.scale refinementScale
        (PositionedPeriodicCNF.canonicalLiteralPosition
          sourcePlacement clause literal))
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (placement sourcePlacement)
        (occurrenceClause occurrencePorts clauseIndex clause)
        (PeriodicEightOccurrenceSplit.occurrenceLiteral
          occurrencePorts clauseIndex literalIndex literal)) := by
  cases portEq : occurrencePorts.port clauseIndex literalIndex <;>
    simp [PositionedPeriodicCNF.canonicalLiteralPosition,
      occurrenceClause,
      PeriodicEightOccurrenceSplit.occurrenceLiteral,
      occurrenceClause_clauseAnchor,
      occurrenceVariablePosition_copy,
      portEq, placement, refinementScale,
      macroOrigin, OccurrenceSplitRing.variablePosition,
      PeriodicVariablePlacement.translation,
      WithinCoordinateRadius, Cell.add, Cell.sub, Cell.scale] <;>
    ring_nf <;>
    norm_num

end PeriodicEightOccurrenceSplitPositioned
end LeanTrominoes
