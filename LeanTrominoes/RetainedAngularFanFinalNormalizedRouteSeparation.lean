import LeanTrominoes.OrthogonalPolylineLoopErasureSeparation
import LeanTrominoes.RetainedAngularFanFinalNormalizedRouteFamily
import LeanTrominoes.RetainedAngularFanFinalPublicRouteSeparation

/-!
# Pairwise separation of the normalized final route family

The public coordinated route family is already continuously separated at
zero periodic shift.  The generic loop-erasure transport theorem turns that
certificate into the same complete separation statement for the normalized,
geometrically simple routes.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Every pair of distinct genuine incidences in the normalized final route
family avoids each other. -/
theorem
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {firstClause secondClause :
      PositionedPeriodicClause
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitPositionedFormula
          formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (ThreeOccurrenceVariable
          (WrappedPeriodicPlanarSATVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (incidencesDistinct :
      firstClauseIndex ≠ secondClauseIndex ∨
        firstLiteralIndex ≠ secondLiteralIndex) :
    RoutesAvoidEachOther
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        formula firstClauseIndex firstLiteralIndex)
      (retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes
        formula secondClauseIndex secondLiteralIndex) := by
  let firstRoute :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      formula firstClauseIndex firstLiteralIndex
  let secondRoute :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
      formula secondClauseIndex secondLiteralIndex
  have firstValid :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty firstClauseMember firstLiteralMember
  have secondValid :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_valid
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty secondClauseMember secondLiteralMember
  have firstNonempty : firstRoute ≠ [] := by
    intro routeEmpty
    have := firstValid.1
    simp [firstRoute, routeEmpty] at this
  have secondNonempty : secondRoute ≠ [] := by
    intro routeEmpty
    have := secondValid.1
    simp [secondRoute, routeEmpty] at this
  have originalAvoids :=
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_avoidEachOther
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember incidencesDistinct
  have normalizedAvoids :=
    originalAvoids.normalizeOrthogonalPolyline
      firstNonempty secondNonempty
      firstValid.2.2 secondValid.2.2
  simpa only [
    retainedDrawingSourceScaledNormalizedEightOccurrenceSplitIncidenceRoutes,
    firstRoute, secondRoute] using normalizedAvoids

end PeriodicOrthocrossing
end LeanTrominoes
