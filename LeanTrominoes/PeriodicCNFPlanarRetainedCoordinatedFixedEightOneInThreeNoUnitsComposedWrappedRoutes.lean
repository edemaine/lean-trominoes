import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsComposedRoutes
import LeanTrominoes.PeriodicCNFPlanarRetainedCoordinatedFixedEightOneInThreeNoUnitsRoutes
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedRenaming
import LeanTrominoes.PositionedPeriodicCNFCanonicalRouteRenaming

/-!
# Composed routes through the public exact-one wrapper

The certified composed Figure 9 and unit-elimination drawings use the raw
two-stage variable type.  The public reduction wraps the intermediate
Figure 9 variables before unit elimination.  Unit elimination is natural
under that coordinate-preserving wrapping, so the composed routes can be
reused without changing a single point.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

set_option maxHeartbeats 2000000

/-- The variable map induced by wrapping every intermediate Figure 9
variable.  Auxiliary keys retain their source clause, renamed pointwise. -/
def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawToWrappedVariable
    {Variable : Type*} :
    OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable) →
      OneInThreeNoUnitVariable
        (WrappedPeriodicVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
  PeriodicOneInThreeNoUnits.renameVariable WrappedPeriodicVariable.mk

/-- The public unit-free formula is exactly the coordinate-preserving
rename of the raw composed formula. -/
theorem
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_rename
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
        source).rename
        retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawToWrappedVariable =
      retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source := by
  simpa [
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawToWrappedVariable] using
    PeriodicOneInThreeNoUnitsPositioned.formula_rename
      WrappedPeriodicVariable.mk
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
        source)

/-- The public and raw composed placements have the same physical period. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedPlacement_period
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source).period =
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).period := by
  simpa [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement,
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement] using
    PeriodicOneInThreeNoUnitsPositioned.placement_period_rename
      WrappedPeriodicVariable.mk
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
      rfl

/-- Every raw composed variable and its public wrapped image have the same
physical position. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedPlacement_position
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (atom :
      OneInThreeNoUnitVariable
        (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source).position
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawToWrappedVariable
          atom) =
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
        source).position atom := by
  simpa [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeFormula,
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement,
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawToWrappedVariable,
    PlanarOneInThreeNoUnitsFigureNine.composedPlacement] using
    PeriodicOneInThreeNoUnitsPositioned.placement_position_rename
      WrappedPeriodicVariable.mk
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeRawFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeRawPlacement source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreePlacement source)
      (fun _ => rfl)
      rfl atom

/-- The certified composed routes, reused verbatim for the public wrapped
unit-free formula. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedIncidenceRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.IncidenceRoutes :=
  retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
    source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty

/-- Every genuine public composed route has canonical endpoints and is an
orthogonal polyline. -/
theorem
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedIncidenceRoutes_valid
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)))}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx) :
    (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
              source)
            clause) ∧
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedIncidenceRoutes
        source sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseIndex literalIndex).getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
              source)
            clause literal) ∧
      OrthogonalPolyline
        (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedIncidenceRoutes
          source sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseIndex literalIndex) := by
  let rawFormula :=
    retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula
      source
  let rawPlacement :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawPlacement
      source
  let wrappedPlacement :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement source
  let routes :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
  let variableMap :
      OneInThreeNoUnitVariable
          (PeriodicPlanarOneInThreeThreeRawVariable Variable) →
        OneInThreeNoUnitVariable
          (WrappedPeriodicVariable
            (PeriodicPlanarOneInThreeThreeRawVariable Variable)) :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawToWrappedVariable
  have renamedFormula :
      rawFormula.rename variableMap =
        retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
          source := by
    simpa [rawFormula, variableMap] using
      retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsComposedRawFormula_rename
        source
  have renamedClauseMember :
      (clause, clauseIndex) ∈
        (rawFormula.rename variableMap).clauses.zipIdx := by
    rw [renamedFormula]
    exact clauseMember
  have rawEndpoints :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ rawFormula.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          (routes sourceClauseIndex sourceLiteralIndex).head? =
              some
                (PositionedPeriodicCNF.canonicalClausePosition
                  rawPlacement sourceClause) ∧
            (routes sourceClauseIndex sourceLiteralIndex).getLast? =
              some
                (PositionedPeriodicCNF.canonicalLiteralPosition
                  rawPlacement sourceClause sourceLiteral) := by
    intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
    have valid :=
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
        sourceClauseMember sourceLiteralMember
    exact ⟨valid.1, valid.2.1⟩
  have rawOrthogonal :
      ∀ sourceClause sourceClauseIndex,
        (sourceClause, sourceClauseIndex) ∈ rawFormula.clauses.zipIdx →
        ∀ sourceLiteral sourceLiteralIndex,
          (sourceLiteral, sourceLiteralIndex) ∈
              sourceClause.literals.zipIdx →
          OrthogonalPolyline
            (routes sourceClauseIndex sourceLiteralIndex) := by
    intro sourceClause sourceClauseIndex sourceClauseMember
      sourceLiteral sourceLiteralIndex sourceLiteralMember
    exact
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedRawIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
        sourceClauseMember sourceLiteralMember).2.2
  have endpoints :=
    PositionedPeriodicCNF.canonicalIncidenceRoutes_endpoints_rename
      rawFormula rawPlacement wrappedPlacement routes variableMap rawEndpoints
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedPlacement_position
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedPlacement_period
        source)
      renamedClauseMember literalMember
  have orthogonal :=
    PositionedPeriodicCNF.canonicalIncidenceRoutes_orthogonal_rename
      rawFormula routes variableMap rawOrthogonal
      renamedClauseMember literalMember
  simpa [
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedIncidenceRoutes,
    rawFormula, rawPlacement, wrappedPlacement, routes, variableMap] using
      ⟨endpoints.1, endpoints.2, orthogonal⟩

/-- The public composed route family packaged with its endpoint and
orthogonality certificates. -/
noncomputable def
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedCanonicalRoutes
    {Variable : Type*} [DecidableEq Variable]
    (source : PeriodicCNF Variable)
    (sourceLocal : source.IsLocal)
    (sourceWidth : source.WidthAtMost 3)
    (sourceOccurrences : source.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ source.clauses, clause ≠ []) :
    PositionedPeriodicCNF.CanonicalOrthogonalIncidenceRoutes
      (retainedCoordinatedFixedEightPositionedPeriodicPlanarOneInThreeNoUnitsFormula
        source)
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsPlacement
        source) where
  routes :=
    retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedIncidenceRoutes
      source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
  endpoints := by
    intro clause clauseIndex clauseMember literal literalIndex literalMember
    have valid :=
      retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
        clauseMember literalMember
    exact ⟨valid.1, valid.2.1⟩
  orthogonal := by
    intro clause clauseIndex clauseMember literal literalIndex literalMember
    exact
      (retainedCoordinatedFixedEightPeriodicPlanarOneInThreeNoUnitsComposedIncidenceRoutes_valid
        source sourceLocal sourceWidth sourceOccurrences sourceClausesNonempty
        clauseMember literalMember).2.2

end PeriodicOrthocrossing
end LeanTrominoes
