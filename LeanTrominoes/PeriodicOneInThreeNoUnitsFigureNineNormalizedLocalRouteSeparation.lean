import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineNormalizedLocalRoutes
import LeanTrominoes.PositionedPeriodicCNFNormalizedRouteSeparation

/-!
# Relative separation of normalized composed local routes

The selected Figure 9-plus-unit-elimination routes are first described in
displayed physical coordinates and then shifted into each final clause's
canonical anchor gauge.  The generic two-anchor calculation specializes here
to move ordinary and strict physical separation into the stored local route
family used by the complete splice.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- A physical separation certificate at the anchor-adjusted relative offset
gives separation of the corresponding normalized local routes. -/
theorem normalizedLocalRoutes_relative_avoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (firstLiteralIndex secondLiteralIndex : Nat)
    (relativeTranslate : Cell)
    (physicalAvoid :
      RoutesAvoidEachOther
        (localRoutes source firstClauseIndex firstLiteralIndex)
        ((localRoutes source
            secondClauseIndex secondLiteralIndex).map
          (Cell.add
            (PositionedPeriodicCNF.relativePhysicalRouteOffset
              (composedPlacement source sourcePlacement)
              firstClause secondClause relativeTranslate)))) :
    RoutesAvoidEachOther
      (normalizedLocalRoutes source sourcePlacement
        firstClauseIndex firstLiteralIndex)
      ((normalizedLocalRoutes source sourcePlacement
          secondClauseIndex secondLiteralIndex).map
        (Cell.add
          ((composedPlacement source sourcePlacement).translation
            relativeTranslate))) := by
  rcases formulaClauseMetadata_lookup source firstClauseMember with
    ⟨firstMetadata, firstLookup, firstClauseEqual⟩
  rcases formulaClauseMetadata_lookup source secondClauseMember with
    ⟨secondMetadata, secondLookup, secondClauseEqual⟩
  subst firstClause
  subst secondClause
  simpa [normalizedLocalRoutes, firstLookup, secondLookup] using
    PositionedPeriodicCNF.normalizeIncidenceRoutes_relative_avoidEachOther
      (composedPlacement source sourcePlacement)
      firstMetadata.clause secondMetadata.clause
      (localRoutes source firstClauseIndex firstLiteralIndex)
      (localRoutes source secondClauseIndex secondLiteralIndex)
      relativeTranslate physicalAvoid

/-- The same anchor-adjusted transport preserves contact-free separation. -/
theorem normalizedLocalRoutes_relative_strictlyAvoidEachOther
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    {firstClause secondClause :
      PositionedPeriodicClause
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source)).clauses.zipIdx)
    (firstLiteralIndex secondLiteralIndex : Nat)
    (relativeTranslate : Cell)
    (physicalAvoid :
      RoutesStrictlyAvoidEachOther
        (localRoutes source firstClauseIndex firstLiteralIndex)
        ((localRoutes source
            secondClauseIndex secondLiteralIndex).map
          (Cell.add
            (PositionedPeriodicCNF.relativePhysicalRouteOffset
              (composedPlacement source sourcePlacement)
              firstClause secondClause relativeTranslate)))) :
    RoutesStrictlyAvoidEachOther
      (normalizedLocalRoutes source sourcePlacement
        firstClauseIndex firstLiteralIndex)
      ((normalizedLocalRoutes source sourcePlacement
          secondClauseIndex secondLiteralIndex).map
        (Cell.add
          ((composedPlacement source sourcePlacement).translation
            relativeTranslate))) := by
  rcases formulaClauseMetadata_lookup source firstClauseMember with
    ⟨firstMetadata, firstLookup, firstClauseEqual⟩
  rcases formulaClauseMetadata_lookup source secondClauseMember with
    ⟨secondMetadata, secondLookup, secondClauseEqual⟩
  subst firstClause
  subst secondClause
  simpa [normalizedLocalRoutes, firstLookup, secondLookup] using
    PositionedPeriodicCNF.normalizeIncidenceRoutes_relative_strictlyAvoidEachOther
      (composedPlacement source sourcePlacement)
      firstMetadata.clause secondMetadata.clause
      (localRoutes source firstClauseIndex firstLiteralIndex)
      (localRoutes source secondClauseIndex secondLiteralIndex)
      relativeTranslate physicalAvoid

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
