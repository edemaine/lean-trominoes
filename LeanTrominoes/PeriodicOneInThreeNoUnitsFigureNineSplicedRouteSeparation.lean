import LeanTrominoes.OrthogonalPolylineTailEndpointContactSeparation
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineRouteFamily

/-!
# Component separation for composed Figure 9 route splicing

The direct two-stage construction joins one normalized local route from the
combined Figure 9 and unit-elimination drawing to a completed canonical
suffix.  This module isolates the six component conditions sufficient for
two complete joins to avoid each other and discharges all endpoint
bookkeeping from the canonical local and suffix certificates.
-/

namespace LeanTrominoes
namespace PlanarOneInThreeNoUnitsFigureNine

open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The component-level obligations for a pair of complete composed routes.
Local routes may meet only at their clause-side heads, suffixes may meet only
at their variable-side tails, and both cross pairs are contact-free. -/
def SplicedRoutePairComponentsSeparated
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (original :
      OriginalInheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source))
        (composedPlacement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
    (firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat) : Prop :=
  let suffixes :=
    completeRouteSuffixes
      source sourcePlacement sourceWidth sourceDistinct original
  let firstLocal :=
    normalizedLocalRoutes source sourcePlacement
      firstClauseIndex firstLiteralIndex
  let secondLocal :=
    normalizedLocalRoutes source sourcePlacement
      secondClauseIndex secondLiteralIndex
  let firstSuffix :=
    suffixes.routes firstClauseIndex firstLiteralIndex
  let secondSuffix :=
    suffixes.routes secondClauseIndex secondLiteralIndex
  RoutesAvoidEachOther firstLocal secondLocal ∧
    RoutesMeetOnlyAtHeads firstLocal secondLocal ∧
    RoutesStrictlyAvoidEachOther firstLocal secondSuffix ∧
    RoutesStrictlyAvoidEachOther firstSuffix secondLocal ∧
    RoutesAvoidEachOther firstSuffix secondSuffix ∧
    RoutesMeetOnlyAtTails firstSuffix secondSuffix

/-- Component separation and the standard local and suffix endpoint
certificates imply separation of the complete composed routes. -/
theorem splicedRoutes_avoidEachOther_of_components
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (original :
      OriginalInheritedCanonicalIncidenceRouteSuffixes
        (PeriodicOneInThreeNoUnitsPositioned.formula
          (PeriodicOneInThreePositioned.formula source))
        (composedPlacement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
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
    {firstLiteral secondLiteral :
      PeriodicLiteral
        (OneInThreeNoUnitVariable (OneInThreeVariable Variable))}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (components :
      SplicedRoutePairComponentsSeparated
        source sourcePlacement sourceWidth sourceDistinct original
        firstClauseIndex firstLiteralIndex
        secondClauseIndex secondLiteralIndex) :
    RoutesAvoidEachOther
      (splicedRoutes
        source sourcePlacement sourceWidth sourceDistinct original
        firstClauseIndex firstLiteralIndex)
      (splicedRoutes
        source sourcePlacement sourceWidth sourceDistinct original
        secondClauseIndex secondLiteralIndex) := by
  let suffixes :=
    completeRouteSuffixes
      source sourcePlacement sourceWidth sourceDistinct original
  let firstLocal :=
    normalizedLocalRoutes source sourcePlacement
      firstClauseIndex firstLiteralIndex
  let secondLocal :=
    normalizedLocalRoutes source sourcePlacement
      secondClauseIndex secondLiteralIndex
  let firstSuffix :=
    suffixes.routes firstClauseIndex firstLiteralIndex
  let secondSuffix :=
    suffixes.routes secondClauseIndex secondLiteralIndex
  rcases components with
    ⟨prefixesAvoid, prefixContactsAtHeads,
      firstPrefixAvoidSecondSuffix,
      firstSuffixAvoidSecondPrefix,
      suffixesAvoid, suffixContactsAtTails⟩
  have firstLocalEndpoints :=
    normalizedLocalRoutes_endpoints_of_members
      source sourcePlacement sourceWidth sourceDistinct
      firstClauseMember firstLiteralMember
  have secondLocalEndpoints :=
    normalizedLocalRoutes_endpoints_of_members
      source sourcePlacement sourceWidth sourceDistinct
      secondClauseMember secondLiteralMember
  have firstSuffixEndpoints :=
    suffixes.endpoints
      firstClause firstClauseIndex firstClauseMember
      firstLiteral firstLiteralIndex firstLiteralMember
  have secondSuffixEndpoints :=
    suffixes.endpoints
      secondClause secondClauseIndex secondClauseMember
      secondLiteral secondLiteralIndex secondLiteralMember
  have joined :=
    prefixesAvoid.join_tails_of_prefix_heads_and_suffix_tails
      prefixContactsAtHeads
      firstPrefixAvoidSecondSuffix
      firstSuffixAvoidSecondPrefix
      suffixesAvoid suffixContactsAtTails
      firstLocalEndpoints.2 firstSuffixEndpoints.1
      secondLocalEndpoints.2 secondSuffixEndpoints.1
  simpa [splicedRoutes,
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes,
    suffixes, firstLocal, secondLocal,
    firstSuffix, secondSuffix] using joined

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
