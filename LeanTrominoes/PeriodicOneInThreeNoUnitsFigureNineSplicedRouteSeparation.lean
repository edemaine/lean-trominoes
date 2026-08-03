import LeanTrominoes.OrthogonalPolylineTailEndpointContactSeparation
import LeanTrominoes.PeriodicOneInThreeNoUnitsFigureNineRouteFamily
import LeanTrominoes.PositionedPeriodicCNFRelativeRouteSeparation

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

local instance composedVariableDecidableEq
    {Variable : Type*} [DecidableEq Variable] :
    DecidableEq
      (OneInThreeNoUnitVariable (OneInThreeVariable Variable)) :=
  nestedVariableDecidableEq

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

/-- Component obligations for one stored route and one relatively translated
stored route.  The translation is applied separately to the second local and
suffix pieces before they are rejoined. -/
def RelativeSplicedRoutePairComponentsSeparated
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
      secondClauseIndex secondLiteralIndex : Nat)
    (relativeTranslate : Cell) : Prop :=
  let suffixes :=
    completeRouteSuffixes
      source sourcePlacement sourceWidth sourceDistinct original
  let offset :=
    (composedPlacement source sourcePlacement).translation
      relativeTranslate
  let firstLocal :=
    normalizedLocalRoutes source sourcePlacement
      firstClauseIndex firstLiteralIndex
  let secondLocal :=
    (normalizedLocalRoutes source sourcePlacement
      secondClauseIndex secondLiteralIndex).map (Cell.add offset)
  let firstSuffix :=
    suffixes.routes firstClauseIndex firstLiteralIndex
  let secondSuffix :=
    (suffixes.routes
      secondClauseIndex secondLiteralIndex).map (Cell.add offset)
  RoutesAvoidEachOther firstLocal secondLocal ∧
    RoutesMeetOnlyAtHeads firstLocal secondLocal ∧
    RoutesStrictlyAvoidEachOther firstLocal secondSuffix ∧
    RoutesStrictlyAvoidEachOther firstSuffix secondLocal ∧
    RoutesAvoidEachOther firstSuffix secondSuffix ∧
    RoutesMeetOnlyAtTails firstSuffix secondSuffix

/-- Relative component separation implies separation of the first complete
route from the translated second complete route. -/
theorem splicedRoutes_relative_avoidEachOther_of_components
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
    (relativeTranslate : Cell)
    (components :
      RelativeSplicedRoutePairComponentsSeparated
        source sourcePlacement sourceWidth sourceDistinct original
        firstClauseIndex firstLiteralIndex
        secondClauseIndex secondLiteralIndex relativeTranslate) :
    RoutesAvoidEachOther
      (splicedRoutes
        source sourcePlacement sourceWidth sourceDistinct original
        firstClauseIndex firstLiteralIndex)
      ((splicedRoutes
          source sourcePlacement sourceWidth sourceDistinct original
          secondClauseIndex secondLiteralIndex).map
        (Cell.add
          ((composedPlacement source sourcePlacement).translation
            relativeTranslate))) := by
  let suffixes :=
    completeRouteSuffixes
      source sourcePlacement sourceWidth sourceDistinct original
  let offset :=
    (composedPlacement source sourcePlacement).translation
      relativeTranslate
  let firstLocal :=
    normalizedLocalRoutes source sourcePlacement
      firstClauseIndex firstLiteralIndex
  let secondLocalBase :=
    normalizedLocalRoutes source sourcePlacement
      secondClauseIndex secondLiteralIndex
  let secondLocal := secondLocalBase.map (Cell.add offset)
  let firstSuffix :=
    suffixes.routes firstClauseIndex firstLiteralIndex
  let secondSuffixBase :=
    suffixes.routes secondClauseIndex secondLiteralIndex
  let secondSuffix := secondSuffixBase.map (Cell.add offset)
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
  have secondLocalLast :
      secondLocal.getLast? =
        some
          (Cell.add offset
            (normalizedLocalEndpoint source sourcePlacement
              secondClauseIndex secondLiteralIndex)) := by
    simpa [secondLocal, secondLocalBase] using
      congrArg (Option.map (Cell.add offset)) secondLocalEndpoints.2
  have secondSuffixHead :
      secondSuffix.head? =
        some
          (Cell.add offset
            (normalizedLocalEndpoint source sourcePlacement
              secondClauseIndex secondLiteralIndex)) := by
    simpa [secondSuffix, secondSuffixBase] using
      congrArg (Option.map (Cell.add offset)) secondSuffixEndpoints.1
  have joined :=
    prefixesAvoid.join_tails_of_prefix_heads_and_suffix_tails
      prefixContactsAtHeads
      firstPrefixAvoidSecondSuffix
      firstSuffixAvoidSecondPrefix
      suffixesAvoid suffixContactsAtTails
      firstLocalEndpoints.2 firstSuffixEndpoints.1
      secondLocalLast secondSuffixHead
  simpa [splicedRoutes,
    PositionedPeriodicCNF.spliceLocalIncidenceRoutes,
    suffixes, offset, firstLocal, secondLocalBase, secondLocal,
    firstSuffix, secondSuffixBase, secondSuffix,
    joinAtEndpoint, List.map_append] using joined

/-- Pointwise relative component certificates assemble into the complete
incidence-indexed separation predicate consumed by loop erasure and ribbon
readiness. -/
theorem splicedRoutes_relativeIncidenceRoutesAvoidEachOther_of_components
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
    (components :
      ∀ first ∈
          (PeriodicCNF.incidencesWithMetadata
            (PeriodicOneInThreeNoUnitsPositioned.formula
              (PeriodicOneInThreePositioned.formula source)).erase).zipIdx,
        ∀ second ∈
            (PeriodicCNF.incidencesWithMetadata
              (PeriodicOneInThreeNoUnitsPositioned.formula
                (PeriodicOneInThreePositioned.formula source)).erase).zipIdx,
          ∀ relativeTranslate,
            (first.2, (0, 0)) ≠
                (second.2, relativeTranslate) →
              RelativeSplicedRoutePairComponentsSeparated
                source sourcePlacement sourceWidth sourceDistinct original
                first.1.clauseIndex first.1.literalIndex
                second.1.clauseIndex second.1.literalIndex
                relativeTranslate) :
    PositionedPeriodicCNF.RelativeIncidenceRoutesAvoidEachOther
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source))
      (composedPlacement source sourcePlacement)
      (splicedRoutes
        source sourcePlacement sourceWidth sourceDistinct original) := by
  intro first firstMember second secondMember
    relativeTranslate occurrencesDifferent
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source))
      firstMember with
    ⟨firstClause, firstLiteral,
      firstClauseMember, firstLiteralMember, _⟩
  rcases PositionedPeriodicCNF.incidenceMetadata_of_tagged
      (PeriodicOneInThreeNoUnitsPositioned.formula
        (PeriodicOneInThreePositioned.formula source))
      secondMember with
    ⟨secondClause, secondLiteral,
      secondClauseMember, secondLiteralMember, _⟩
  exact
    splicedRoutes_relative_avoidEachOther_of_components
      source sourcePlacement sourceWidth sourceDistinct original
      firstClauseMember secondClauseMember
      firstLiteralMember secondLiteralMember relativeTranslate
      (components first firstMember second secondMember
        relativeTranslate occurrencesDifferent)

end PlanarOneInThreeNoUnitsFigureNine
end LeanTrominoes
