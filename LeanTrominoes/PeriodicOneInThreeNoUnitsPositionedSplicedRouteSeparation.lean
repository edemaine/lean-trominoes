/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.OrthogonalPolylineTailEndpointContactSeparation
import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedAuxiliaryEndpoints

/-!
# Component separation for unit-elimination route splicing

The final unit-elimination route joins a normalized local clause route to a
completed canonical suffix.  This file packages the six pairwise component
conditions that make two such joins continuously separated and discharges all
splice-endpoint bookkeeping from the canonical endpoint certificates.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The component-level geometric obligations for a pair of final
unit-elimination routes.  Local routes may meet only at their clause-side
heads, suffixes may meet only at their variable-side tails, and the two cross
pairs are contact-free. -/
def SplicedRoutePairComponentsSeparated
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (inherited :
      PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
        (formula source)
        (placement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
    (firstClauseIndex firstLiteralIndex
      secondClauseIndex secondLiteralIndex : Nat) : Prop :=
  let suffixes :=
    completeRouteSuffixes source sourcePlacement inherited
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

/-- Component separation plus the standard local and suffix endpoint
certificates implies separation of the two complete spliced routes. -/
theorem splicedRoutes_avoidEachOther_of_components
    {Variable : Type*} [DecidableEq Variable]
    (source : PositionedPeriodicCNF Variable)
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceWidth : source.erase.WidthAtMost 3)
    (sourceDistinct : source.AllAtomsNodup)
    (inherited :
      PositionedPeriodicCNF.InheritedCanonicalIncidenceRouteSuffixes
        (formula source)
        (placement source sourcePlacement)
        (normalizedLocalEndpoint source sourcePlacement))
    {firstClause secondClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable)}
    {firstClauseIndex secondClauseIndex : Nat}
    (firstClauseMember :
      (firstClause, firstClauseIndex) ∈
        (formula source).clauses.zipIdx)
    (secondClauseMember :
      (secondClause, secondClauseIndex) ∈
        (formula source).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (OneInThreeNoUnitVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈
        firstClause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈
        secondClause.literals.zipIdx)
    (components :
      SplicedRoutePairComponentsSeparated
        source sourcePlacement inherited
        firstClauseIndex firstLiteralIndex
        secondClauseIndex secondLiteralIndex) :
    RoutesAvoidEachOther
      (splicedRoutes source sourcePlacement inherited
        firstClauseIndex firstLiteralIndex)
      (splicedRoutes source sourcePlacement inherited
        secondClauseIndex secondLiteralIndex) := by
  let suffixes :=
    completeRouteSuffixes source sourcePlacement inherited
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

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
