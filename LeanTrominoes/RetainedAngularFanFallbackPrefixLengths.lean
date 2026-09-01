/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceChoiceFailure

/-!
# Prefix lengths for fallback final routes

Failure of the checked direct-source selector leaves a straight carrier lens
or a route-bend corner.  This file records the small finite fact about those
two component drawings needed by same-clause fan separation:

* in one carrier clause, at most one of its two incidence routes has a
  singleton deleted-final-point prefix; and
* no bend-corner incidence route has such a singleton prefix.

Translation, gauging, anchor normalization, and representative
deduplication preserve route length, so the finite facts lift to physical
witnesses for two final incidences.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PlanarThreeSAT

set_option maxHeartbeats 800000

/-- Within one canonical horizontal equality-lens clause, two different
literal indices cannot both select a route with a singleton deleted-final
prefix. -/
private theorem horizontalEqualityLensRoutes_not_both_singletonPrefixes
    (span : Int) (clauseIndex firstLiteralIndex secondLiteralIndex : Nat)
    (indicesDifferent : firstLiteralIndex ≠ secondLiteralIndex) :
    ¬(((horizontalEqualityLensRoutes
          span clauseIndex firstLiteralIndex).dropLast.length = 1) ∧
      ((horizontalEqualityLensRoutes
          span clauseIndex secondLiteralIndex).dropLast.length = 1)) := by
  rcases clauseIndex with (_ | _ | clauseIndex) <;>
    rcases firstLiteralIndex with
      (_ | _ | firstLiteralIndex) <;>
    rcases secondLiteralIndex with
      (_ | _ | secondLiteralIndex) <;>
    simp [horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute] at *

/-- Axis placement and variable renaming preserve the carrier lens's finite
prefix-length dichotomy. -/
private theorem
    drawingPlanarSATCarrierLensIncidenceDrawing_not_both_singletonPrefixes
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (clauseIndex firstLiteralIndex secondLiteralIndex : Nat)
    (indicesDifferent : firstLiteralIndex ≠ secondLiteralIndex) :
    ¬(((drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).routes
            clauseIndex firstLiteralIndex).dropLast.length = 1 ∧
      ((drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).routes
            clauseIndex secondLiteralIndex).dropLast.length = 1) := by
  intro both
  apply
    horizontalEqualityLensRoutes_not_both_singletonPrefixes
      (AxisDirection.axisSpan
        (CarrierNode.position formula.incidenceGraph link.first)
        (CarrierNode.position formula.incidenceGraph link.second))
      clauseIndex firstLiteralIndex secondLiteralIndex
      indicesDifferent
  simpa [drawingPlanarSATCarrierLensIncidenceDrawing,
    EqualityLink.lensDrawing, placedEqualityLensDrawing,
    axisEqualityLensDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.placeOnAxis,
    EmbeddedCNFIncidenceDrawing.orient,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedCNFIncidenceDrawing.mapPoints,
    horizontalEqualityLensDrawing] using both

/-- Every entry of every genuine corner route table has at least two points
before its final point; out-of-range and equal-port entries are empty. -/
private theorem cornerEqualityRoutes_prefix_length_ne_one
    (firstPort secondPort : CornerPort)
    (clauseIndex literalIndex : Nat) :
    (cornerEqualityRoutes
      firstPort secondPort clauseIndex literalIndex).dropLast.length ≠ 1 := by
  unfold cornerEqualityRoutes
  by_cases bound :
      2 * clauseIndex + literalIndex <
        (cornerEqualityRouteTable
          firstPort secondPort).length
  · cases firstPort <;> cases secondPort
    all_goals
      simp only [cornerEqualityRouteTable,
        List.length_cons, List.length_nil,
        Nat.reduceAdd, Nat.not_lt_zero] at bound
    all_goals
      have clauseBound : clauseIndex < 2 := by omega
      have literalBound : literalIndex < 4 := by omega
      interval_cases clauseIndex <;>
        interval_cases literalIndex <;>
        simp [cornerEqualityRouteTable]
  · rw [List.getD_eq_default
      (cornerEqualityRouteTable firstPort secondPort) []
      (Nat.le_of_not_gt bound)]
    simp

/-- Placement and renaming preserve the bend corner's lower bound on its
deleted-final-point prefix length. -/
private theorem
    drawingPlanarSATBendCornerIncidenceDrawing_prefix_length_ne_one
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (clauseIndex literalIndex : Nat) :
    ((drawingPlanarSATBendCornerIncidenceDrawing
        formula routeBend).routes
          clauseIndex literalIndex).dropLast.length ≠ 1 := by
  intro singleton
  apply cornerEqualityRoutes_prefix_length_ne_one
    routeBend.incomingPort routeBend.outgoingPort
    clauseIndex literalIndex
  simpa [drawingPlanarSATBendCornerIncidenceDrawing,
    RouteBend.cornerDrawing, placedCornerEqualityDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedCNFIncidenceDrawing.mapPoints,
    cornerEqualityDrawing] using singleton

/-- Public finite corollary: no local bend-corner incidence route has a
singleton deleted-final-point prefix. -/
theorem bendCornerIncidenceRoute_prefix_length_ne_one
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (routeBend : RouteBend)
    (clauseIndex literalIndex : Nat) :
    ((drawingPlanarSATBendCornerIncidenceDrawing formula routeBend).routes
      clauseIndex literalIndex).dropLast.length ≠ 1 :=
  drawingPlanarSATBendCornerIncidenceDrawing_prefix_length_ne_one
    formula routeBend clauseIndex literalIndex

/-- A physical final witness has the same deleted-prefix length as its
metadata-selected finite local route. -/
theorem
    finalGaugedRouteOccurrence_dropLast_length_eq_localRoute
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0)) :
    (finalGaugedRouteOccurrence
        formula clauseIndex literalIndex (0, 0)).dropLast.length =
      ((witness.metadata.source.incidenceDrawing formula).routes
        witness.metadata.source.localClauseIndex
        literalIndex).dropLast.length := by
  rw [witness.routeEq]
  unfold metadataPhysicalRouteOccurrence translatePolyline
  rw [← List.map_dropLast, List.length_map]
  simp [retainedDrawingPlanarSATLocalIncidenceDrawing_routes,
    retainedDrawingPlanarSATLocalIncidenceRoutes,
    metadataPhysicalIncidence,
    EmbeddedCNFIncidenceDrawing.routeAt,
    witness.metadataLookup]

/-- A final occurrence represented by a bend route cannot have a singleton
deleted-final-point prefix. -/
theorem
    finalGaugedRouteOccurrence_prefix_length_ne_one_of_bend_witness
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex literalIndex : Nat}
    (witness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex literalIndex (0, 0))
    (routeBend : RouteBend)
    (localClauseIndex : Nat)
    (sourceEq :
      witness.metadata.source =
        .bend routeBend localClauseIndex) :
    (finalGaugedRouteOccurrence
      formula clauseIndex literalIndex (0, 0)).dropLast.length ≠ 1 := by
  intro singleton
  apply
    drawingPlanarSATBendCornerIncidenceDrawing_prefix_length_ne_one
      formula routeBend localClauseIndex literalIndex
  have localSingleton :=
    (finalGaugedRouteOccurrence_dropLast_length_eq_localRoute
      formula witness).symm.trans singleton
  simpa [sourceEq,
    DrawingPlanarSATClauseSource.incidenceDrawing,
    DrawingPlanarSATClauseSource.localClauseIndex] using
      localSingleton

/-- Two different literal occurrences represented by the same carrier or
bend metadata cannot both have singleton final-point-deleted prefixes. -/
theorem
    not_both_singletonPrefixes_of_sameMetadata_carrier_or_bend_witnesses
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    {clauseIndex firstLiteralIndex secondLiteralIndex : Nat}
    (firstWitness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex firstLiteralIndex (0, 0))
    (secondWitness :
      FinalGaugedRouteOccurrenceWitness
        formula clauseIndex secondLiteralIndex (0, 0))
    (metadataEq :
      firstWitness.metadata = secondWitness.metadata)
    (indicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex)
    (sourceCases :
      (∃ link localClauseIndex,
          firstWitness.metadata.source =
            .carrier link localClauseIndex) ∨
        (∃ routeBend localClauseIndex,
          firstWitness.metadata.source =
            .bend routeBend localClauseIndex)) :
    ¬((finalGaugedRouteOccurrence
          formula clauseIndex firstLiteralIndex
          (0, 0)).dropLast.length = 1 ∧
      (finalGaugedRouteOccurrence
          formula clauseIndex secondLiteralIndex
          (0, 0)).dropLast.length = 1) := by
  intro both
  have firstLocal :=
    finalGaugedRouteOccurrence_dropLast_length_eq_localRoute
      formula firstWitness
  have secondLocal :=
    finalGaugedRouteOccurrence_dropLast_length_eq_localRoute
      formula secondWitness
  have sameSource :
      firstWitness.metadata.source =
        secondWitness.metadata.source :=
    congrArg DrawingPlanarSATClauseMetadata.source metadataEq
  rcases sourceCases with
    ⟨link, localClauseIndex, firstSourceEq⟩ |
      ⟨routeBend, localClauseIndex, firstSourceEq⟩
  · have secondSourceEq :
        secondWitness.metadata.source =
          .carrier link localClauseIndex :=
      sameSource.symm.trans firstSourceEq
    apply
      drawingPlanarSATCarrierLensIncidenceDrawing_not_both_singletonPrefixes
        formula link localClauseIndex
        firstLiteralIndex secondLiteralIndex indicesDifferent
    constructor
    · have localSingleton := firstLocal.symm.trans both.1
      simpa [firstSourceEq,
        DrawingPlanarSATClauseSource.incidenceDrawing,
        DrawingPlanarSATClauseSource.localClauseIndex] using localSingleton
    · have localSingleton := secondLocal.symm.trans both.2
      simpa [secondSourceEq,
        DrawingPlanarSATClauseSource.incidenceDrawing,
        DrawingPlanarSATClauseSource.localClauseIndex] using localSingleton
  · have secondSourceEq :
        secondWitness.metadata.source =
          .bend routeBend localClauseIndex :=
      sameSource.symm.trans firstSourceEq
    exact
      drawingPlanarSATBendCornerIncidenceDrawing_prefix_length_ne_one
        formula routeBend localClauseIndex firstLiteralIndex
        (by
          have localSingleton := firstLocal.symm.trans both.1
          simpa [firstSourceEq,
            DrawingPlanarSATClauseSource.incidenceDrawing,
            DrawingPlanarSATClauseSource.localClauseIndex] using
              localSingleton)

/-- At two different genuine literals of one final clause, failure of the
checked direct selector itself implies that the two final route prefixes are
not both singletons. -/
theorem
    not_both_singletonPrefixes_of_sameClause_finalDirectSourceChoice_none
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    {clause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈
        (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
          formula).clauses.zipIdx)
    {firstLiteral secondLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {firstLiteralIndex secondLiteralIndex : Nat}
    (firstLiteralMember :
      (firstLiteral, firstLiteralIndex) ∈ clause.literals.zipIdx)
    (secondLiteralMember :
      (secondLiteral, secondLiteralIndex) ∈ clause.literals.zipIdx)
    (indicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex)
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex = none) :
    ¬((finalGaugedRouteOccurrence
          formula clauseIndex firstLiteralIndex
          (0, 0)).dropLast.length = 1 ∧
      (finalGaugedRouteOccurrence
          formula clauseIndex secondLiteralIndex
          (0, 0)).dropLast.length = 1) := by
  rcases
      exists_sameMetadata_carrier_or_bend_witnesses_of_sameClause_choice_none
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember
        firstLiteralMember secondLiteralMember
        firstChoiceNone with
    ⟨firstWitness, secondWitness, metadataEq, sourceCases⟩
  exact
    not_both_singletonPrefixes_of_sameMetadata_carrier_or_bend_witnesses
      formula firstWitness secondWitness metadataEq
      indicesDifferent sourceCases

end PeriodicEightOccurrenceSplit
end LeanTrominoes
