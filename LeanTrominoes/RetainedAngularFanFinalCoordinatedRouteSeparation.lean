/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFinalDirectSourceSpokeIdentification
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutePairs
import LeanTrominoes.RetainedAngularFanFinalFallbackOccurrenceSeparation
import LeanTrominoes.RetainedAngularFanFinalOccurrenceSuffixSeparation

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Two successful coordinated direct occurrences of one final clause have
fully separated routes, with their common clause gate as the only possible
contact. -/
theorem retainedFinalCoordinatedDirectOccurrenceRoutes_separated
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choiceFirst choiceSecond : RetainedDirectSourceRouteChoice)
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
    (choiceFirstLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex =
        some choiceFirst)
    (choiceSecondLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex secondLiteralIndex =
        some choiceSecond)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    RoutesAvoidEachOther
        (retainedFinalCoordinatedDirectOccurrenceRoute
          formula choiceFirst
          (clause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral clauseIndex firstLiteralIndex)
        (retainedFinalCoordinatedDirectOccurrenceRoute
          formula choiceSecond
          (clause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral clauseIndex secondLiteralIndex) ∧
      RoutesMeetOnlyAtHeads
        (retainedFinalCoordinatedDirectOccurrenceRoute
          formula choiceFirst
          (clause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral clauseIndex firstLiteralIndex)
        (retainedFinalCoordinatedDirectOccurrenceRoute
          formula choiceSecond
          (clause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral clauseIndex secondLiteralIndex) := by
  let source :=
    (retainedDeduplicatedGaugedWrappedDrawingPositionedPeriodicPlanarSATFormula
      formula).scale retainedAngularFanSourceClearanceFactor
  let placement :=
    (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
      formula).scale retainedAngularFanSourceClearanceFactor
  let routes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes
      retainedAngularFanSourceClearanceFactor
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
        formula)
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral clauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral clauseIndex secondLiteralIndex
  let firstSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        (clause.scale retainedAngularFanSourceClearanceFactor)
        firstLiteral clauseIndex firstLiteralIndex)
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement
        (angularOccurrenceOrder source.erase routes)
        (clause.scale retainedAngularFanSourceClearanceFactor)
        secondLiteral clauseIndex secondLiteralIndex)
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have crossSeparated :=
    retainedFinalDirectSourceRouteChoices_crossFigure7Spokes_strictlyAvoid
      formula sourceCertificate.graphDegreeAtMostThree
      clauseIndex firstLiteralIndex secondLiteralIndex
      choiceFirst choiceSecond
      choiceFirstLookup choiceSecondLookup
      literalIndicesDifferent firstSlot secondSlot
  have firstSpokeEq :
      choiceFirst.figure7Spoke firstSlot = firstSuffix := by
    simpa [source, placement, routes, firstSlot, firstSuffix] using
      retainedFinalDirectSourceRouteChoice_figure7Spoke_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choiceFirst
        clauseMember firstLiteralMember choiceFirstLookup
  have secondSpokeEq :
      choiceSecond.figure7Spoke secondSlot = secondSuffix := by
    simpa [source, placement, routes, secondSlot, secondSuffix] using
      retainedFinalDirectSourceRouteChoice_figure7Spoke_eq_occurrenceSuffix
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choiceSecond
        clauseMember secondLiteralMember choiceSecondLookup
  have firstPrefixAvoidSecondSuffix :
      RoutesStrictlyAvoidEachOther
        (choiceFirst.completeRoute firstSlot) secondSuffix := by
    rw [← secondSpokeEq]
    exact crossSeparated.1
  have firstSuffixAvoidSecondPrefix :
      RoutesStrictlyAvoidEachOther
        firstSuffix (choiceSecond.completeRoute secondSlot) := by
    rw [← firstSpokeEq]
    exact crossSeparated.2
  have suffixesAvoid :
      RoutesStrictlyAvoidEachOther firstSuffix secondSuffix := by
    simpa [source, placement, routes, firstSuffix, secondSuffix] using
      retainedFinalCoordinatedOccurrenceSuffixes_strictlyAvoid
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember
        firstLiteralMember secondLiteralMember
        literalIndicesDifferent
  exact
    retainedFinalCoordinatedDirectOccurrenceRoutes_separated_of_suffix_pieces
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choiceFirst choiceSecond
      clauseMember firstLiteralMember secondLiteralMember
      choiceFirstLookup choiceSecondLookup literalIndicesDifferent
      (by
        simpa [source, placement, routes, firstSlot, secondSuffix] using
          firstPrefixAvoidSecondSuffix)
      (by
        simpa [source, placement, routes, secondSlot, firstSuffix] using
          firstSuffixAvoidSecondPrefix)
      (by
        simpa [source, placement, routes, firstSuffix, secondSuffix] using
          suffixesAvoid)

/-- The same-clause separation theorem in the public total route-family
interface: two successful final selectors reduce to their explicit
coordinated occurrence routes. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_separated_of_choices_some
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choiceFirst choiceSecond : RetainedDirectSourceRouteChoice)
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
    (choiceFirstLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex =
        some choiceFirst)
    (choiceSecondLookup :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex secondLiteralIndex =
        some choiceSecond)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    RoutesAvoidEachOther
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex firstLiteralIndex)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex secondLiteralIndex) ∧
      RoutesMeetOnlyAtHeads
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex firstLiteralIndex)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex secondLiteralIndex) := by
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor, clauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have scaledClauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp scaledClauseMember
  have firstLiteralLookup :
      (clause.scale retainedAngularFanSourceClearanceFactor).literals[
          firstLiteralIndex]? =
        some firstLiteral := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp firstLiteralMember
  have secondLiteralLookup :
      (clause.scale retainedAngularFanSourceClearanceFactor).literals[
          secondLiteralIndex]? =
        some secondLiteral := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp secondLiteralMember
  rw [
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
      formula clauseIndex firstLiteralIndex choiceFirst
      (clause.scale retainedAngularFanSourceClearanceFactor)
      firstLiteral choiceFirstLookup
      scaledClauseLookup firstLiteralLookup,
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_some
      formula clauseIndex secondLiteralIndex choiceSecond
      (clause.scale retainedAngularFanSourceClearanceFactor)
      secondLiteral choiceSecondLookup
      scaledClauseLookup secondLiteralLookup]
  exact
    retainedFinalCoordinatedDirectOccurrenceRoutes_separated
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choiceFirst choiceSecond
      clauseMember firstLiteralMember secondLiteralMember
      choiceFirstLookup choiceSecondLookup literalIndicesDifferent

/-- A compact reusable package saying that two routes avoid each other and
that their only possible contact is their common head.  The geometric model
routes are stored separately from the public routes, so constructing the
certificate never unfolds the route predicates during lookup normalization. -/
structure RoutesSeparatedAtHeads
    (first second : List Cell) where
  firstModel : List Cell
  secondModel : List Cell
  firstEq : first = firstModel
  secondEq : second = secondModel
  modelsAvoid : RoutesAvoidEachOther firstModel secondModel
  modelsMeetOnlyAtHeads :
    RoutesMeetOnlyAtHeads firstModel secondModel

namespace RoutesSeparatedAtHeads

/-- Package direct avoidance and common-head-only contact proofs using the
public routes themselves as geometric models. -/
def ofProofs
    {first second : List Cell}
    (avoid : RoutesAvoidEachOther first second)
    (meetOnlyAtHeads : RoutesMeetOnlyAtHeads first second) :
    RoutesSeparatedAtHeads first second :=
  ⟨first, second, rfl, rfl, avoid, meetOnlyAtHeads⟩

/-- A separated-at-heads certificate is symmetric in its two routes. -/
def symm
    {first second : List Cell}
    (certificate : RoutesSeparatedAtHeads first second) :
    RoutesSeparatedAtHeads second first :=
  ⟨certificate.secondModel, certificate.firstModel,
    certificate.secondEq, certificate.firstEq,
    routesAvoidEachOther_comm certificate.modelsAvoid,
    certificate.modelsMeetOnlyAtHeads.symm⟩

/-- Recover avoidance of the public routes from the stored geometric
models. -/
theorem avoid
    {first second : List Cell}
    (certificate : RoutesSeparatedAtHeads first second) :
    RoutesAvoidEachOther first second := by
  rcases certificate with
    ⟨firstModel, secondModel, firstEq, secondEq,
      modelsAvoid, _modelsMeet⟩
  cases firstEq
  cases secondEq
  exact modelsAvoid

/-- Recover common-head-only contact of the public routes from the stored
geometric models. -/
theorem meetOnlyAtHeads
    {first second : List Cell}
    (certificate : RoutesSeparatedAtHeads first second) :
    RoutesMeetOnlyAtHeads first second := by
  rcases certificate with
    ⟨firstModel, secondModel, firstEq, secondEq,
      _modelsAvoid, modelsMeet⟩
  cases firstEq
  cases secondEq
  exact modelsMeet

end RoutesSeparatedAtHeads

private theorem
    coordinatedFallbackSecond_choice_none_and_prefix_length_ne_one
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
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex = none)
    (firstPrefixLength :
      (finalCoordinatedSourceRoutes
        formula clauseIndex firstLiteralIndex).dropLast.length = 1)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    retainedFinalDirectSourceRouteChoice?
          formula clauseIndex secondLiteralIndex = none ∧
      (finalCoordinatedSourceRoutes
        formula clauseIndex secondLiteralIndex).dropLast.length ≠ 1 := by
  have secondChoiceNone :=
    retainedFinalDirectSourceRouteChoice_eq_none_of_sameClause_choice_none
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember
      firstLiteralMember secondLiteralMember firstChoiceNone
  have notBothSingleton :=
    not_both_singletonPrefixes_of_sameClause_finalDirectSourceChoice_none
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember
      firstLiteralMember secondLiteralMember literalIndicesDifferent
      firstChoiceNone
  refine ⟨secondChoiceNone, ?_⟩
  intro secondPrefixLength
  exact notBothSingleton
    ⟨by
        rw [←
          finalCoordinatedSourceRoutes_eq_finalGaugedRouteOccurrence_zero
            formula clauseIndex firstLiteralIndex]
        exact firstPrefixLength,
      by
        rw [←
          finalCoordinatedSourceRoutes_eq_finalGaugedRouteOccurrence_zero
            formula clauseIndex secondLiteralIndex]
        exact secondPrefixLength⟩

private theorem
    coordinatedFallbackRouteModels_of_choice_none_of_prefix_length_one
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
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex = none)
    (firstPrefixLength :
      (finalCoordinatedSourceRoutes
        formula clauseIndex firstLiteralIndex).dropLast.length = 1)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex firstLiteralIndex =
      retainedFinalEscapedFallbackOccurrenceRoute
        formula
        (clause.scale retainedAngularFanSourceClearanceFactor)
        firstLiteral clauseIndex firstLiteralIndex ∧
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex secondLiteralIndex =
      joinAtEndpoint
        (retainedAngularFanSplicedBoundaryRoute
          (scalePolyline retainedAngularFanSourceClearanceFactor
            (finalCoordinatedSourceRoutes
              formula clauseIndex secondLiteralIndex))
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            (classifiedRetainedTerminalData
              (routeTerminalVector
                (finalCoordinatedSourceRoutes
                  formula clauseIndex secondLiteralIndex))))
          (retainedFinalCoordinatedOccurrenceSlot
            formula secondLiteral clauseIndex secondLiteralIndex))
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix
            ((finalCoordinatedPlacement formula).scale
              retainedAngularFanSourceClearanceFactor)
            (angularOccurrenceOrder
              ((finalCoordinatedSource formula).scale
                retainedAngularFanSourceClearanceFactor).erase
              (PositionedPeriodicCNF.scaleIncidenceRoutes
                retainedAngularFanSourceClearanceFactor
                (finalCoordinatedSourceRoutes formula)))
            (clause.scale retainedAngularFanSourceClearanceFactor)
            secondLiteral clauseIndex secondLiteralIndex)) := by
  have finalClauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx := by
    simpa [finalCoordinatedSource] using clauseMember
  have secondProperties :=
    coordinatedFallbackSecond_choice_none_and_prefix_length_ne_one
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceNone firstPrefixLength literalIndicesDifferent
  have scaledClauseMember :
      (clause.scale retainedAngularFanSourceClearanceFactor, clauseIndex) ∈
        ((finalCoordinatedSource formula).scale
          retainedAngularFanSourceClearanceFactor).clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses, List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), finalClauseMember, rfl⟩
  have scaledClauseLookup :=
    (List.mem_zipIdx_iff_getElem?).mp scaledClauseMember
  have firstLiteralLookup :
      (clause.scale retainedAngularFanSourceClearanceFactor).literals[
          firstLiteralIndex]? =
        some firstLiteral := by
    simpa using
      (List.mem_zipIdx_iff_getElem?).mp firstLiteralMember
  constructor
  · exact
      retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_one
        formula clauseIndex firstLiteralIndex
        (clause.scale retainedAngularFanSourceClearanceFactor)
        firstLiteral firstChoiceNone firstPrefixLength
        scaledClauseLookup firstLiteralLookup
  · exact
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
          formula clauseIndex secondLiteralIndex
          secondProperties.1 secondProperties.2).trans
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty finalClauseMember secondLiteralMember)

/-- The public total route family also separates the exceptional failed
selector branch: a singleton first prefix uses the escaped route, while
selector uniformity and the prefix-length dichotomy leave the second route
as the established ordinary splice. -/
def
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_separated_of_choice_none_of_prefix_length_one
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
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex = none)
    (firstPrefixLength :
      (finalCoordinatedSourceRoutes
        formula clauseIndex firstLiteralIndex).dropLast.length = 1)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    RoutesSeparatedAtHeads
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex firstLiteralIndex)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex secondLiteralIndex) := by
  have finalClauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx := by
    simpa [finalCoordinatedSource] using clauseMember
  have modelEqualities :=
    coordinatedFallbackRouteModels_of_choice_none_of_prefix_length_one
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceNone firstPrefixLength literalIndicesDifferent
  have separated :=
    retainedFinalSameClauseEscapedFallbackExplicitOccurrenceRoutes_separated
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty finalClauseMember
      firstLiteralMember secondLiteralMember literalIndicesDifferent
      firstChoiceNone firstPrefixLength
  exact
    ⟨_, _, modelEqualities.1, modelEqualities.2,
      separated.1, separated.2⟩

/-- The symmetric exceptional branch: when the second failed-choice prefix
is a singleton, reverse the literal order, use the escaped-first certificate,
and then restore the public route order. -/
def
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_separated_of_choice_none_of_second_prefix_length_one
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
    (secondChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex secondLiteralIndex = none)
    (secondPrefixLength :
      (finalCoordinatedSourceRoutes
        formula clauseIndex secondLiteralIndex).dropLast.length = 1)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    RoutesSeparatedAtHeads
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex firstLiteralIndex)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex secondLiteralIndex) :=
  (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_separated_of_choice_none_of_prefix_length_one
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember
      secondLiteralMember firstLiteralMember
      secondChoiceNone secondPrefixLength
      (Ne.symm literalIndicesDifferent)).symm

private theorem
    coordinatedFallbackRouteModels_of_choice_none_of_prefix_lengths_ne_one
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
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex = none)
    (firstPrefixLengthNeOne :
      (finalCoordinatedSourceRoutes
        formula clauseIndex firstLiteralIndex).dropLast.length ≠ 1)
    (secondPrefixLengthNeOne :
      (finalCoordinatedSourceRoutes
        formula clauseIndex secondLiteralIndex).dropLast.length ≠ 1) :
    let source :=
      (finalCoordinatedSource formula).scale
        retainedAngularFanSourceClearanceFactor
    let placement :=
      (finalCoordinatedPlacement formula).scale
        retainedAngularFanSourceClearanceFactor
    let routes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes
        retainedAngularFanSourceClearanceFactor
        (finalCoordinatedSourceRoutes formula)
    let order :=
      angularOccurrenceOrder source.erase routes
    let scaledClause :=
      clause.scale retainedAngularFanSourceClearanceFactor
    let firstRawRoute :=
      finalCoordinatedSourceRoutes
        formula clauseIndex firstLiteralIndex
    let secondRawRoute :=
      finalCoordinatedSourceRoutes
        formula clauseIndex secondLiteralIndex
    let firstExplicit :=
      joinAtEndpoint
        (retainedAngularFanSplicedBoundaryRoute
          (scalePolyline retainedAngularFanSourceClearanceFactor
            firstRawRoute)
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            (classifiedRetainedTerminalData
              (routeTerminalVector firstRawRoute)))
          (retainedFinalCoordinatedOccurrenceSlot
            formula firstLiteral clauseIndex firstLiteralIndex))
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement order
            scaledClause firstLiteral clauseIndex firstLiteralIndex))
    let secondExplicit :=
      joinAtEndpoint
        (retainedAngularFanSplicedBoundaryRoute
          (scalePolyline retainedAngularFanSourceClearanceFactor
            secondRawRoute)
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            (classifiedRetainedTerminalData
              (routeTerminalVector secondRawRoute)))
          (retainedFinalCoordinatedOccurrenceSlot
            formula secondLiteral clauseIndex secondLiteralIndex))
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix placement order
            scaledClause secondLiteral clauseIndex secondLiteralIndex))
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex firstLiteralIndex =
      firstExplicit ∧
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
        formula clauseIndex secondLiteralIndex =
      secondExplicit := by
  dsimp only
  have finalClauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx := by
    simpa [finalCoordinatedSource] using clauseMember
  have secondChoiceNone :=
    retainedFinalDirectSourceRouteChoice_eq_none_of_sameClause_choice_none
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember
      firstLiteralMember secondLiteralMember firstChoiceNone
  constructor
  · exact
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
          formula clauseIndex firstLiteralIndex
          firstChoiceNone firstPrefixLengthNeOne).trans
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty finalClauseMember firstLiteralMember)
  · exact
      (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_of_choice_none_of_prefix_length_ne_one
          formula clauseIndex secondLiteralIndex
          secondChoiceNone secondPrefixLengthNeOne).trans
        (retainedDrawingSourceScaledRefinedEightOccurrenceSplitIncidenceRoutes_eq_explicitOccurrenceJoin
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty finalClauseMember secondLiteralMember)

/-- The public total route family separates the complementary failed-selector
branch in which both source prefixes are non-singletons and therefore retain
their ordinary outer fans. -/
def
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_separated_of_choice_none_of_prefix_lengths_ne_one
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
    (firstChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex firstLiteralIndex = none)
    (firstPrefixLengthNeOne :
      (finalCoordinatedSourceRoutes
        formula clauseIndex firstLiteralIndex).dropLast.length ≠ 1)
    (secondPrefixLengthNeOne :
      (finalCoordinatedSourceRoutes
        formula clauseIndex secondLiteralIndex).dropLast.length ≠ 1)
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    RoutesSeparatedAtHeads
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex firstLiteralIndex)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex secondLiteralIndex) := by
  have finalClauseMember :
      (clause, clauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx := by
    simpa [finalCoordinatedSource] using clauseMember
  have modelEqualities :=
    coordinatedFallbackRouteModels_of_choice_none_of_prefix_lengths_ne_one
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember
      firstLiteralMember secondLiteralMember
      firstChoiceNone firstPrefixLengthNeOne
      secondPrefixLengthNeOne
  have separated :=
    retainedFinalSameClauseOrdinaryFallbackExplicitOccurrenceRoutes_separated
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty finalClauseMember
      firstLiteralMember secondLiteralMember literalIndicesDifferent
      firstChoiceNone firstPrefixLengthNeOne
      secondPrefixLengthNeOne
  exact
    ⟨_, _, modelEqualities.1, modelEqualities.2,
      separated.1, separated.2⟩

/-- Unconditional same-clause separation for two distinct genuine entries
of the public coordinated route family.  Selector success is uniform across
the clause; on uniform failure, the two prefix-length tests choose between
the escaped-first, escaped-second, and ordinary/ordinary certificates. -/
theorem
    retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_separated
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
    (literalIndicesDifferent :
      firstLiteralIndex ≠ secondLiteralIndex) :
    RoutesAvoidEachOther
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex firstLiteralIndex)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex secondLiteralIndex) ∧
      RoutesMeetOnlyAtHeads
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex firstLiteralIndex)
        (retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes
          formula clauseIndex secondLiteralIndex) := by
  cases firstChoiceLookup :
      retainedFinalDirectSourceRouteChoice?
        formula clauseIndex firstLiteralIndex with
  | some firstChoice =>
      rcases
          retainedFinalDirectSourceRouteChoice_exists_of_sameClause_choice_some
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember
            secondLiteralMember firstChoice firstChoiceLookup with
        ⟨secondChoice, secondChoiceLookup⟩
      have separated :=
        retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_separated_of_choices_some
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty firstChoice secondChoice
          clauseMember firstLiteralMember secondLiteralMember
          firstChoiceLookup secondChoiceLookup
          literalIndicesDifferent
      exact separated
  | none =>
      by_cases firstPrefixLength :
          (finalCoordinatedSourceRoutes
            formula clauseIndex firstLiteralIndex).dropLast.length = 1
      · have certificate :=
          retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_separated_of_choice_none_of_prefix_length_one
            formula sourceLocal sourceWidth sourceOccurrences
            sourceClausesNonempty clauseMember
            firstLiteralMember secondLiteralMember
            firstChoiceLookup firstPrefixLength
            literalIndicesDifferent
        exact
          ⟨certificate.avoid,
            certificate.meetOnlyAtHeads⟩
      · by_cases secondPrefixLength :
            (finalCoordinatedSourceRoutes
              formula clauseIndex secondLiteralIndex).dropLast.length = 1
        · have secondChoiceNone :=
            retainedFinalDirectSourceRouteChoice_eq_none_of_sameClause_choice_none
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty clauseMember
              firstLiteralMember secondLiteralMember
              firstChoiceLookup
          have certificate :=
            retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_separated_of_choice_none_of_second_prefix_length_one
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty clauseMember
              firstLiteralMember secondLiteralMember
              secondChoiceNone secondPrefixLength
              literalIndicesDifferent
          exact
            ⟨certificate.avoid,
              certificate.meetOnlyAtHeads⟩
        · have certificate :=
            retainedDrawingSourceScaledCoordinatedEightOccurrenceSplitIncidenceRoutes_separated_of_choice_none_of_prefix_lengths_ne_one
              formula sourceLocal sourceWidth sourceOccurrences
              sourceClausesNonempty clauseMember
              firstLiteralMember secondLiteralMember
              firstChoiceLookup firstPrefixLength
              secondPrefixLength literalIndicesDifferent
          exact
            ⟨certificate.avoid,
              certificate.meetOnlyAtHeads⟩

end PeriodicOrthocrossing
end LeanTrominoes
