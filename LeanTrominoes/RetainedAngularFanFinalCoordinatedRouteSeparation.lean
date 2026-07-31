import LeanTrominoes.RetainedAngularFanFinalDirectSourceSpokeIdentification
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRoutePairs
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

end PeriodicOrthocrossing
end LeanTrominoes
