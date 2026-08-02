import LeanTrominoes.RetainedAngularFanFinalMixedAlignedCorridorSeparation
import LeanTrominoes.RetainedAngularFanFinalMixedOccurrenceAssembly
import LeanTrominoes.RetainedAngularFanFinalFallbackSegmentClassification

/-!
# Distinct-center final mixed occurrence separation

For an axis-aligned successful direct choice, a failed fallback choice also
has an axis-aligned final source segment.  At distinct literal centers the
two retained incidences have four distinct endpoints, so retained planarity
strictly separates their final-segment rectangles.  Together with the
already established source corridor, this separates the complete selected
direct occurrence from the fallback occurrence.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 1000000

/-- At distinct literal centers, an aligned successful direct source segment
has a strictly separated endpoint rectangle from a failed fallback source
segment in another clause. -/
theorem
    retainedFinalDirectFallback_finalSegmentRectanglesSeparated_of_distinctCenters_of_directSegment_axisAligned
    {Variable : Type*} [variableDecEq : DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (clauseIndicesDifferent :
      directClauseIndex ≠ fallbackClauseIndex)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral)
    (directAligned : choice.sourceSegment.IsAxisAligned) :
    let fallbackRoute :=
      finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex
    ClosedGridRectanglesSeparated
      choice.sourceSegment.coordinateLower
      choice.sourceSegment.coordinateUpper
      (⟨polylineLastEntrance fallbackRoute,
          fallbackRoute.getLastD (0, 0)⟩ : GridSegment).coordinateLower
      (⟨polylineLastEntrance fallbackRoute,
          fallbackRoute.getLastD (0, 0)⟩ : GridSegment).coordinateUpper := by
  dsimp only
  let certificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  let directRoute :=
    routes directClauseIndex directLiteralIndex
  let fallbackRoute :=
    routes fallbackClauseIndex fallbackLiteralIndex
  have copiesDifferent :
      (directLiteral.atom, directClauseIndex, directLiteralIndex) ≠
        (fallbackLiteral.atom, fallbackClauseIndex, fallbackLiteralIndex) := by
    intro copiesEqual
    apply clauseIndicesDifferent
    exact congrArg (fun copy => copy.2.1) copiesEqual
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        directClauseMember directLiteralMember with
    ⟨directRouteIndex, directIncidenceMember, directRouteMember⟩
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        fallbackClauseMember fallbackLiteralMember with
    ⟨fallbackRouteIndex, fallbackIncidenceMember, fallbackRouteMember⟩
  have routeIndicesDifferent :
      directRouteIndex ≠ fallbackRouteIndex := by
    intro indicesEqual
    apply copiesDifferent
    have taggedEqual :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        directIncidenceMember fallbackIncidenceMember indicesEqual
    have incidenceEqual := congrArg Prod.fst taggedEqual
    exact
      congrArg
        (fun incidence :
            CNFIncidence
              (WrappedPeriodicPlanarSATVariable Variable) =>
          (incidence.literal.atom, incidence.clauseIndex,
            incidence.literalIndex))
        incidenceEqual
  have directLength : 2 ≤ directRoute.length := by
    simpa [directRoute, routes, source] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackLength : 2 ≤ fallbackRoute.length := by
    simpa [fallbackRoute, routes, source] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have directEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty directClauseMember directLiteralMember
  have fallbackEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have compatible :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal retainedClausesNonempty
  have directHeadNeFallbackLast :=
    @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
      (WrappedPeriodicPlanarSATVariable Variable)
      (fun first second =>
        @instDecidableEqWrappedPeriodicVariable
          (PeriodicPlanarSATVariable Variable)
          (fun firstOriginal secondOriginal =>
            @instDecidableEqPeriodicPlanarSATVariable
              Variable variableDecEq firstOriginal secondOriginal)
          first second)
      source placement routes compatible
      _ _ directIncidenceMember fallbackIncidenceMember
  have fallbackHeadNeDirectLast :=
    @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
      (WrappedPeriodicPlanarSATVariable Variable)
      (fun first second =>
        @instDecidableEqWrappedPeriodicVariable
          (PeriodicPlanarSATVariable Variable)
          (fun firstOriginal secondOriginal =>
            @instDecidableEqPeriodicPlanarSATVariable
              Variable variableDecEq firstOriginal secondOriginal)
          first second)
      source placement routes compatible
      _ _ fallbackIncidenceMember directIncidenceMember
  have sourcesDifferent :=
    retainedFinalCanonicalClausePositions_ne
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      directClauseMember fallbackClauseMember
      clauseIndicesDifferent
  have headsDifferent :
      directRoute.head? ≠ fallbackRoute.head? := by
    rw [show directRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement directClause) by
          simpa [directRoute, routes, placement] using directEndpoints.1,
      show fallbackRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement fallbackClause) by
          simpa [fallbackRoute, routes, placement] using fallbackEndpoints.1]
    exact fun equal => sourcesDifferent (Option.some.inj equal)
  have endsDifferent :
      directRoute.getLast? ≠ fallbackRoute.getLast? := by
    rw [show directRoute.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement directClause directLiteral) by
          simpa [directRoute, routes, placement] using directEndpoints.2,
      show fallbackRoute.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement fallbackClause fallbackLiteral) by
          simpa [fallbackRoute, routes, placement] using fallbackEndpoints.2]
    exact fun equal => centersDifferent (Option.some.inj equal)
  have directFinalAligned :
      (⟨polylineLastEntrance directRoute,
          directRoute.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned := by
    have representedSegment :=
      retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
        formula directClauseIndex directLiteralIndex choice choiceLookup
    rw [show directRoute =
        finalCoordinatedSourceRoutes
          formula directClauseIndex directLiteralIndex from rfl,
      representedSegment]
    exact directAligned
  have fallbackFinalAligned :
      (⟨polylineLastEntrance fallbackRoute,
          fallbackRoute.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned := by
    simpa [fallbackRoute, routes] using
      finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty
        fallbackClauseMember fallbackLiteralMember fallbackChoiceNone
  have separated :=
    retainedDeduplicatedGaugedWrappedDrawing_finalSegmentRectanglesSeparated_of_axisAligned
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree certificate.graphIsLocal
      retainedClausesNonempty
      directRouteMember fallbackRouteMember
      directLength fallbackLength routeIndicesDifferent
      headsDifferent directHeadNeFallbackLast
      fallbackHeadNeDirectLast.symm endsDifferent
      directFinalAligned fallbackFinalAligned
  have representedSegment :=
    retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
      formula directClauseIndex directLiteralIndex choice choiceLookup
  have separated' :
      ClosedGridRectanglesSeparated
        (⟨polylineLastEntrance
              (finalCoordinatedSourceRoutes
                formula directClauseIndex directLiteralIndex),
            (finalCoordinatedSourceRoutes
              formula directClauseIndex directLiteralIndex).getLastD
                (0, 0)⟩ : GridSegment).coordinateLower
        (⟨polylineLastEntrance
              (finalCoordinatedSourceRoutes
                formula directClauseIndex directLiteralIndex),
            (finalCoordinatedSourceRoutes
              formula directClauseIndex directLiteralIndex).getLastD
                (0, 0)⟩ : GridSegment).coordinateUpper
        (⟨polylineLastEntrance
              (finalCoordinatedSourceRoutes
                formula fallbackClauseIndex fallbackLiteralIndex),
            (finalCoordinatedSourceRoutes
              formula fallbackClauseIndex fallbackLiteralIndex).getLastD
                (0, 0)⟩ : GridSegment).coordinateLower
        (⟨polylineLastEntrance
              (finalCoordinatedSourceRoutes
                formula fallbackClauseIndex fallbackLiteralIndex),
            (finalCoordinatedSourceRoutes
              formula fallbackClauseIndex fallbackLiteralIndex).getLastD
                (0, 0)⟩ : GridSegment).coordinateUpper := by
    simpa only [routes] using separated
  rw [representedSegment] at separated'
  exact separated'

/-- An aligned successful direct occurrence strictly avoids a distinct-center
failed fallback occurrence from another clause. -/
theorem
    retainedFinalCoordinatedAlignedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence_of_distinctCenter
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (sourceLocal : formula.IsLocal)
    (sourceWidth : formula.WidthAtMost 3)
    (sourceOccurrences : formula.OccurrencesAtMost 3)
    (sourceClausesNonempty :
      ∀ clause ∈ formula.clauses, clause ≠ [])
    (choice : RetainedDirectSourceRouteChoice)
    {directClause fallbackClause :
      PositionedPeriodicClause
        (WrappedPeriodicPlanarSATVariable Variable)}
    {directClauseIndex fallbackClauseIndex : Nat}
    (directClauseMember :
      (directClause, directClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    (fallbackClauseMember :
      (fallbackClause, fallbackClauseIndex) ∈
        (finalCoordinatedSource formula).clauses.zipIdx)
    {directLiteral fallbackLiteral :
      PeriodicLiteral (WrappedPeriodicPlanarSATVariable Variable)}
    {directLiteralIndex fallbackLiteralIndex : Nat}
    (directLiteralMember :
      (directLiteral, directLiteralIndex) ∈
        directClause.literals.zipIdx)
    (fallbackLiteralMember :
      (fallbackLiteral, fallbackLiteralIndex) ∈
        fallbackClause.literals.zipIdx)
    (choiceLookup :
      retainedFinalDirectSourceRouteChoice?
          formula directClauseIndex directLiteralIndex = some choice)
    (kindNe : choice.kind ≠ .routedClause)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (clauseIndicesDifferent :
      directClauseIndex ≠ fallbackClauseIndex)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral)
    (directAligned : choice.sourceSegment.IsAxisAligned) :
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
    let fallbackSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement
          (angularOccurrenceOrder source.erase routes)
          (fallbackClause.scale retainedAngularFanSourceClearanceFactor)
          fallbackLiteral fallbackClauseIndex fallbackLiteralIndex)
    RoutesStrictlyAvoidEachOther
      (retainedFinalCoordinatedDirectOccurrenceRoute
        formula choice
        (directClause.scale retainedAngularFanSourceClearanceFactor)
        directLiteral directClauseIndex directLiteralIndex)
      (joinAtEndpoint
        (retainedFinalCoordinatedFallbackBoundaryPrefix
          formula fallbackLiteral
          fallbackClauseIndex fallbackLiteralIndex)
        fallbackSuffix) := by
  apply
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence_of_corridor_finalSegmentRectanglesSeparated
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember
      choiceLookup kindNe fallbackChoiceNone clauseIndicesDifferent
  · exact
      retainedFinalDirectFallback_sourcePrefixCorridorSeparated_of_directSegment_axisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        choiceLookup clauseIndicesDifferent directAligned
  · exact
      retainedFinalDirectFallback_finalSegmentRectanglesSeparated_of_distinctCenters_of_directSegment_axisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        choiceLookup fallbackChoiceNone clauseIndicesDifferent
        centersDifferent directAligned

end PeriodicOrthocrossing
end LeanTrominoes
