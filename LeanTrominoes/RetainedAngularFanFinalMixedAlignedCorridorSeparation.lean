import LeanTrominoes.RetainedAngularFanFinalDirectSourceAlignedOrthogonality
import LeanTrominoes.RetainedAngularFanFinalDirectSourceTerminalClassification
import LeanTrominoes.RetainedAngularFanFinalDirectSourceSameTargetClassification
import LeanTrominoes.RetainedFinalRoutePrefixRectangleSeparation

/-!
# Source corridors for aligned final mixed pairs

When a successful direct source segment is axis-aligned, the retained
drawing's strict prefix separation lifts to the exact rectangle corridor
used by the final mixed direct/fallback assembly.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 200000

/-- A cross-clause source prefix has the required corridor against every
successful aligned direct source segment. -/
theorem
    retainedFinalDirectFallback_sourcePrefixCorridorSeparated_of_directSegment_axisAligned
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
          formula directClauseIndex directLiteralIndex =
        some choice)
    (clauseIndicesDifferent :
      directClauseIndex ≠ fallbackClauseIndex)
    (directAligned : choice.sourceSegment.IsAxisAligned) :
    SourcePrefixCorridorSeparated
      (finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex)
      (finalCoordinatedSourceRoutes
        formula directClauseIndex directLiteralIndex)
      (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 := by
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
  let directTerminal : RetainedTerminalData :=
    ((retainedDirectSourceFanTerminalAt
      choice.kind choice.index).1,
      (retainedDirectSourceLocalTerminalAt
        choice.kind choice.index).2)
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
      fallbackRouteIndex ≠ directRouteIndex := by
    intro indicesEqual
    apply copiesDifferent
    have taggedEqual :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        fallbackIncidenceMember directIncidenceMember indicesEqual
    have incidenceEqual := congrArg Prod.fst taggedEqual
    exact
      (congrArg
        (fun incidence :
            CNFIncidence
              (WrappedPeriodicPlanarSATVariable Variable) =>
          (incidence.literal.atom, incidence.clauseIndex,
            incidence.literalIndex))
        incidenceEqual).symm
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
  have directLast :
      directRoute.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement directClause directLiteral) := by
    exact directEndpoints.2
  have fallbackHead :
      fallbackRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement fallbackClause) := by
    exact fallbackEndpoints.1
  have compatible :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal retainedClausesNonempty
  have fallbackHeadNeDirectLast :=
    @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
      (WrappedPeriodicPlanarSATVariable Variable)
      (fun first second =>
        @instDecidableEqWrappedPeriodicVariable
          (PeriodicPlanarSATVariable Variable)
          (fun firstOriginal secondOriginal =>
            @instDecidableEqPeriodicPlanarSATVariable
              Variable inferInstance firstOriginal secondOriginal)
          first second)
      source placement routes compatible
      _ _ fallbackIncidenceMember directIncidenceMember
  have sourcesDifferent :=
    retainedFinalCanonicalClausePositions_ne
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      fallbackClauseMember directClauseMember
      (Ne.symm clauseIndicesDifferent)
  have headsDifferent : fallbackRoute.head? ≠ directRoute.head? := by
    rw [show fallbackRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement fallbackClause) by
          simpa [fallbackRoute, routes, placement] using
            fallbackEndpoints.1,
      show directRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            placement directClause) by
          simpa [directRoute, routes, placement] using
            directEndpoints.1]
    exact fun equal => sourcesDifferent (Option.some.inj equal)
  have fallbackSourceNeDirectTarget :
      PositionedPeriodicCNF.canonicalClausePosition
          placement fallbackClause ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement directClause directLiteral := by
    rw [fallbackEndpoints.1, directEndpoints.2]
      at fallbackHeadNeDirectLast
    simpa [fallbackRoute, directRoute, routes] using
      fallbackHeadNeDirectLast
  have directOrthogonal : OrthogonalPolyline directRoute := by
    simpa [directRoute, routes] using
      retainedFinalDirectSourceRoute_orthogonal_of_sourceSegment_axisAligned
        formula directClauseIndex directLiteralIndex
        choice choiceLookup directAligned
  have directFinalAligned :
      (⟨polylineLastEntrance directRoute,
          PositionedPeriodicCNF.canonicalLiteralPosition
            placement directClause directLiteral⟩ :
        GridSegment).IsAxisAligned := by
    have aligned :=
      (orthogonalPolyline_iff_segments directRoute).mp
        directOrthogonal
        (⟨polylineLastEntrance directRoute,
          directRoute.getLastD (0, 0)⟩ : GridSegment)
        (finalGridSegment_mem directRoute directLength)
    have directLastD :
        directRoute.getLastD (0, 0) =
          PositionedPeriodicCNF.canonicalLiteralPosition
            placement directClause directLiteral := by
      rw [List.getLastD_eq_getLast?, directLast]
      rfl
    rwa [directLastD] at aligned
  have rectanglesSeparated :
      SourcePolylineRectanglesSeparated
        fallbackRoute.dropLast directRoute := by
    exact
      retainedDeduplicatedGaugedWrappedDrawing_routePrefix_sourcePolylineRectanglesSeparated_of_finalSegmentAxisAligned
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal retainedClausesNonempty
        fallbackRouteMember directRouteMember
        fallbackLength directLength
        routeIndicesDifferent headsDifferent
        fallbackHead directLast
        fallbackSourceNeDirectTarget directFinalAligned
  have fallbackRetained : RetainedRayPolyline fallbackRoute := by
    simpa [fallbackRoute, routes, source] using
      finalCoordinatedSourceRoutes_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty fallbackClauseMember fallbackLiteralMember
  have directRetained : RetainedRayPolyline directRoute := by
    simpa [directRoute, routes, source] using
      finalCoordinatedSourceRoutes_retainedRay
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty directClauseMember directLiteralMember
  have directClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector directRoute) =
        some directTerminal := by
    simpa only [directRoute, directTerminal, routes] using
      retainedFinalDirectSourceRouteChoice_terminalClassify
        formula directClauseIndex directLiteralIndex choice choiceLookup
  rw [show
    finalCoordinatedSourceRoutes
        formula fallbackClauseIndex fallbackLiteralIndex =
      fallbackRoute from rfl]
  rw [show
    finalCoordinatedSourceRoutes
        formula directClauseIndex directLiteralIndex =
      directRoute from rfl]
  rw [show
    (retainedDirectSourceFanTerminalAt
        choice.kind choice.index).1 =
      directTerminal.1 from rfl]
  exact
    sourcePrefixCorridorSeparated_of_sourcePolylineRectanglesSeparated
      fallbackRoute directRoute directTerminal
      fallbackRetained directRetained
      fallbackLength directLength directClassified rectanglesSeparated

end PeriodicOrthocrossing
end LeanTrominoes
