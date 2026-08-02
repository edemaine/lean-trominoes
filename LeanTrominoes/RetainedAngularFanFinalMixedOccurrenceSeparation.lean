import LeanTrominoes.RetainedAngularFanFinalMixedAlignedOccurrenceSeparation
import LeanTrominoes.RetainedAngularFanFinalMixedObliqueCorridorSeparation
import LeanTrominoes.RetainedAngularFanFinalDirectSourceFallbackPrefixSeparation
import LeanTrominoes.RetainedAngularFanFinalRoutedClausePrefixSeparation

/-!
# Complete final mixed occurrence separation

The aligned and oblique source-corridor theorems cover the non-routed direct
choices.  Routed-clause choices use flat-component separation for their wide
escape and the ordinary corridor for their tail.  Together these cases give
unconditional separation from a same-center cross-clause fallback occurrence.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 400000

/-- A non-routed oblique direct occurrence strictly avoids a same-center
cross-clause fallback occurrence in the final coordinated drawing. -/
theorem
    retainedFinalCoordinatedObliqueDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence
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
    (kindNe : choice.kind ≠ .routedClause)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (clauseIndicesDifferent :
      directClauseIndex ≠ fallbackClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral)
    (directOblique : ¬choice.sourceSegment.IsAxisAligned) :
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
  have representedSegment :=
    retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
      formula directClauseIndex directLiteralIndex choice choiceLookup
  have directFinalOblique :
      ¬(⟨polylineLastEntrance
            (finalCoordinatedSourceRoutes
              formula directClauseIndex directLiteralIndex),
          (finalCoordinatedSourceRoutes
            formula directClauseIndex directLiteralIndex).getLastD
              (0, 0)⟩ : GridSegment).IsAxisAligned := by
    rw [representedSegment]
    exact directOblique
  apply
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence_of_corridor
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember
      choiceLookup kindNe fallbackChoiceNone clauseIndicesDifferent
      centersEqual
  exact
    retainedFinalDirectFallback_sourcePrefixCorridorSeparated_of_directSegment_not_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember
      choiceLookup fallbackChoiceNone clauseIndicesDifferent
      directFinalOblique

/-- A routed-clause direct occurrence strictly avoids a same-center
cross-clause fallback occurrence.  Flat-component reduction handles its wide
escape, while the ordinary corridor handles its post-escape tail. -/
theorem
    retainedFinalCoordinatedRoutedClauseDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence
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
    (kindEq : choice.kind = RetainedDirectClauseKind.routedClause)
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (clauseIndicesDifferent :
      directClauseIndex ≠ fallbackClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral) :
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
  have fallbackSourceNeDirectTarget :
      PositionedPeriodicCNF.canonicalClausePosition
          placement fallbackClause ≠
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement directClause directLiteral := by
    rw [fallbackEndpoints.1, directEndpoints.2]
      at fallbackHeadNeDirectLast
    simpa [fallbackRoute, directRoute, routes] using
      fallbackHeadNeDirectLast
  have representedSegment :=
    retainedFinalDirectSourceRouteChoice_finalSegment_eq_sourceSegment
      formula directClauseIndex directLiteralIndex choice choiceLookup
  have directOblique :
      ¬(⟨polylineLastEntrance directRoute,
          directRoute.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned := by
    have choiceOblique :=
      choice.sourceSegment_not_axisAligned_of_kind_eq_routedClause kindEq
    rw [representedSegment]
    exact choiceOblique
  have directLastD :
      directRoute.getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement directClause directLiteral := by
    rw [List.getLastD_eq_getLast?, directLast]
    rfl
  have directFinalOblique :
      ¬(⟨polylineLastEntrance directRoute,
          PositionedPeriodicCNF.canonicalLiteralPosition
            placement directClause directLiteral⟩ :
        GridSegment).IsAxisAligned := by
    rw [← directLastD]
    exact directOblique
  have corridor :
      SourcePrefixCorridorSeparated
        fallbackRoute directRoute
        (retainedDirectSourceFanTerminalAt
          choice.kind choice.index).1 := by
    simpa [fallbackRoute, directRoute, routes] using
      retainedFinalDirectFallback_sourcePrefixCorridorSeparated_of_directSegment_not_axisAligned
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        choiceLookup fallbackChoiceNone clauseIndicesDifferent
        (by simpa [directRoute, routes] using directOblique)
  have tailAvoid :=
    retainedFinalSourceScaledPrefix_strictlyAvoids_directCompleteTail_of_corridorSeparated
      formula certificate.graphWellFormed
      certificate.graphDegreeAtMostThree
      certificate.graphIsLocal retainedClausesNonempty
      fallbackRoute fallbackRouteIndex directRouteIndex
      (PositionedPeriodicCNF.canonicalClausePosition
        placement fallbackClause)
      (PositionedPeriodicCNF.canonicalLiteralPosition
        placement directClause directLiteral)
      directClauseIndex directLiteralIndex choice
      (retainedFinalCoordinatedOccurrenceSlot
        formula directLiteral directClauseIndex directLiteralIndex)
      fallbackRouteMember directRouteMember
      fallbackLength directLength routeIndicesDifferent
      fallbackHead directLast fallbackSourceNeDirectTarget
      choiceLookup corridor
  have choiceRouteEq :
      translatePolyline choice.origin
          (retainedDirectSourceLocalRouteAt
            choice.kind choice.index) = directRoute := by
    have represents :=
      retainedFinalDirectSourceRouteChoice_representsFinalRoute
        formula directClauseIndex directLiteralIndex choice choiceLookup
    simpa [RetainedDirectSourceRouteChoice.RepresentsFinalRoute,
      directRoute, routes, finalCoordinatedSourceRoutes] using represents
  have fallbackTaggedIncidenceMember :
      ((⟨fallbackClauseIndex, fallbackClause.literals,
          fallbackLiteralIndex, fallbackLiteral⟩ :
            CNFIncidence
              (WrappedPeriodicPlanarSATVariable Variable)),
        fallbackRouteIndex) ∈
          (finalGaugedIncidences formula).zipIdx := by
    simpa [finalGaugedIncidences, source,
      finalCoordinatedSource] using fallbackIncidenceMember
  have rawPrefixAvoid :
      RoutesStrictlyAvoidEachOther
        (scalePolyline
          (retainedTerminalFanTotalRefinement * 4)
          fallbackRoute.dropLast)
        (choice.completeRoute
          (retainedFinalCoordinatedOccurrenceSlot
            formula directLiteral directClauseIndex directLiteralIndex)) := by
    apply
      retainedFinalSourceScaledPrefix_strictlyAvoids_routedClauseChoiceCompleteRoute_of_flatComponentCases
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal retainedClausesNonempty
        fallbackRouteMember directRouteMember
        directLength directLast directFinalOblique choice
        (retainedFinalCoordinatedOccurrenceSlot
          formula directLiteral directClauseIndex directLiteralIndex)
        kindEq choiceRouteEq tailAvoid
    intro fallbackMacrocell directMacrocell centersEqual
    exfalso
    exact
      FinalGaugedFlatRouteMacrocellWitness.translatedCenter_ne_of_incidence_choice_none_of_second_finalSegment_not_axisAligned
        formula certificate.graphWellFormed
        certificate.graphDegreeAtMostThree
        certificate.graphIsLocal
        fallbackMacrocell directMacrocell
        fallbackTaggedIncidenceMember fallbackChoiceNone
        directLength directLast directFinalOblique centersEqual
  have sourcePrefixAvoid :
      RoutesStrictlyAvoidEachOther
        (choice.completeRoute
          (retainedFinalCoordinatedOccurrenceSlot
            formula directLiteral directClauseIndex directLiteralIndex))
        (scalePolyline retainedTerminalFanTotalRefinement
          (scalePolyline retainedAngularFanSourceClearanceFactor
            fallbackRoute)).dropLast := by
    rw [scalePolyline_dropLast_eq,
      scalePolyline_dropLast_eq,
      scalePolyline_scalePolyline_nat]
    simpa only [retainedAngularFanSourceClearanceFactor,
      Nat.cast_ofNat] using rawPrefixAvoid.symm
  exact
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence_of_sourcePrefix_sameCenter
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty choice
      directClauseMember fallbackClauseMember
      directLiteralMember fallbackLiteralMember
      choiceLookup fallbackChoiceNone clauseIndicesDifferent
      centersEqual
      (by simpa [fallbackRoute, routes] using sourcePrefixAvoid)

/-- Every successful direct occurrence strictly avoids a same-center
cross-clause fallback occurrence in the final coordinated drawing. -/
theorem
    retainedFinalCoordinatedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence
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
    (fallbackChoiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula fallbackClauseIndex fallbackLiteralIndex = none)
    (clauseIndicesDifferent :
      directClauseIndex ≠ fallbackClauseIndex)
    (centersEqual :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          directClause directLiteral =
        PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula)
          fallbackClause fallbackLiteral) :
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
  by_cases kindEq : choice.kind = .routedClause
  · exact
      retainedFinalCoordinatedRoutedClauseDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty choice
        directClauseMember fallbackClauseMember
        directLiteralMember fallbackLiteralMember
        choiceLookup kindEq fallbackChoiceNone clauseIndicesDifferent
        centersEqual
  · by_cases directAligned : choice.sourceSegment.IsAxisAligned
    · exact
        retainedFinalCoordinatedAlignedDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty choice
          directClauseMember fallbackClauseMember
          directLiteralMember fallbackLiteralMember
          choiceLookup kindEq fallbackChoiceNone clauseIndicesDifferent
          centersEqual directAligned
    · exact
        retainedFinalCoordinatedObliqueDirectOccurrenceRoute_strictlyAvoids_crossClauseFallbackOccurrence
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty choice
          directClauseMember fallbackClauseMember
          directLiteralMember fallbackLiteralMember
          choiceLookup kindEq fallbackChoiceNone clauseIndicesDifferent
          centersEqual directAligned

end PeriodicOrthocrossing
end LeanTrominoes
