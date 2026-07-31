import LeanTrominoes.RetainedAngularFanFallbackPrefixLengths
import LeanTrominoes.RetainedAngularFanFinalCarrierLensSingletonGeometry
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity
import LeanTrominoes.RetainedAngularFanFinalOccurrenceSuffixSeparation
import LeanTrominoes.RetainedAngularFanSourceEscapedSpliceSeparation
import LeanTrominoes.RetainedFinalEscapedOuterFanSeparation
import LeanTrominoes.RetainedFinalRoutePrefixSeparation
import LeanTrominoes.PositionedPeriodicCNFRetainedRayRasterization

/-!
# Same-clause separation for one escaped final fallback

When the final direct-source selector fails and the first copied source
route has a singleton prefix, its common fallback component cannot be a
bend.  Both routes therefore come from one carrier equality lens.  The
singleton lens calculation controls the only permitted escaped-fan/prefix
contact, while global retained planarity controls the old source routes and
the two discarded terminal corridors.

This file assembles those facts before rasterization.  The result is the
head-only separation certificate for the escaped first boundary polyline
and ordinary second boundary polyline.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PeriodicThreeSATThree
open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 500000

/-- In one final source clause, replacing a singleton fallback prefix by
the delayed-lane escaped fan preserves head-only separation from the
ordinary fallback at every other literal. -/
theorem
    retainedFinalSameClauseEscapedOrdinarySplicedBoundaryPolylines_separated
    {Variable : Type*}
    [variableDecidableEq : DecidableEq Variable]
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
        (finalCoordinatedSource formula).clauses.zipIdx)
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
          formula clauseIndex firstLiteralIndex = none)
    (firstSingletonPrefix :
      (finalCoordinatedSourceRoutes
        formula clauseIndex firstLiteralIndex).dropLast.length = 1) :
    let firstRawRoute :=
      finalCoordinatedSourceRoutes
        formula clauseIndex firstLiteralIndex
    let secondRawRoute :=
      finalCoordinatedSourceRoutes
        formula clauseIndex secondLiteralIndex
    let firstRawTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector firstRawRoute)
    let secondRawTerminal :=
      classifiedRetainedTerminalData
        (routeTerminalVector secondRawRoute)
    let firstSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula firstLiteral clauseIndex firstLiteralIndex
    let secondSlot :=
      retainedFinalCoordinatedOccurrenceSlot
        formula secondLiteral clauseIndex secondLiteralIndex
    let firstRoute :=
      scalePolyline retainedAngularFanSourceClearanceFactor
        firstRawRoute
    let secondRoute :=
      scalePolyline retainedAngularFanSourceClearanceFactor
        secondRawRoute
    let firstTerminal :=
      scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor firstRawTerminal
    let secondTerminal :=
      scaleRetainedTerminalData
        retainedAngularFanSourceClearanceFactor secondRawTerminal
    RoutesAvoidEachOther
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot)
        (retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) ∧
      RoutesMeetOnlyAtHeads
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot)
        (retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) := by
  dsimp only
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let wellFormed := sourceCertificate.graphWellFormed
  let degree := sourceCertificate.graphDegreeAtMostThree
  let isLocal := sourceCertificate.graphIsLocal
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let firstRawRoute :=
    finalCoordinatedSourceRoutes
      formula clauseIndex firstLiteralIndex
  let secondRawRoute :=
    finalCoordinatedSourceRoutes
      formula clauseIndex secondLiteralIndex
  let firstRawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector firstRawRoute)
  let secondRawTerminal :=
    classifiedRetainedTerminalData
      (routeTerminalVector secondRawRoute)
  let firstSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula firstLiteral clauseIndex firstLiteralIndex
  let secondSlot :=
    retainedFinalCoordinatedOccurrenceSlot
      formula secondLiteral clauseIndex secondLiteralIndex
  let firstRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      firstRawRoute
  let secondRoute :=
    scalePolyline retainedAngularFanSourceClearanceFactor
      secondRawRoute
  let firstTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor firstRawTerminal
  let secondTerminal :=
    scaleRetainedTerminalData
      retainedAngularFanSourceClearanceFactor secondRawTerminal
  have firstRawOccurrenceEq :
      firstRawRoute =
        finalGaugedRouteOccurrence
          formula clauseIndex firstLiteralIndex (0, 0) := by
    unfold firstRawRoute finalCoordinatedSourceRoutes
      finalGaugedRouteOccurrence translatePolyline
    have zeroTranslation :
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation (0, 0) = (0, 0) := by
      simp [PeriodicVariablePlacement.translation, Cell.scale]
    rw [zeroTranslation]
    induction
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula clauseIndex firstLiteralIndex) with
    | nil => rfl
    | cons point points induction =>
        simp only [List.map_cons]
        rw [induction]
        simp [Cell.add]
  have secondRawOccurrenceEq :
      secondRawRoute =
        finalGaugedRouteOccurrence
          formula clauseIndex secondLiteralIndex (0, 0) := by
    unfold secondRawRoute finalCoordinatedSourceRoutes
      finalGaugedRouteOccurrence translatePolyline
    have zeroTranslation :
        (retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement
          formula).translation (0, 0) = (0, 0) := by
      simp [PeriodicVariablePlacement.translation, Cell.scale]
    rw [zeroTranslation]
    induction
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula clauseIndex secondLiteralIndex) with
    | nil => rfl
    | cons point points induction =>
        simp only [List.map_cons]
        rw [induction]
        simp [Cell.add]
  rcases
      exists_sameMetadata_carrier_or_bend_witnesses_of_sameClause_choice_none
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember
        firstLiteralMember secondLiteralMember
        firstChoiceNone with
    ⟨firstWitness, secondWitness, metadataEq,
      sourceCases⟩
  rcases sourceCases with
    ⟨link, localClauseIndex, firstSourceEq⟩ |
      ⟨routeBend, localClauseIndex, firstSourceEq⟩
  · have secondSourceEq :
        secondWitness.metadata.source =
          .carrier link localClauseIndex :=
      (congrArg DrawingPlanarSATClauseMetadata.source metadataEq).symm.trans
        firstSourceEq
    have secondLiteralIndexLt :
        secondLiteralIndex < 2 :=
      secondWitness.literalIndex_lt_two_of_carrier
        link localClauseIndex secondSourceEq
    have firstLength :
        2 ≤ firstRawRoute.length := by
      exact
        finalCoordinatedSourceRoutes_length_ge_two
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember firstLiteralMember
    have secondLength :
        2 ≤ secondRawRoute.length := by
      exact
        finalCoordinatedSourceRoutes_length_ge_two
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember secondLiteralMember
    have firstClassified :
        retainedTerminalDirectionClassify
            (routeTerminalVector firstRawRoute) =
          some firstRawTerminal := by
      simpa [firstRawRoute, firstRawTerminal] using
        finalCoordinatedSourceRoute_classified
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember firstLiteralMember
    have secondClassified :
        retainedTerminalDirectionClassify
            (routeTerminalVector secondRawRoute) =
          some secondRawTerminal := by
      simpa [secondRawRoute, secondRawTerminal] using
        finalCoordinatedSourceRoute_classified
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember secondLiteralMember
    rcases
        PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
          (finalCoordinatedSource formula)
          (finalCoordinatedPlacement formula)
          (finalCoordinatedSourceRoutes formula)
          clauseMember firstLiteralMember with
      ⟨firstRouteIndex, firstIncidenceMember, firstRouteMember⟩
    rcases
        PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
          (finalCoordinatedSource formula)
          (finalCoordinatedPlacement formula)
          (finalCoordinatedSourceRoutes formula)
          clauseMember secondLiteralMember with
      ⟨secondRouteIndex, secondIncidenceMember, secondRouteMember⟩
    simp only [finalCoordinatedSource,
      finalCoordinatedPlacement, finalCoordinatedSourceRoutes]
      at firstRouteMember secondRouteMember
    change
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula clauseIndex firstLiteralIndex,
        firstRouteIndex) ∈
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).edgeRoutes.zipIdx at firstRouteMember
    change
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes
          formula clauseIndex secondLiteralIndex,
        secondRouteIndex) ∈
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).edgeRoutes.zipIdx at secondRouteMember
    have firstRawRouteMember :
        (firstRawRoute, firstRouteIndex) ∈
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).edgeRoutes.zipIdx := by
      simpa only [firstRawRoute, finalCoordinatedSourceRoutes] using
        firstRouteMember
    have secondRawRouteMember :
        (secondRawRoute, secondRouteIndex) ∈
          (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
            formula).edgeRoutes.zipIdx := by
      simpa only [secondRawRoute, finalCoordinatedSourceRoutes] using
        secondRouteMember
    have routeIndicesDifferent :
        firstRouteIndex ≠ secondRouteIndex := by
      intro indicesEqual
      have taggedEqual :=
        tagged_eq_of_mem_zipIdx_of_snd_eq
          firstIncidenceMember secondIncidenceMember
          indicesEqual
      exact indicesDifferent
        (congrArg
          (fun tagged :
              CNFIncidence
                  (WrappedPeriodicPlanarSATVariable Variable) × Nat =>
            tagged.1.literalIndex)
          taggedEqual)
    have firstNodup : firstRawRoute.Nodup := by
      simpa only [firstRawRoute, finalCoordinatedSourceRoutes] using
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoute_isSimple
          formula wellFormed degree isLocal retainedClausesNonempty
          (clause, clauseIndex)
          (by
            simpa only [finalCoordinatedSource] using clauseMember)
          (firstLiteral, firstLiteralIndex) firstLiteralMember).1
    have secondNodup : secondRawRoute.Nodup := by
      simpa only [secondRawRoute, finalCoordinatedSourceRoutes] using
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoute_isSimple
          formula wellFormed degree isLocal retainedClausesNonempty
          (clause, clauseIndex)
          (by
            simpa only [finalCoordinatedSource] using clauseMember)
          (secondLiteral, secondLiteralIndex) secondLiteralMember).1
    have rawRoutesAvoid :
        RoutesAvoidEachOther firstRawRoute secondRawRoute := by
      exact
        retainedDeduplicatedGaugedWrappedDrawing_routesAvoidEachOther
          formula wellFormed degree isLocal
          retainedClausesNonempty
          firstRawRouteMember secondRawRouteMember
          firstLength secondLength routeIndicesDifferent
    have firstEndpoints :=
      finalCoordinatedSourceRoutes_endpoints
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember firstLiteralMember
    have secondEndpoints :=
      finalCoordinatedSourceRoutes_endpoints
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember secondLiteralMember
    have compatible :=
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
        formula wellFormed degree isLocal retainedClausesNonempty
    have firstHeadNeSecondLast :=
      @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
        (WrappedPeriodicPlanarSATVariable Variable)
        (fun first second =>
          @instDecidableEqWrappedPeriodicVariable
            (PeriodicPlanarSATVariable Variable)
            (fun firstOriginal secondOriginal =>
              @instDecidableEqPeriodicPlanarSATVariable
                Variable variableDecidableEq
                firstOriginal secondOriginal)
            first second)
        (finalCoordinatedSource formula)
        (finalCoordinatedPlacement formula)
        (finalCoordinatedSourceRoutes formula)
        compatible _ _
        firstIncidenceMember secondIncidenceMember
    have secondHeadNeFirstLast :=
      @PositionedPeriodicCNF.route_head_ne_route_last_of_taggedIncidences
        (WrappedPeriodicPlanarSATVariable Variable)
        (fun first second =>
          @instDecidableEqWrappedPeriodicVariable
            (PeriodicPlanarSATVariable Variable)
            (fun firstOriginal secondOriginal =>
              @instDecidableEqPeriodicPlanarSATVariable
                Variable variableDecidableEq
                firstOriginal secondOriginal)
            first second)
        (finalCoordinatedSource formula)
        (finalCoordinatedPlacement formula)
        (finalCoordinatedSourceRoutes formula)
        compatible _ _
        secondIncidenceMember firstIncidenceMember
    have firstSourceNeSecondCenter :
        PositionedPeriodicCNF.canonicalClausePosition
            (finalCoordinatedPlacement formula) clause ≠
          PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause secondLiteral := by
      rw [firstEndpoints.1, secondEndpoints.2]
        at firstHeadNeSecondLast
      simpa using firstHeadNeSecondLast
    have secondSourceNeFirstCenter :
        PositionedPeriodicCNF.canonicalClausePosition
            (finalCoordinatedPlacement formula) clause ≠
          PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause firstLiteral := by
      rw [secondEndpoints.1, firstEndpoints.2]
        at secondHeadNeFirstLast
      simpa using secondHeadNeFirstLast
    have centersDifferent :
        PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause firstLiteral ≠
          PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause secondLiteral := by
      intro centersEqual
      apply
        retainedFinalSameClauseCanonicalLiteralPositions_ne
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember
          firstLiteralMember secondLiteralMember indicesDifferent
      simpa only [finalCoordinatedPlacement,
        PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale] using
          congrArg
            (Cell.scale retainedAngularFanSourceClearanceFactor)
            centersEqual
    have firstAligned :
        (⟨polylineLastEntrance firstRawRoute,
            firstRawRoute.getLastD (0, 0)⟩ :
          GridSegment).IsAxisAligned := by
      apply firstWitness.routeSegments_axisAligned_of_carrier
        wellFormed degree isLocal
        link localClauseIndex firstSourceEq
      rw [← firstRawOccurrenceEq]
      exact finalGridSegment_mem firstRawRoute firstLength
    have secondAligned :
        (⟨polylineLastEntrance secondRawRoute,
            secondRawRoute.getLastD (0, 0)⟩ :
          GridSegment).IsAxisAligned := by
      apply secondWitness.routeSegments_axisAligned_of_carrier
        wellFormed degree isLocal
        link localClauseIndex secondSourceEq
      rw [← secondRawOccurrenceEq]
      exact finalGridSegment_mem secondRawRoute secondLength
    have notBothSingleton :
        ¬(firstRawRoute.dropLast.length = 1 ∧
          secondRawRoute.dropLast.length = 1) := by
      simpa [firstRawRoute, secondRawRoute,
        ← firstRawOccurrenceEq, ← secondRawOccurrenceEq] using
        not_both_singletonPrefixes_of_sameMetadata_carrier_or_bend_witnesses
          formula firstWitness secondWitness metadataEq
          indicesDifferent
          (Or.inl ⟨link, localClauseIndex, firstSourceEq⟩)
    have firstEscapeFits :
        retainedTerminalFanOuterSourceEscapeLength ≤
          retainedTerminalFanOuterRadialLength
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              firstRawTerminal) := by
      simpa [firstRawRoute, firstRawTerminal] using
        finalCoordinatedScaledSourceRoute_escapeFits
          formula sourceLocal sourceWidth sourceOccurrences
          sourceClausesNonempty clauseMember firstLiteralMember
    have fansAvoid :
        RoutesStrictlyAvoidEachOther
          (retainedTerminalFanOuterEscapedCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              ((scalePolyline
                retainedAngularFanSourceClearanceFactor
                firstRawRoute).getLastD (0, 0)))
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              firstRawTerminal)
            firstSlot)
          (retainedTerminalFanOuterCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              ((scalePolyline
                retainedAngularFanSourceClearanceFactor
                secondRawRoute).getLastD (0, 0)))
            (scaleRetainedTerminalData
              retainedAngularFanSourceClearanceFactor
              secondRawTerminal)
            secondSlot) := by
      apply
        retainedFinalEscapedOuterCompleteRoute_strictlyAvoid_ordinary_of_axisAligned_of_not_both_singletonPrefixes
          formula wellFormed degree isLocal retainedClausesNonempty
          retainedAngularFanSourceClearanceFactor_pos
          (by native_decide)
          firstRawRouteMember secondRawRouteMember
          firstLength secondLength routeIndicesDifferent
          firstEndpoints.1 secondEndpoints.1
          firstEndpoints.2 secondEndpoints.2
          firstSourceNeSecondCenter secondSourceNeFirstCenter
          centersDifferent notBothSingleton
          firstAligned secondAligned
          firstRawTerminal secondRawTerminal firstSlot secondSlot
          firstClassified secondClassified firstEscapeFits
    have firstPrefixAvoidSecondFan :
        RoutesStrictlyAvoidEachOther
          (scalePolyline retainedTerminalFanTotalRefinement
            firstRoute).dropLast
          (retainedTerminalFanOuterCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              (secondRoute.getLastD (0, 0)))
            secondTerminal secondSlot) := by
      simpa [firstRoute, secondRoute, secondTerminal] using
        retainedAngularFanSourceScaledPrefix_strictlyAvoids_otherOuterCompleteRoute_of_singletonPrefix_of_escapedFansAvoid
          retainedAngularFanSourceClearanceFactor_pos
          firstRawRoute firstRawTerminal
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            secondRawTerminal)
          firstSlot secondSlot
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline
              retainedAngularFanSourceClearanceFactor
              secondRawRoute).getLastD (0, 0)))
          firstLength firstClassified firstSingletonPrefix
          fansAvoid
    rcases
        finalGaugedCarrierRoutes_singletonPrefix_escapedCompleteRoute_separated_from_partnerPrefix
          formula wellFormed degree isLocal
          firstWitness secondWitness metadataEq
          link localClauseIndex firstSourceEq
          indicesDifferent secondLiteralIndexLt
          retainedAngularFanSourceClearanceFactor
          retainedAngularFanSourceClearanceFactor_pos firstSlot
          (by simpa [← firstRawOccurrenceEq] using firstLength)
          (by
            simpa [← firstRawOccurrenceEq] using
              firstSingletonPrefix) with
      ⟨port, terminalLength, carrierClassified,
        escapedFanAvoidSecondPrefix,
        escapedFanSecondPrefixContactsAtHeads⟩
    have firstRawTerminalEq :
        firstRawTerminal = (.compass port, terminalLength) := by
      exact Option.some.inj
        (firstClassified.symm.trans
          (by simpa [← firstRawOccurrenceEq] using
            carrierClassified))
    have escapedFanAvoidSecondPrefix' :
        RoutesAvoidEachOther
          (retainedTerminalFanOuterEscapedCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              (firstRoute.getLastD (0, 0)))
            firstTerminal firstSlot)
          (scalePolyline retainedTerminalFanTotalRefinement
            secondRoute).dropLast := by
      simpa [firstRoute, secondRoute, firstTerminal,
        firstRawTerminalEq, ← firstRawOccurrenceEq,
        ← secondRawOccurrenceEq] using
        escapedFanAvoidSecondPrefix
    have escapedFanSecondPrefixContactsAtHeads' :
        RoutesMeetOnlyAtHeads
          (retainedTerminalFanOuterEscapedCompleteRoute
            (Cell.scale retainedTerminalFanTotalRefinement
              (firstRoute.getLastD (0, 0)))
            firstTerminal firstSlot)
          (scalePolyline retainedTerminalFanTotalRefinement
            secondRoute).dropLast := by
      simpa [firstRoute, secondRoute, firstTerminal,
        firstRawTerminalEq, ← firstRawOccurrenceEq,
        ← secondRawOccurrenceEq] using
        escapedFanSecondPrefixContactsAtHeads
    have firstRouteLength : 2 ≤ firstRoute.length := by
      simpa [firstRoute, scalePolyline] using firstLength
    have secondRouteLength : 2 ≤ secondRoute.length := by
      simpa [secondRoute, scalePolyline] using secondLength
    have firstRouteNodup : firstRoute.Nodup := by
      exact firstNodup.map
        (Cell.scale_injective
          (show
            (retainedAngularFanSourceClearanceFactor : Int) ≠ 0 by
            norm_num [retainedAngularFanSourceClearanceFactor]))
    have secondRouteNodup : secondRoute.Nodup := by
      exact secondNodup.map
        (Cell.scale_injective
          (show
            (retainedAngularFanSourceClearanceFactor : Int) ≠ 0 by
            norm_num [retainedAngularFanSourceClearanceFactor]))
    have firstRouteClassified :
        retainedTerminalDirectionClassify
            (routeTerminalVector firstRoute) =
          some firstTerminal := by
      simpa [firstRoute, firstTerminal] using
        routeTerminalVector_scale_classified
          retainedAngularFanSourceClearanceFactor_pos
          firstClassified
    have secondRouteClassified :
        retainedTerminalDirectionClassify
            (routeTerminalVector secondRoute) =
          some secondTerminal := by
      simpa [secondRoute, secondTerminal] using
        routeTerminalVector_scale_classified
          retainedAngularFanSourceClearanceFactor_pos
          secondClassified
    have scaledRoutesAvoid :
        RoutesAvoidEachOther firstRoute secondRoute := by
      simpa [firstRoute, secondRoute] using
        rawRoutesAvoid.scalePolyline
          (show
            (0 : Int) <
              retainedAngularFanSourceClearanceFactor by
            exact_mod_cast
              retainedAngularFanSourceClearanceFactor_pos)
    have firstRouteSingleton :
        firstRoute.dropLast.length = 1 := by
      simpa [firstRoute, scalePolyline] using
        firstSingletonPrefix
    simpa [firstRawRoute, secondRawRoute,
      firstRawTerminal, secondRawTerminal,
      firstSlot, secondSlot, firstRoute, secondRoute,
      firstTerminal, secondTerminal] using
      retainedAngularFanEscapedOrdinarySplicedBoundaryPolylines_avoid_of_first_singletonPrefix
        firstRoute secondRoute firstTerminal secondTerminal
        firstSlot secondSlot
        firstRouteLength secondRouteLength
        firstRouteNodup secondRouteNodup
        firstRouteClassified secondRouteClassified
        scaledRoutesAvoid firstRouteSingleton
        firstPrefixAvoidSecondFan
        escapedFanAvoidSecondPrefix'
        escapedFanSecondPrefixContactsAtHeads'
        (by
          simpa [firstRoute, secondRoute,
            firstTerminal, secondTerminal] using fansAvoid)
  · exfalso
    apply
      finalGaugedRouteOccurrence_prefix_length_ne_one_of_bend_witness
        formula firstWitness routeBend localClauseIndex
        firstSourceEq
    simpa [← firstRawOccurrenceEq] using firstSingletonPrefix

end PeriodicEightOccurrenceSplit
end LeanTrominoes
