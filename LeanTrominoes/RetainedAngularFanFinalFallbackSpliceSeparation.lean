/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.RetainedAngularFanFallbackPrefixLengths
import LeanTrominoes.RetainedAngularFanEqualityLensSingletonSpokeSeparation
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
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

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
    let firstSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement order
          (clause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral clauseIndex firstLiteralIndex)
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement order
          (clause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral clauseIndex secondLiteralIndex)
    RoutesAvoidEachOther
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot)
        (retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) ∧
      RoutesMeetOnlyAtHeads
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot)
        (retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot) ∧
      PeriodicOrthocrossing.OrthogonalPolyline
        (retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) ∧
      RoutesStrictlyAvoidEachOther
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot)
        secondSuffix ∧
      RoutesStrictlyAvoidEachOther
        firstSuffix
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
  let firstSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        (clause.scale retainedAngularFanSourceClearanceFactor)
        firstLiteral clauseIndex firstLiteralIndex)
  let secondSuffix :=
    scalePolyline retainedTerminalFanRoutingRefinement
      (angularOccurrenceSuffix placement order
        (clause.scale retainedAngularFanSourceClearanceFactor)
        secondLiteral clauseIndex secondLiteralIndex)
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
    have firstRawOrthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline
          firstRawRoute := by
      rw [PeriodicOrthocrossing.orthogonalPolyline_iff_segments]
      intro segment segmentMember
      apply firstWitness.routeSegments_axisAligned_of_carrier
        wellFormed degree isLocal
        link localClauseIndex firstSourceEq
      rw [← firstRawOccurrenceEq]
      exact segmentMember
    have secondRawOrthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline
          secondRawRoute := by
      rw [PeriodicOrthocrossing.orthogonalPolyline_iff_segments]
      intro segment segmentMember
      apply secondWitness.routeSegments_axisAligned_of_carrier
        wellFormed degree isLocal
        link localClauseIndex secondSourceEq
      rw [← secondRawOccurrenceEq]
      exact segmentMember
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
    have shiftsEq :
        firstWitness.physicalShift =
          secondWitness.physicalShift := by
      unfold FinalGaugedRouteOccurrenceWitness.physicalShift
      rw [metadataEq]
    let normalizedLink :=
      firstWitness.anchorNormalizedCarrierLink link
    have firstNormalizedRouteEq :
        firstRawRoute =
          (drawingPlanarSATCarrierLensIncidenceDrawing
            formula normalizedLink).routes
              localClauseIndex firstLiteralIndex := by
      rw [firstRawOccurrenceEq]
      simpa [normalizedLink] using
        firstWitness.route_eq_anchorNormalizedCarrierLink
          link localClauseIndex firstSourceEq
    have secondNormalizedRouteEq :
        secondRawRoute =
          (drawingPlanarSATCarrierLensIncidenceDrawing
            formula normalizedLink).routes
              localClauseIndex secondLiteralIndex := by
      rw [secondRawOccurrenceEq]
      simpa [normalizedLink,
        FinalGaugedRouteOccurrenceWitness.anchorNormalizedCarrierLink,
        ← shiftsEq] using
          secondWitness.route_eq_anchorNormalizedCarrierLink
            link localClauseIndex secondSourceEq
    have normalizedLinkMember :
        normalizedLink ∈
          retainedDrawingCompleteCarrierLinksRaw
            formula.incidenceGraph := by
      simpa [normalizedLink] using
        firstWitness.anchorNormalizedCarrierLink_mem_raw
          wellFormed degree isLocal
          link localClauseIndex firstSourceEq
    have normalizedGeometry :
        EqualityLink.LensGeometry
          (CarrierNode.position formula.incidenceGraph)
          normalizedLink :=
      retainedDrawingCompleteCarrierLinkRaw_lensGeometry
        wellFormed degree isLocal normalizedLinkMember
    have firstLastD :
        firstRawRoute.getLastD (0, 0) =
          PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause firstLiteral := by
      rw [List.getLastD_eq_getLast?]
      change
        (finalCoordinatedSourceRoutes
          formula clauseIndex firstLiteralIndex).getLast?.getD (0, 0) = _
      rw [firstEndpoints.2]
      rfl
    have secondLastD :
        secondRawRoute.getLastD (0, 0) =
          PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause secondLiteral := by
      rw [List.getLastD_eq_getLast?]
      change
        (finalCoordinatedSourceRoutes
          formula clauseIndex secondLiteralIndex).getLast?.getD (0, 0) = _
      rw [secondEndpoints.2]
      rfl
    have firstSuffixCenterEq :
        Cell.scale
            (retainedTerminalFanRoutingRefinement *
              PeriodicEightOccurrenceSplitPositioned.refinementScale)
            (PositionedPeriodicCNF.canonicalLiteralPosition
              placement
              (clause.scale retainedAngularFanSourceClearanceFactor)
              firstLiteral) =
          Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            (firstRawRoute.getLastD (0, 0)) := by
      dsimp only [placement]
      rw [
        PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale,
        ← firstLastD, Cell.scale_scale]
      norm_num [retainedTerminalFanTotalRefinement_eq,
        retainedTerminalFanRoutingRefinement,
        retainedAngularFanSourceClearanceFactor,
        PeriodicEightOccurrenceSplitPositioned.refinementScale]
    have secondSuffixCenterEq :
        Cell.scale
            (retainedTerminalFanRoutingRefinement *
              PeriodicEightOccurrenceSplitPositioned.refinementScale)
            (PositionedPeriodicCNF.canonicalLiteralPosition
              placement
              (clause.scale retainedAngularFanSourceClearanceFactor)
              secondLiteral) =
          Cell.scale
            (retainedTerminalFanTotalRefinement *
              retainedAngularFanSourceClearanceFactor)
            (secondRawRoute.getLastD (0, 0)) := by
      dsimp only [placement]
      rw [
        PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale,
        ← secondLastD, Cell.scale_scale]
      norm_num [retainedTerminalFanTotalRefinement_eq,
        retainedTerminalFanRoutingRefinement,
        retainedAngularFanSourceClearanceFactor,
        PeriodicEightOccurrenceSplitPositioned.refinementScale]
    have firstSuffixBounded :
        ∀ point ∈ firstSuffix,
          InClosedGridRectangle
            (coordinateRadiusLower 96
              (Cell.scale
                (retainedTerminalFanTotalRefinement *
                  retainedAngularFanSourceClearanceFactor)
                (firstRawRoute.getLastD (0, 0))))
            (coordinateRadiusUpper 96
              (Cell.scale
                (retainedTerminalFanTotalRefinement *
                  retainedAngularFanSourceClearanceFactor)
                (firstRawRoute.getLastD (0, 0))))
            point := by
      intro point pointMember
      change
        point ∈
          scalePolyline retainedTerminalFanRoutingRefinement
            (angularOccurrenceSuffix placement order
              (clause.scale retainedAngularFanSourceClearanceFactor)
              firstLiteral clauseIndex firstLiteralIndex)
        at pointMember
      have bounded :=
        scaledAngularOccurrenceSuffix_point_in_centerRectangle
          placement order
          (clause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral clauseIndex firstLiteralIndex
          pointMember
      rw [firstSuffixCenterEq] at bounded
      exact bounded
    have secondSuffixBounded :
        ∀ point ∈ secondSuffix,
          InClosedGridRectangle
            (coordinateRadiusLower 96
              (Cell.scale
                (retainedTerminalFanTotalRefinement *
                  retainedAngularFanSourceClearanceFactor)
                (secondRawRoute.getLastD (0, 0))))
            (coordinateRadiusUpper 96
              (Cell.scale
                (retainedTerminalFanTotalRefinement *
                  retainedAngularFanSourceClearanceFactor)
                (secondRawRoute.getLastD (0, 0))))
            point := by
      intro point pointMember
      change
        point ∈
          scalePolyline retainedTerminalFanRoutingRefinement
            (angularOccurrenceSuffix placement order
              (clause.scale retainedAngularFanSourceClearanceFactor)
              secondLiteral clauseIndex secondLiteralIndex)
        at pointMember
      have bounded :=
        scaledAngularOccurrenceSuffix_point_in_centerRectangle
          placement order
          (clause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral clauseIndex secondLiteralIndex
          pointMember
      rw [secondSuffixCenterEq] at bounded
      exact bounded
    have crossSuffixesAvoid :
        RoutesStrictlyAvoidEachOther
            (retainedAngularFanEscapedSplicedBoundaryPolyline
              firstRoute firstTerminal firstSlot)
            secondSuffix ∧
          RoutesStrictlyAvoidEachOther
            firstSuffix
            (retainedAngularFanSplicedBoundaryPolyline
              secondRoute secondTerminal secondSlot) := by
      have localSeparated :=
        drawingPlanarSATCarrierLensIncidenceDrawing_singletonSplices_crossSuffixes_strictlyAvoid
          formula normalizedLink normalizedGeometry
          localClauseIndex firstLiteralIndex secondLiteralIndex
          indicesDifferent secondLiteralIndexLt
          firstRawTerminal secondRawTerminal firstSlot secondSlot
          (by simpa [← firstNormalizedRouteEq] using firstLength)
          (by simpa [← secondNormalizedRouteEq] using secondLength)
          (by simpa [← firstNormalizedRouteEq] using firstClassified)
          (by simpa [← secondNormalizedRouteEq] using secondClassified)
          firstEscapeFits
          (by
            simpa [← firstNormalizedRouteEq] using
              firstSingletonPrefix)
          firstSuffix secondSuffix
          (by
            simpa [← firstNormalizedRouteEq] using
              firstSuffixBounded)
          (by
            simpa [← secondNormalizedRouteEq] using
              secondSuffixBounded)
      simpa [firstRoute, secondRoute,
        firstTerminal, secondTerminal,
        ← firstNormalizedRouteEq,
        ← secondNormalizedRouteEq] using localSeparated
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
    have separated :=
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
    have firstRouteOrthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline firstRoute := by
      exact
        PeriodicOrthocrossing.OrthogonalPolyline.scalePolyline
          firstRawOrthogonal
          retainedAngularFanSourceClearanceFactor_pos
    have secondRouteOrthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline secondRoute := by
      exact
        PeriodicOrthocrossing.OrthogonalPolyline.scalePolyline
          secondRawOrthogonal
          retainedAngularFanSourceClearanceFactor_pos
    have firstSpliceOrthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline
          (retainedAngularFanEscapedSplicedBoundaryPolyline
            firstRoute firstTerminal firstSlot) :=
      retainedAngularFanEscapedSplicedBoundaryPolyline_orthogonal
        firstRoute firstTerminal firstSlot
        firstRouteLength firstRouteClassified
        firstRouteOrthogonal firstEscapeFits
    have secondSpliceOrthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline
          (retainedAngularFanSplicedBoundaryPolyline
            secondRoute secondTerminal secondSlot) :=
      retainedAngularFanSplicedBoundaryPolyline_orthogonal
        secondRoute secondTerminal secondSlot
        secondRouteLength secondRouteClassified
        secondRouteOrthogonal
    simpa [firstRawRoute, secondRawRoute,
      firstRawTerminal, secondRawTerminal,
      firstSlot, secondSlot, firstRoute, secondRoute,
      firstTerminal, secondTerminal,
      source, placement, routes, order,
      firstSuffix, secondSuffix] using
      ⟨separated.1, separated.2,
        firstSpliceOrthogonal, secondSpliceOrthogonal,
        crossSuffixesAvoid.1, crossSuffixesAvoid.2⟩
  · exfalso
    apply
      finalGaugedRouteOccurrence_prefix_length_ne_one_of_bend_witness
        formula firstWitness routeBend localClauseIndex
        firstSourceEq
    simpa [← firstRawOccurrenceEq] using firstSingletonPrefix

/-- The same exceptional pair is separated after retained rasterization.
Carrier fallback routes and both fan replacements are already orthogonal,
so the retained rasterizer is literally the identity in this branch. -/
theorem
    retainedFinalSameClauseEscapedOrdinarySplicedBoundaryRoutes_separated
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
    let firstSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement order
          (clause.scale retainedAngularFanSourceClearanceFactor)
          firstLiteral clauseIndex firstLiteralIndex)
    let secondSuffix :=
      scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix placement order
          (clause.scale retainedAngularFanSourceClearanceFactor)
          secondLiteral clauseIndex secondLiteralIndex)
    RoutesAvoidEachOther
        (retainedAngularFanEscapedSplicedBoundaryRoute
          firstRoute firstTerminal firstSlot)
        (retainedAngularFanSplicedBoundaryRoute
          secondRoute secondTerminal secondSlot) ∧
      RoutesMeetOnlyAtHeads
        (retainedAngularFanEscapedSplicedBoundaryRoute
          firstRoute firstTerminal firstSlot)
        (retainedAngularFanSplicedBoundaryRoute
          secondRoute secondTerminal secondSlot) ∧
      RoutesStrictlyAvoidEachOther
        (retainedAngularFanEscapedSplicedBoundaryRoute
          firstRoute firstTerminal firstSlot)
        secondSuffix ∧
      RoutesStrictlyAvoidEachOther
        firstSuffix
        (retainedAngularFanSplicedBoundaryRoute
          secondRoute secondTerminal secondSlot) := by
  dsimp only
  rcases
      retainedFinalSameClauseEscapedOrdinarySplicedBoundaryPolylines_separated
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember
        firstLiteralMember secondLiteralMember indicesDifferent
        firstChoiceNone firstSingletonPrefix with
    ⟨avoid, contactsAtHeads,
      firstOrthogonal, secondOrthogonal,
      firstCrossSuffix, secondCrossSuffix⟩
  rw [retainedAngularFanEscapedSplicedBoundaryRoute,
    rasterizeRetainedPolyline_eq_of_orthogonal firstOrthogonal,
    retainedAngularFanSplicedBoundaryRoute,
    rasterizeRetainedPolyline_eq_of_orthogonal secondOrthogonal]
  exact
    ⟨avoid, contactsAtHeads,
      firstCrossSuffix, secondCrossSuffix⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
