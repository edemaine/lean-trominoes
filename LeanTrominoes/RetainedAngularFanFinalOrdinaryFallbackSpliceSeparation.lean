import LeanTrominoes.RetainedAngularFanFallbackPrefixLengths
import LeanTrominoes.RetainedAngularFanFinalCoordinatedRouteValidity
import LeanTrominoes.RetainedAngularFanFinalFallbackOrthogonality
import LeanTrominoes.RetainedAngularFanFinalOccurrenceSuffixSeparation
import LeanTrominoes.RetainedFinalOuterFanSeparation
import LeanTrominoes.RetainedFinalSourceScaledSpliceSeparation
import LeanTrominoes.PositionedPeriodicCNFRetainedRayRasterization

/-!
# Ordinary final fallback splice separation

When the final direct-source selector fails on a clause, all of its genuine
routes come from one carrier lens or bend corner.  If two such routes have
non-singleton source prefixes, inherited source planarity separates their
ordinary angular-fan splices away from the common clause head.  Orthogonality
then transports the same certificate through retained rasterization.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicOrthocrossing
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

/-- Two non-singleton ordinary fallback splices selected from different
literals of one final clause avoid each other except for their common
clause head.  Both splices are orthogonal. -/
theorem
    retainedFinalSameClauseOrdinarySplicedBoundaryPolylines_separated_of_choice_none_of_prefix_lengths_ne_one
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
    (firstPrefixLengthNeOne :
      (finalCoordinatedSourceRoutes
        formula clauseIndex firstLiteralIndex).dropLast.length ≠ 1)
    (secondPrefixLengthNeOne :
      (finalCoordinatedSourceRoutes
        formula clauseIndex secondLiteralIndex).dropLast.length ≠ 1) :
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
        (retainedAngularFanSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot)
        (retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) ∧
      RoutesMeetOnlyAtHeads
        (retainedAngularFanSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot)
        (retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) ∧
      OrthogonalPolyline
        (retainedAngularFanSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot) ∧
      OrthogonalPolyline
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
    exact
      finalCoordinatedSourceRoutes_eq_finalGaugedRouteOccurrence_zero
        formula clauseIndex firstLiteralIndex
  have secondRawOccurrenceEq :
      secondRawRoute =
        finalGaugedRouteOccurrence
          formula clauseIndex secondLiteralIndex (0, 0) := by
    exact
      finalCoordinatedSourceRoutes_eq_finalGaugedRouteOccurrence_zero
        formula clauseIndex secondLiteralIndex
  rcases
      exists_sameMetadata_carrier_or_bend_witnesses_of_sameClause_choice_none
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember
        firstLiteralMember secondLiteralMember
        firstChoiceNone with
    ⟨firstWitness, secondWitness, metadataEq, sourceCases⟩
  have secondSourceCases :
      (∃ link localClauseIndex,
          secondWitness.metadata.source =
            .carrier link localClauseIndex) ∨
        (∃ routeBend localClauseIndex,
          secondWitness.metadata.source =
            .bend routeBend localClauseIndex) := by
    rw [← metadataEq]
    exact sourceCases
  have firstRawOrthogonal :
      OrthogonalPolyline firstRawRoute := by
    rw [firstRawOccurrenceEq]
    exact
      firstWitness.routeOrthogonal_of_carrier_or_bend
        wellFormed degree isLocal sourceCases
  have secondRawOrthogonal :
      OrthogonalPolyline secondRawRoute := by
    rw [secondRawOccurrenceEq]
    exact
      secondWitness.routeOrthogonal_of_carrier_or_bend
        wellFormed degree isLocal secondSourceCases
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
        firstIncidenceMember secondIncidenceMember indicesEqual
    exact indicesDifferent
      (congrArg
        (fun tagged :
            CNFIncidence
                (WrappedPeriodicPlanarSATVariable Variable) × Nat =>
          tagged.1.literalIndex)
        taggedEqual)
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
  have firstAligned :
      (⟨polylineLastEntrance firstRawRoute,
          firstRawRoute.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned := by
    exact
      (orthogonalPolyline_iff_segments firstRawRoute).mp
        firstRawOrthogonal
        (⟨polylineLastEntrance firstRawRoute,
          firstRawRoute.getLastD (0, 0)⟩ : GridSegment)
        (finalGridSegment_mem firstRawRoute firstLength)
  have secondAligned :
      (⟨polylineLastEntrance secondRawRoute,
          secondRawRoute.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned := by
    exact
      (orthogonalPolyline_iff_segments secondRawRoute).mp
        secondRawOrthogonal
        (⟨polylineLastEntrance secondRawRoute,
          secondRawRoute.getLastD (0, 0)⟩ : GridSegment)
        (finalGridSegment_mem secondRawRoute secondLength)
  have fansAvoid :
      RoutesStrictlyAvoidEachOther
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline retainedAngularFanSourceClearanceFactor
              firstRawRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor firstRawTerminal)
          firstSlot)
        (retainedTerminalFanOuterCompleteRoute
          (Cell.scale retainedTerminalFanTotalRefinement
            ((scalePolyline retainedAngularFanSourceClearanceFactor
              secondRawRoute).getLastD (0, 0)))
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor secondRawTerminal)
          secondSlot) := by
    apply
      retainedFinalOuterCompleteRoutes_strictlyAvoid_of_axisAligned_of_not_both_singletonPrefixes
        formula wellFormed degree isLocal retainedClausesNonempty
        retainedAngularFanSourceClearanceFactor_pos
        (by native_decide)
        firstRawRouteMember secondRawRouteMember
        firstLength secondLength routeIndicesDifferent
        firstEndpoints.1 secondEndpoints.1
        firstEndpoints.2 secondEndpoints.2
        firstSourceNeSecondCenter secondSourceNeFirstCenter
        centersDifferent
        (by
          rintro ⟨firstSingleton, secondSingleton⟩
          exact firstPrefixLengthNeOne firstSingleton)
        firstAligned secondAligned
        firstRawTerminal secondRawTerminal firstSlot secondSlot
        firstClassified secondClassified
  have firstAlignedAtCenter :
      (⟨polylineLastEntrance firstRawRoute,
          PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause firstLiteral⟩ :
        GridSegment).IsAxisAligned := by
    rw [← firstLastD]
    exact firstAligned
  have secondAlignedAtCenter :
      (⟨polylineLastEntrance secondRawRoute,
          PositionedPeriodicCNF.canonicalLiteralPosition
            (finalCoordinatedPlacement formula)
            clause secondLiteral⟩ :
        GridSegment).IsAxisAligned := by
    rw [← secondLastD]
    exact secondAligned
  have separated :=
    retainedFinalSourceScaledSplicedBoundaryPolylines_separated_of_axisAligned_of_prefix_lengths_ne_one
      formula wellFormed degree isLocal retainedClausesNonempty
      (by
        norm_num [retainedAngularFanSourceClearanceFactor])
      firstRawRouteMember secondRawRouteMember
      firstLength secondLength routeIndicesDifferent
      firstEndpoints.1 secondEndpoints.1
      firstEndpoints.2 secondEndpoints.2
      firstSourceNeSecondCenter secondSourceNeFirstCenter
      firstPrefixLengthNeOne secondPrefixLengthNeOne
      firstAlignedAtCenter secondAlignedAtCenter
      firstRawTerminal secondRawTerminal firstSlot secondSlot
      firstClassified secondClassified fansAvoid
  have firstRouteLength : 2 ≤ firstRoute.length := by
    simpa [firstRoute, scalePolyline] using firstLength
  have secondRouteLength : 2 ≤ secondRoute.length := by
    simpa [secondRoute, scalePolyline] using secondLength
  have firstRouteClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstRoute) =
        some firstTerminal := by
    simpa [firstRoute, firstTerminal] using
      routeTerminalVector_scale_classified
        retainedAngularFanSourceClearanceFactor_pos firstClassified
  have secondRouteClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector secondRoute) =
        some secondTerminal := by
    simpa [secondRoute, secondTerminal] using
      routeTerminalVector_scale_classified
        retainedAngularFanSourceClearanceFactor_pos secondClassified
  have firstRouteOrthogonal :
      OrthogonalPolyline firstRoute :=
    firstRawOrthogonal.scalePolyline
      retainedAngularFanSourceClearanceFactor_pos
  have secondRouteOrthogonal :
      OrthogonalPolyline secondRoute :=
    secondRawOrthogonal.scalePolyline
      retainedAngularFanSourceClearanceFactor_pos
  have firstSpliceOrthogonal :
      OrthogonalPolyline
        (retainedAngularFanSplicedBoundaryPolyline
          firstRoute firstTerminal firstSlot) :=
    retainedAngularFanSplicedBoundaryPolyline_orthogonal
      firstRoute firstTerminal firstSlot
      firstRouteLength firstRouteClassified firstRouteOrthogonal
  have secondSpliceOrthogonal :
      OrthogonalPolyline
        (retainedAngularFanSplicedBoundaryPolyline
          secondRoute secondTerminal secondSlot) :=
    retainedAngularFanSplicedBoundaryPolyline_orthogonal
      secondRoute secondTerminal secondSlot
      secondRouteLength secondRouteClassified secondRouteOrthogonal
  simpa [firstRawRoute, secondRawRoute,
    firstRawTerminal, secondRawTerminal,
    firstSlot, secondSlot, firstRoute, secondRoute,
    firstTerminal, secondTerminal] using
      ⟨separated.1, separated.2,
        firstSpliceOrthogonal, secondSpliceOrthogonal⟩

/-- The same non-singleton ordinary fallback pair remains head-only
separated after retained rasterization. -/
theorem
    retainedFinalSameClauseOrdinarySplicedBoundaryRoutes_separated_of_choice_none_of_prefix_lengths_ne_one
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
    (firstPrefixLengthNeOne :
      (finalCoordinatedSourceRoutes
        formula clauseIndex firstLiteralIndex).dropLast.length ≠ 1)
    (secondPrefixLengthNeOne :
      (finalCoordinatedSourceRoutes
        formula clauseIndex secondLiteralIndex).dropLast.length ≠ 1) :
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
        (retainedAngularFanSplicedBoundaryRoute
          firstRoute firstTerminal firstSlot)
        (retainedAngularFanSplicedBoundaryRoute
          secondRoute secondTerminal secondSlot) ∧
      RoutesMeetOnlyAtHeads
        (retainedAngularFanSplicedBoundaryRoute
          firstRoute firstTerminal firstSlot)
        (retainedAngularFanSplicedBoundaryRoute
          secondRoute secondTerminal secondSlot) := by
  dsimp only
  rcases
      retainedFinalSameClauseOrdinarySplicedBoundaryPolylines_separated_of_choice_none_of_prefix_lengths_ne_one
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember
        firstLiteralMember secondLiteralMember indicesDifferent
        firstChoiceNone firstPrefixLengthNeOne
        secondPrefixLengthNeOne with
    ⟨avoid, contactsAtHeads,
      firstOrthogonal, secondOrthogonal⟩
  rw [retainedAngularFanSplicedBoundaryRoute,
    rasterizeRetainedPolyline_eq_of_orthogonal firstOrthogonal,
    retainedAngularFanSplicedBoundaryRoute,
    rasterizeRetainedPolyline_eq_of_orthogonal secondOrthogonal]
  exact ⟨avoid, contactsAtHeads⟩

end PeriodicEightOccurrenceSplit
end LeanTrominoes
