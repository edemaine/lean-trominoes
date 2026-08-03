import LeanTrominoes.RetainedAngularFanFinalSourceRelativeRouteSeparation
import LeanTrominoes.RetainedAngularFanFinalRelativeDirectCycleSeparation
import LeanTrominoes.RetainedFinalSourceRouteOtherVertexFinalSegmentSeparation

/-!
# Final source routes avoid translated source vertices

The retained source drawing is periodically planar, but the earlier
source-vertex lemmas fixed the target variable in the stored fundamental
cell.  This file exposes the corresponding arbitrary-period statements.
They are the source-side input needed to separate fallback angular-fan
routes from translated implication-cycle neighborhoods.
-/

namespace LeanTrominoes
namespace PeriodicOrthocrossing

open PeriodicEightOccurrenceSplit
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxRecDepth 8192
set_option maxHeartbeats 4000000

/-- A genuine retained clause vertex cannot equal a periodically translated
occurring source-variable vertex. -/
theorem
    finalCoordinatedCanonicalClausePosition_ne_translatedSourceVariablePosition
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
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (targetAtom : WrappedPeriodicPlanarSATVariable Variable)
    (targetAtomMember :
      targetAtom ∈
        sourceVariables (finalCoordinatedSource formula).erase)
    (relativeTranslate : Cell) :
    PositionedPeriodicCNF.canonicalClausePosition
        (finalCoordinatedPlacement formula) clause ≠
      Cell.add
        ((finalCoordinatedPlacement formula).position targetAtom)
        ((finalCoordinatedPlacement formula).translation
          relativeTranslate) := by
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  rcases
      exists_positioned_members_of_mem_sourceVariables
        source targetAtomMember with
    ⟨targetClause, targetClauseIndex,
      targetLiteral, targetLiteralIndex,
      targetClauseMember, targetLiteralMember,
      targetAtomEqual⟩
  by_cases translateZero : relativeTranslate = (0, 0)
  · subst relativeTranslate
    have compatible :=
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing_isCompatible
        formula sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal retainedClausesNonempty
    have distinct :=
      @PositionedPeriodicCNF.canonicalClausePosition_ne_variablePosition_of_members
        (WrappedPeriodicPlanarSATVariable Variable)
        (fun first second =>
          @instDecidableEqWrappedPeriodicVariable
            (PeriodicPlanarSATVariable Variable)
            (fun firstOriginal secondOriginal =>
              @instDecidableEqPeriodicPlanarSATVariable
                Variable inferInstance
                firstOriginal secondOriginal)
            first second)
        source placement routes compatible
        clause targetClause clauseIndex targetClauseIndex
        clauseMember literal literalIndex literalMember
        targetClauseMember targetLiteral targetLiteralIndex
        targetLiteralMember
    simpa [source, placement, routes, targetAtomEqual,
      PeriodicVariablePlacement.translation,
      Cell.add, Cell.scale] using distinct
  · have clausePositionMember :
        PositionedPeriodicCNF.canonicalClausePosition
            placement clause ∈
          PositionedPeriodicCNF.incidenceVertexPositions
            source placement := by
      rw [PositionedPeriodicCNF.incidenceVertexPositions]
      exact List.mem_append.mpr <| Or.inr <|
        List.mem_map.mpr
          ⟨clause, List.fst_mem_of_mem_zipIdx clauseMember, rfl⟩
    have clauseBounds :=
      retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSAT_incidenceVertexPositions_inSquare
        formula sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal retainedClausesNonempty
        (PositionedPeriodicCNF.canonicalClausePosition
          placement clause)
        (by
          simpa [source, placement, finalCoordinatedSource,
            finalCoordinatedPlacement] using clausePositionMember)
    have targetBounds :=
      retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_position_inSquare
        formula targetAtom
    have periodPositive : 0 < placement.period := by
      simpa [placement, finalCoordinatedPlacement,
        retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement,
        wrappedDrawingPeriodicPlanarSATPlacement] using
        drawingPeriodicPlanarSATPlacement_period_pos formula
    exact
      LeanTrominoes.PeriodicOrthocrossing.PeriodicVariablePlacement.position_ne_add_translation_of_inSquare_of_nonzero
        placement
        periodPositive
        (by
          simpa [placement, finalCoordinatedPlacement,
            retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,
            wrappedDrawingPeriodicPlanarSATPlacement] using clauseBounds)
        (by
          simpa [placement, finalCoordinatedPlacement,
            retainedGaugedWrappedDrawingPeriodicPlanarSATPlacement_period,
            wrappedDrawingPeriodicPlanarSATPlacement] using targetBounds)
        relativeTranslate translateZero

/-- A genuine final source incidence's deleted-final-point prefix avoids a
periodically translated occurring source-variable position, provided that
position is not the incidence's own canonical endpoint. -/
theorem
    finalCoordinatedSourceRoutePrefix_avoids_translatedSourceVariablePosition
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
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (targetAtom : WrappedPeriodicPlanarSATVariable Variable)
    (targetAtomMember :
      targetAtom ∈
        sourceVariables (finalCoordinatedSource formula).erase)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal ≠
        Cell.add
          ((finalCoordinatedPlacement formula).position targetAtom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    (∀ point ∈
        (finalCoordinatedSourceRoutes
          formula clauseIndex literalIndex).dropLast,
        point ≠
          Cell.add
            ((finalCoordinatedPlacement formula).position targetAtom)
            ((finalCoordinatedPlacement formula).translation
              relativeTranslate)) ∧
      ∀ segment ∈
        gridPolylineSegments
          (finalCoordinatedSourceRoutes
            formula clauseIndex literalIndex).dropLast,
        segment.IsAxisAligned →
          ¬segment.Contains
            (Cell.add
              ((finalCoordinatedPlacement formula).position targetAtom)
              ((finalCoordinatedPlacement formula).translation
                relativeTranslate)) := by
  let source := finalCoordinatedSource formula
  let placement := finalCoordinatedPlacement formula
  let routes := finalCoordinatedSourceRoutes formula
  let currentRoute := routes clauseIndex literalIndex
  rcases
      exists_positioned_members_of_mem_sourceVariables
        source targetAtomMember with
    ⟨targetClause, targetClauseIndex,
      targetLiteral, targetLiteralIndex,
      targetClauseMember, targetLiteralMember,
      targetAtomEqual⟩
  let targetRoute :=
    routes targetClauseIndex targetLiteralIndex
  let targetShift :=
    Cell.sub relativeTranslate
      (incidenceRelativeOffset targetClause targetLiteral)
  let currentIncidence :
      CNFIncidence
        (WrappedPeriodicPlanarSATVariable Variable) :=
    ⟨clauseIndex, clause.literals, literalIndex, literal⟩
  let targetIncidence :
      CNFIncidence
        (WrappedPeriodicPlanarSATVariable Variable) :=
    ⟨targetClauseIndex, targetClause.literals,
      targetLiteralIndex, targetLiteral⟩
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes clauseMember literalMember with
    ⟨currentRouteIndex, currentIncidenceMember,
      _currentRouteMember⟩
  rcases
      PositionedPeriodicCNF.exists_taggedIncidenceRoute_of_positioned_members
        source placement routes
        targetClauseMember targetLiteralMember with
    ⟨targetRouteIndex, targetIncidenceMember,
      _targetRouteMember⟩
  have occurrencesDifferent :
      (currentRouteIndex, ((0, 0) : Cell)) ≠
        (targetRouteIndex, targetShift) := by
    intro occurrencesEqual
    have routeIndicesEqual :
        currentRouteIndex = targetRouteIndex :=
      congrArg Prod.fst occurrencesEqual
    have targetShiftZero : targetShift = (0, 0) :=
      (congrArg Prod.snd occurrencesEqual).symm
    have incidencesEqual :=
      tagged_eq_of_mem_zipIdx_of_snd_eq
        currentIncidenceMember targetIncidenceMember
        routeIndicesEqual
    have canonicalPositionsEqual :
        PositionedPeriodicCNF.canonicalLiteralPosition
            placement clause literal =
          PositionedPeriodicCNF.canonicalLiteralPosition
            placement targetClause targetLiteral := by
      have equal :=
        congrArg
          (fun tagged :
              CNFIncidence
                  (WrappedPeriodicPlanarSATVariable Variable) × Nat =>
            Cell.add
              (placement.position tagged.1.literal.atom)
              (placement.translation
                (Cell.sub tagged.1.literal.offset
                  (PeriodicCNF.clauseAnchor
                    tagged.1.clause))))
          incidencesEqual
      simpa [PositionedPeriodicCNF.canonicalLiteralPosition]
        using equal
    have relativeEqual :
        incidenceRelativeOffset targetClause targetLiteral =
          relativeTranslate := by
      rcases relativeEq :
          incidenceRelativeOffset targetClause targetLiteral with
        ⟨relativeX, relativeY⟩
      rcases relativeTranslate with
        ⟨translateX, translateY⟩
      simp only [targetShift, relativeEq,
        Cell.sub, Prod.mk.injEq] at targetShiftZero
      exact Prod.ext (by omega) (by omega)
    apply centersDifferent
    calc
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal =
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement targetClause targetLiteral := by
            simpa [placement] using canonicalPositionsEqual
      _ = Cell.add
          ((finalCoordinatedPlacement formula).position targetAtom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate) := by
        change
          Cell.add
              (placement.position targetLiteral.atom)
              (placement.translation
                (incidenceRelativeOffset
                  targetClause targetLiteral)) =
            Cell.add (placement.position targetAtom)
              (placement.translation relativeTranslate)
        rw [targetAtomEqual, relativeEqual]
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  let retainedClausesNonempty :=
    retainedDrawingPlanarSATFormula_clausesNonempty_of_source
      formula sourceClausesNonempty
  have relativeAvoid :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoutes_relativeAvoidEachOther
      formula sourceCertificate.graphWellFormed
      sourceCertificate.graphDegreeAtMostThree
      sourceCertificate.graphIsLocal retainedClausesNonempty
  have rawAvoid :
      RoutesAvoidEachOther currentRoute
        (targetRoute.map
          (Cell.add (placement.translation targetShift))) := by
    simpa [source, placement, routes,
      currentRoute, targetRoute,
      currentIncidence, targetIncidence,
      finalCoordinatedSourceRoutes,
      finalCoordinatedPlacement] using
      relativeAvoid
        (currentIncidence, currentRouteIndex)
        currentIncidenceMember
        (targetIncidence, targetRouteIndex)
        targetIncidenceMember targetShift occurrencesDifferent
  have currentNodup : currentRoute.Nodup := by
    simpa [currentRoute, routes,
      finalCoordinatedSourceRoutes] using
      (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceRoute_isSimple
        formula sourceCertificate.graphWellFormed
        sourceCertificate.graphDegreeAtMostThree
        sourceCertificate.graphIsLocal retainedClausesNonempty
        (clause, clauseIndex)
        (by simpa [source, finalCoordinatedSource]
          using clauseMember)
        (literal, literalIndex) literalMember).1
  have currentEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
  have targetEndpoints :=
    finalCoordinatedSourceRoutes_endpoints
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
      targetClauseMember targetLiteralMember
  have translatedTargetLast :
      (targetRoute.map
        (Cell.add
          (placement.translation targetShift))).getLast? =
        some
          (Cell.add (placement.position targetAtom)
            (placement.translation relativeTranslate)) := by
    rw [List.getLast?_map]
    have targetLast :
        targetRoute.getLast? =
          some
            (PositionedPeriodicCNF.canonicalLiteralPosition
              placement targetClause targetLiteral) := by
      simpa [targetRoute, routes, placement] using
        targetEndpoints.2
    rw [targetLast]
    apply congrArg some
    change
      Cell.add (placement.translation targetShift)
          (Cell.add
            (placement.position targetLiteral.atom)
            (placement.translation
              (incidenceRelativeOffset
                targetClause targetLiteral))) =
        Cell.add (placement.position targetAtom)
          (placement.translation relativeTranslate)
    rcases targetPositionEq : placement.position targetAtom with
      ⟨targetX, targetY⟩
    rcases relativeEq :
        incidenceRelativeOffset targetClause targetLiteral with
      ⟨relativeX, relativeY⟩
    rcases relativeTranslate with ⟨translateX, translateY⟩
    simp only [targetShift, relativeEq,
      PeriodicVariablePlacement.translation,
      Cell.sub, Cell.scale, Cell.add,
      targetAtomEqual, targetPositionEq, Prod.mk.injEq]
    constructor <;> ring
  have sourceNeTarget :=
    finalCoordinatedCanonicalClausePosition_ne_translatedSourceVariablePosition
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      targetAtom targetAtomMember relativeTranslate
  have prefixAvoid :=
    routePrefix_avoids_other_final_point_of_avoid
      rawAvoid currentNodup
      (by
        simpa [currentRoute, routes, placement] using
          currentEndpoints.1)
      translatedTargetLast
      (by simpa [placement] using sourceNeTarget)
  simpa [currentRoute, routes, placement] using prefixAvoid

/-- Relative vertex planarity applies to a segment of a stored route while
the vertex is moved to an arbitrary period cell and the route stays fixed. -/
theorem verticesAvoidRouteInteriors_of_route_segment_mem_relativeVertex
    (drawing : PeriodicGridDrawing)
    (verticesAvoid : drawing.VerticesAvoidRouteInteriors)
    {vertexPosition : Cell}
    (vertexMember : vertexPosition ∈ drawing.vertexPositions)
    {route : List Cell}
    {routeIndex : Nat}
    (routeMember :
      (route, routeIndex) ∈ drawing.edgeRoutes.zipIdx)
    {segment : GridSegment}
    (segmentMember : segment ∈ gridPolylineSegments route)
    (vertexTranslate : Cell) :
    ¬segment.InteriorContains
      (Cell.add vertexPosition
        (drawing.periodTranslation vertexTranslate)) := by
  rcases List.mem_iff_get.mp segmentMember with
    ⟨segmentIndex, segmentEqual⟩
  let indexedSegment : IndexedGridSegment :=
    ⟨routeIndex, segmentIndex,
      (gridPolylineSegments route).get segmentIndex⟩
  have indexedSegmentMember :
      indexedSegment ∈ drawing.indexedSegments :=
    PeriodicGridDrawing.indexedSegment_mem_of_route_mem
      routeMember segmentIndex
  have avoids :=
    verticesAvoid vertexPosition vertexMember
      indexedSegment indexedSegmentMember
      vertexTranslate (0, 0)
  have zeroTranslation :
      drawing.periodTranslation (0, 0) = (0, 0) := by
    simp [PeriodicGridDrawing.periodTranslation,
      Cell.scale]
  rw [zeroTranslation] at avoids
  have untranslatedAvoids :
      ¬indexedSegment.segment.InteriorContains
        (Cell.add vertexPosition
          (drawing.periodTranslation vertexTranslate)) := by
    simpa [GridSegment.translate, Cell.add] using avoids
  have indexedSegmentEqual :
      indexedSegment.segment = segment := segmentEqual
  rw [indexedSegmentEqual] at untranslatedAvoids
  exact untranslatedAvoids

/-- Any axis-aligned discarded final segment avoids every different
periodically translated occurring source-variable point. -/
theorem
    finalCoordinatedSourceRoute_finalSegment_avoids_translatedSourceVariablePosition_of_axisAligned
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
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (finalAligned :
      let route :=
        finalCoordinatedSourceRoutes formula clauseIndex literalIndex
      (⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ : GridSegment).IsAxisAligned)
    (targetAtom : WrappedPeriodicPlanarSATVariable Variable)
    (targetAtomMember :
      targetAtom ∈
        sourceVariables (finalCoordinatedSource formula).erase)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal ≠
        Cell.add
          ((finalCoordinatedPlacement formula).position targetAtom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    let route :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route, route.getLastD (0, 0)⟩
    finalSegment.IsAxisAligned ∧
      ¬finalSegment.Contains
        (Cell.add
          ((finalCoordinatedPlacement formula).position targetAtom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) := by
  dsimp only
  let placement := finalCoordinatedPlacement formula
  let drawing :=
    retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
      formula
  let route :=
    finalCoordinatedSourceRoutes formula clauseIndex literalIndex
  let finalSegment : GridSegment :=
    ⟨polylineLastEntrance route, route.getLastD (0, 0)⟩
  have routeLength : 2 ≤ route.length := by
    simpa [route] using
      finalCoordinatedSourceRoutes_length_ge_two
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  have finalSegmentMember :
      finalSegment ∈ gridPolylineSegments route := by
    simpa [route, finalSegment] using
      finalCoordinatedSourceRoute_finalSegment_mem
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember
  rcases finalCoordinatedSourceRoute_mem_namedDrawing
      formula clauseMember literalMember with
    ⟨routeIndex, routeMember⟩
  have targetDrawingPositionMember :
      placement.position targetAtom ∈ drawing.vertexPositions := by
    change
      (finalCoordinatedPlacement formula).position targetAtom ∈
        (retainedDeduplicatedGaugedWrappedDrawingPeriodicPlanarSATIncidenceDrawing
          formula).vertexPositions
    exact
      finalCoordinatedSourceVariablePosition_mem_namedVertexPositions
        formula targetAtom targetAtomMember
  let sourceCertificate :=
    retainedPlanarSATCertificate formula
      sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty
  have verticesAvoid : drawing.VerticesAvoidRouteInteriors := by
    simpa only [drawing] using
      sourceCertificate.drawingRibbonReady.1.1.2
  have avoidsInterior :
      ¬finalSegment.InteriorContains
        (Cell.add (placement.position targetAtom)
          (placement.translation relativeTranslate)) := by
    have relativeAvoid :=
      verticesAvoidRouteInteriors_of_route_segment_mem_relativeVertex
        drawing verticesAvoid targetDrawingPositionMember
        routeMember finalSegmentMember relativeTranslate
    rw [
      retainedDeduplicatedGaugedWrappedDrawing_periodTranslation_eq_placement]
      at relativeAvoid
    simpa [drawing, placement,
      finalCoordinatedPlacement] using relativeAvoid
  have prefixAvoid :=
    (finalCoordinatedSourceRoutePrefix_avoids_translatedSourceVariablePosition
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      targetAtom targetAtomMember relativeTranslate centersDifferent).1
  have reverseTailExists :
      ∃ entrance, route.reverse.tail.head? = some entrance :=
    exists_reverse_tail_head?_of_two_le_length route routeLength
  have entranceLast :
      route.dropLast.getLast? =
        some (polylineLastEntrance route) :=
    dropLast_getLast?_of_reverse_tail_head?
      (polylineLastEntrance_spec reverseTailExists)
  have entranceMember :
      polylineLastEntrance route ∈ route.dropLast :=
    mem_of_getLast?_eq_some entranceLast
  have startDifferent :
      finalSegment.start ≠
        Cell.add (placement.position targetAtom)
          (placement.translation relativeTranslate) := by
    have entranceAvoid :=
      prefixAvoid (polylineLastEntrance route)
        (by simpa only [route] using entranceMember)
    dsimp only [finalSegment]
    simpa only [route, placement] using entranceAvoid
  have routeFinal :
      route.getLast? =
        some
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement clause literal) := by
    simpa [route, placement] using
      (finalCoordinatedSourceRoutes_endpoints
        formula sourceLocal sourceWidth sourceOccurrences
        sourceClausesNonempty clauseMember literalMember).2
  have finalPointEq :
      route.getLastD (0, 0) =
        PositionedPeriodicCNF.canonicalLiteralPosition
          placement clause literal := by
    simp [List.getLastD_eq_getLast?, routeFinal]
  have finishDifferent :
      finalSegment.finish ≠
        Cell.add (placement.position targetAtom)
          (placement.translation relativeTranslate) := by
    dsimp only [finalSegment]
    rw [finalPointEq]
    simpa only [placement] using centersDifferent
  refine ⟨?_, ?_⟩
  · simpa [route, finalSegment] using finalAligned
  exact
    gridSegment_not_contains_of_avoidsInterior_and_endpoints
      avoidsInterior startDifferent finishDifferent

/-- A fallback route's discarded final segment is axis-aligned and avoids
every different periodically translated occurring source-variable point. -/
theorem
    finalCoordinatedFallbackSourceRoute_finalSegment_avoids_translatedSourceVariablePosition
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
        (finalCoordinatedSource formula).clauses.zipIdx)
    {literal :
      PeriodicLiteral
        (WrappedPeriodicPlanarSATVariable Variable)}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (choiceNone :
      retainedFinalDirectSourceRouteChoice?
          formula clauseIndex literalIndex = none)
    (targetAtom : WrappedPeriodicPlanarSATVariable Variable)
    (targetAtomMember :
      targetAtom ∈
        sourceVariables (finalCoordinatedSource formula).erase)
    (relativeTranslate : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          (finalCoordinatedPlacement formula) clause literal ≠
        Cell.add
          ((finalCoordinatedPlacement formula).position targetAtom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) :
    let route :=
      finalCoordinatedSourceRoutes formula clauseIndex literalIndex
    let finalSegment : GridSegment :=
      ⟨polylineLastEntrance route, route.getLastD (0, 0)⟩
    finalSegment.IsAxisAligned ∧
      ¬finalSegment.Contains
        (Cell.add
          ((finalCoordinatedPlacement formula).position targetAtom)
          ((finalCoordinatedPlacement formula).translation
            relativeTranslate)) := by
  apply
    finalCoordinatedSourceRoute_finalSegment_avoids_translatedSourceVariablePosition_of_axisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember
      _ targetAtom targetAtomMember relativeTranslate centersDifferent
  exact
    finalCoordinatedFallbackSourceRoute_finalSegment_isAxisAligned
      formula sourceLocal sourceWidth sourceOccurrences
      sourceClausesNonempty clauseMember literalMember choiceNone

end PeriodicOrthocrossing
end LeanTrominoes
