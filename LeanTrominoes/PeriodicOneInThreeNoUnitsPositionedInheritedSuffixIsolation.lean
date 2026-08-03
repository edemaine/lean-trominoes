import LeanTrominoes.PeriodicOneInThreeNoUnitsPositionedConnectorIsolation

/-!
# Endpoint isolation after unit-elimination head replacement

The transformed source tail already has an isolated final endpoint.  If the
source route continues beyond its first exit, connector exclusion extends
that certificate across the new prefix.  If it ends at the first exit,
endpoint isolation forces the source route to be one segment; the vertical
unit-clause case then reduces to the connector's own target certificate.
-/

namespace LeanTrominoes
namespace PeriodicOneInThreeNoUnitsPositioned

/-- Replacing the head of an isolated source route by the unit-elimination
connector preserves isolation of its final endpoint.  The only exceptional
shape is a one-segment source route, for which the first exit must be vertical
in the source clause's canonical gauge. -/
theorem inheritedRouteSuffix_lastNotInDropLast
    {Variable : Type*}
    (outputPlacement :
      PeriodicVariablePlacement (OneInThreeNoUnitVariable Variable))
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (sourceClause : PositionedPeriodicClause Variable)
    (generatedClause :
      PositionedPeriodicClause (OneInThreeNoUnitVariable Variable))
    (sourceLiteralIndex : Nat)
    (sourceLiteralIndexLt : sourceLiteralIndex < 3)
    (sourceRoute : List Cell)
    (sourceExit sourceLast : Cell)
    (sourceHead :
      sourceRoute.head? =
        some
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause))
    (sourceTailHead : sourceRoute.tail.head? = some sourceExit)
    (sourceLastLookup : sourceRoute.getLast? = some sourceLast)
    (sourceOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline sourceRoute)
    (sourceIsolation :
      AxisDirection.HeadNotInTail
          (AxisDirection.unitSubdividePolyline sourceRoute) ∧
        AxisDirection.LastNotInDropLast
          (AxisDirection.unitSubdividePolyline sourceRoute))
    (verticalIfLastIsExit :
      sourceLast = sourceExit →
        sourceExit.1 =
          (PositionedPeriodicCNF.canonicalClausePosition
            sourcePlacement sourceClause).1) :
    AxisDirection.LastNotInDropLast
      (AxisDirection.unitSubdividePolyline
        (inheritedRouteSuffix
          outputPlacement sourcePlacement sourceClause generatedClause
          sourceLiteralIndex sourceRoute)) := by
  let sourceClausePoint :=
    PositionedPeriodicCNF.canonicalClausePosition
      sourcePlacement sourceClause
  obtain ⟨sourceRest, rfl⟩ :
      ∃ sourceRest,
        sourceRoute = sourceClausePoint :: sourceExit :: sourceRest := by
    cases sourceRoute with
    | nil => simp at sourceHead
    | cons actualHead rest =>
        have actualHeadEqual : actualHead = sourceClausePoint := by
          simpa [sourceClausePoint] using sourceHead
        subst actualHead
        cases rest with
        | nil => simp at sourceTailHead
        | cons actualExit sourceRest =>
            have actualExitEqual : actualExit = sourceExit := by
              simpa using sourceTailHead
            subst actualExit
            exact ⟨sourceRest, rfl⟩
  let outputClausePoint :=
    normalizedSourceClausePosition
      outputPlacement sourceClause generatedClause
  let relativeExit := Cell.sub sourceExit sourceClausePoint
  let relativeLast := Cell.sub sourceLast sourceClausePoint
  let transformed :=
    inheritedSourceRoute
      outputPlacement sourcePlacement sourceClause generatedClause
      (sourceClausePoint :: sourceExit :: sourceRest)
  let transformedExit :=
    Cell.add outputClausePoint (Cell.scale gadgetScale relativeExit)
  let transformedLast :=
    Cell.add outputClausePoint (Cell.scale gadgetScale relativeLast)
  let port :=
    Cell.add outputClausePoint
      (PlanarOneInThreeNoUnits.sourceLocalPosition sourceLiteralIndex)
  let connector :=
    PositionedPeriodicCNF.orthogonalDetour port transformedExit
  have transformedTailHead :
      transformed.tail.head? = some transformedExit := by
    have mapped :=
      inheritedSourceRoute_tail_head?
        outputPlacement sourcePlacement sourceClause generatedClause
        (sourceClausePoint :: sourceExit :: sourceRest)
        sourceExit sourceTailHead
    rw [show transformedExit =
        Cell.add
          (inheritedSourceRouteShift
            outputPlacement sourcePlacement sourceClause generatedClause)
          (Cell.scale gadgetScale sourceExit) by
      apply Prod.ext <;>
        simp [transformedExit, outputClausePoint, relativeExit,
          sourceClausePoint, inheritedSourceRouteShift,
          Cell.add, Cell.sub, Cell.scale] <;>
        ring]
    exact mapped
  have firstExitEqual :
      polylineFirstExit transformed = transformedExit := by
    exact Option.some.inj
      ((polylineFirstExit_spec
        ⟨transformedExit, transformedTailHead⟩).symm.trans
          transformedTailHead)
  have transformedLastLookup :
      transformed.getLast? = some transformedLast := by
    have mapped :
        transformed.getLast? =
          some
            (Cell.add
              (inheritedSourceRouteShift
                outputPlacement sourcePlacement sourceClause generatedClause)
              (Cell.scale gadgetScale sourceLast)) := by
      unfold transformed inheritedSourceRoute
        PeriodicOrthocrossing.translatePolyline
      rw [List.getLast?_map, scalePolyline_getLast?, sourceLastLookup]
      rfl
    rw [show transformedLast =
        Cell.add
          (inheritedSourceRouteShift
            outputPlacement sourcePlacement sourceClause generatedClause)
          (Cell.scale gadgetScale sourceLast) by
      apply Prod.ext <;>
        simp [transformedLast, outputClausePoint, relativeLast,
          sourceClausePoint, inheritedSourceRouteShift,
          Cell.add, Cell.sub, Cell.scale] <;>
        ring]
    exact mapped
  have transformedOrthogonal :
      PeriodicOrthocrossing.OrthogonalPolyline transformed :=
    inheritedSourceRoute_orthogonal
      outputPlacement sourcePlacement sourceClause generatedClause
      (sourceClausePoint :: sourceExit :: sourceRest) sourceOrthogonal
  by_cases lastIsExit : sourceLast = sourceExit
  · have sourceRoutePair :
        sourceClausePoint :: sourceExit :: sourceRest =
          [sourceClausePoint, sourceExit] := by
      apply eq_pair_of_last_eq_firstExit
      · simpa [sourceClausePoint] using sourceHead
      · exact sourceTailHead
      · simpa [lastIsExit] using sourceLastLookup
      · exact sourceOrthogonal
      · exact sourceIsolation.2
    have relativeExitVertical : relativeExit.1 = 0 := by
      have vertical := verticalIfLastIsExit lastIsExit
      simp [relativeExit, sourceClausePoint, Cell.sub, vertical]
    have connectorFresh :
        AxisDirection.LastNotInDropLast
          (AxisDirection.unitSubdividePolyline connector) := by
      simpa [connector, port] using
        shiftedSourcePortDetour_lastNotInDropLast_of_vertical
          outputClausePoint sourceLiteralIndex sourceLiteralIndexLt
          relativeExit relativeExitVertical
    have transformedPair :
        transformed = [outputClausePoint, transformedExit] := by
      unfold transformed
      rw [sourceRoutePair]
      simp only [inheritedSourceRoute,
        PeriodicOrthocrossing.translatePolyline, scalePolyline,
        List.map_cons, List.map_nil]
      congr 1
      · apply Prod.ext <;>
          simp [outputClausePoint, sourceClausePoint,
            inheritedSourceRouteShift, Cell.add, Cell.sub,
            Cell.scale] <;>
          ring
      · congr 1
    rw [show
      inheritedRouteSuffix
          outputPlacement sourcePlacement sourceClause generatedClause
          sourceLiteralIndex
          (sourceClausePoint :: sourceExit :: sourceRest) = connector by
      change
        replacePolylineHead
            (PositionedPeriodicCNF.orthogonalDetour
              (normalizedSourcePort outputPlacement sourceClause
                generatedClause sourceLiteralIndex)
              (polylineFirstExit
                (inheritedSourceRoute outputPlacement sourcePlacement
                  sourceClause generatedClause
                  (sourceClausePoint :: sourceExit :: sourceRest))))
            (inheritedSourceRoute outputPlacement sourcePlacement
              sourceClause generatedClause
              (sourceClausePoint :: sourceExit :: sourceRest)) = connector
      rw [show
        inheritedSourceRoute outputPlacement sourcePlacement sourceClause
            generatedClause
            (sourceClausePoint :: sourceExit :: sourceRest) = transformed by
          rfl]
      rw [firstExitEqual, transformedPair]
      simp [connector, port, outputClausePoint, normalizedSourcePort,
        replacePolylineHead, joinAtEndpoint]]
    exact connectorFresh
  · have firstAligned :
        (GridSegment.mk (0, 0) relativeExit).IsAxisAligned := by
      have aligned := (List.isChain_cons_cons.mp sourceOrthogonal).1
      rcases sourceClausePoint with ⟨headX, headY⟩
      rcases sourceExit with ⟨exitX, exitY⟩
      simp [relativeExit, Cell.sub,
        GridSegment.IsAxisAligned, GridSegment.IsHorizontal,
        GridSegment.IsVertical] at aligned ⊢
      omega
    have relativeLastOutside :
        ¬(GridSegment.mk (0, 0) relativeExit).Contains relativeLast := by
      have outside :=
        firstSegment_not_contains_finalEndpoint
          (sourceRoute := sourceClausePoint :: sourceExit :: sourceRest)
          (sourceHead := sourceClausePoint)
          (sourceExit := sourceExit) (sourceLast := sourceLast)
          (by simpa [sourceClausePoint] using sourceHead)
          sourceTailHead sourceLastLookup lastIsExit
          sourceOrthogonal sourceIsolation.2
      intro relativeContains
      have translatedContains :=
        (PeriodicGridDrawing.contains_translate_iff
          (GridSegment.mk (0, 0) relativeExit)
          sourceClausePoint relativeLast).2 relativeContains
      apply outside
      simpa [GridSegment.translate, relativeExit, relativeLast,
        Cell.add, Cell.sub] using translatedContains
    have transformedLastNotInConnector :
        transformedLast ∉
          AxisDirection.unitSubdividePolyline connector := by
      simpa [transformedLast, connector, port] using
        shiftedScaledPoint_not_mem_sourcePortDetour
          outputClausePoint sourceLiteralIndex sourceLiteralIndexLt
          relativeExit relativeLast firstAligned relativeLastOutside
    have transformedTailLast :
        transformed.tail.getLast? = some transformedLast :=
      List.getLast?_tail_eq_getLast?
        transformedTailHead transformedLastLookup
    have sourceTailLength :
        2 ≤ (sourceExit :: sourceRest).length := by
      cases sourceRest with
      | nil =>
          have exitEqualLast : sourceExit = sourceLast := by
            simpa using sourceLastLookup
          exact (lastIsExit exitEqualLast.symm).elim
      | cons second tail => simp
    have sourceTailOrthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline
          (sourceExit :: sourceRest) :=
      sourceOrthogonal.tail
    have sourceTailFresh :
        AxisDirection.LastNotInDropLast
          (AxisDirection.unitSubdividePolyline
            (sourceExit :: sourceRest)) := by
      let first : List Cell := [sourceClausePoint, sourceExit]
      let second : List Cell := sourceExit :: sourceRest
      have firstLast : first.getLast? = some sourceExit := by
        simp [first]
      have secondHead : second.head? = some sourceExit := by
        simp [second]
      have split :=
        AxisDirection.unitSubdividePolyline_joinAtEndpoint
          (first := first) (second := second)
          (firstNonempty := by simp [first])
          (firstLast := firstLast) (secondHead := secondHead)
      have joinedFresh :
          AxisDirection.LastNotInDropLast
            (joinAtEndpoint
              (AxisDirection.unitSubdividePolyline first)
              (AxisDirection.unitSubdividePolyline second)) := by
        rw [← split]
        simpa [first, second, joinAtEndpoint] using sourceIsolation.2
      have firstOrthogonal :
          PeriodicOrthocrossing.OrthogonalPolyline first := by
        simpa [first,
          PeriodicOrthocrossing.OrthogonalPolyline] using
          (List.isChain_cons_cons.mp sourceOrthogonal).1
      have firstSubdividedLast :
          (AxisDirection.unitSubdividePolyline first).getLast? =
            some sourceExit := by
        rw [AxisDirection.unitSubdividePolyline_getLast?
          (by simp [first]) firstOrthogonal, firstLast]
      have secondSubdividedHead :
          (AxisDirection.unitSubdividePolyline second).head? =
            some sourceExit := by
        rw [AxisDirection.unitSubdividePolyline_head?
          (by simp [second]), secondHead]
      have secondSubdividedLength :
          2 ≤
            (AxisDirection.unitSubdividePolyline second).length :=
        AxisDirection.unitSubdividePolyline_length_ge_two_of_length_ge_two
          (by simpa [second] using sourceTailLength)
          (by simpa [second] using sourceTailOrthogonal)
      simpa [second] using
        joinedFresh.of_joinAtEndpoint_right
          firstSubdividedLast secondSubdividedHead
          secondSubdividedLength
    have transformedTailOrthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline transformed.tail := by
      simpa [transformed, inheritedSourceRoute,
        PeriodicOrthocrossing.translatePolyline, scalePolyline] using
        inheritedSourceRoute_orthogonal
          outputPlacement sourcePlacement sourceClause generatedClause
          (sourceExit :: sourceRest) sourceTailOrthogonal
    have transformedTailFresh :
        AxisDirection.LastNotInDropLast
          (AxisDirection.unitSubdividePolyline transformed.tail) := by
      have scaled :=
        sourceTailFresh.unitSubdividePolyline_scalePolyline
          (factor := 6) (by decide) sourceTailOrthogonal
      have translated :=
        scaled.unitSubdividePolyline_map_add
          (inheritedSourceRouteShift
            outputPlacement sourcePlacement sourceClause generatedClause)
      simpa [transformed, inheritedSourceRoute,
        PeriodicOrthocrossing.translatePolyline, scalePolyline,
        gadgetScale] using translated
    have transformedExitNeLast : transformedExit ≠ transformedLast := by
      intro equal
      have scaledEqual :
          Cell.scale gadgetScale relativeExit =
            Cell.scale gadgetScale relativeLast :=
        Cell.add_left_injective outputClausePoint equal
      have relativeEqual : relativeExit = relativeLast := by
        apply Cell.scale_injective
          (factor := gadgetScale) (by decide)
        exact scaledEqual
      apply lastIsExit
      rcases sourceClausePoint with ⟨headX, headY⟩
      rcases sourceExit with ⟨exitX, exitY⟩
      rcases sourceLast with ⟨lastX, lastY⟩
      simpa [relativeExit, relativeLast, Cell.sub] using relativeEqual.symm
    have transformedTailLength : 2 ≤ transformed.tail.length := by
      simpa [transformed, inheritedSourceRoute,
        PeriodicOrthocrossing.translatePolyline, scalePolyline] using
        sourceTailLength
    have connectorOrthogonal :
        PeriodicOrthocrossing.OrthogonalPolyline connector :=
      PositionedPeriodicCNF.orthogonalDetour_orthogonal
        port transformedExit
    have joined :=
      AxisDirection.LastNotInDropLast.unitSubdividePolyline_joinAtEndpoint
        transformedTailFresh
        (by simp [connector,
          PositionedPeriodicCNF.orthogonalDetour])
        transformedTailLength connectorOrthogonal transformedTailOrthogonal
        (by simp [connector]) transformedTailHead transformedTailLast
        transformedLastNotInConnector
    simpa [inheritedRouteSuffix, transformed, firstExitEqual,
      connector, port, normalizedSourcePort,
      replacePolylineHead] using joined

end PeriodicOneInThreeNoUnitsPositioned
end LeanTrominoes
