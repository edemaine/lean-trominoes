import LeanTrominoes.PeriodicEightOccurrenceSplitPositionedRouteRadiusBounds
import LeanTrominoes.PositionedPeriodicCNFRebasedRouteRadiusScaling
import LeanTrominoes.RetainedAngularFanSourceSpliceExpandedBounds

/-!
# Variable-centered radius bounds for retained angular-fan splices

The source-first fixed-eight construction scales a retained source route by
the factor `288`, replaces its last segment by the outer angular fan, and
rasterizes the result.  Relative to a variable-centered source certificate,
the replacement and rasterization cost at most `288 + 9 = 297` cells.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree

/-- Coordinate-radius containment is symmetric in its two points. -/
theorem WithinCoordinateRadius.symm
    {radius : Nat} {first second : Cell}
    (bounded : WithinCoordinateRadius radius first second) :
    WithinCoordinateRadius radius second first := by
  rcases first with ⟨firstX, firstY⟩
  rcases second with ⟨secondX, secondY⟩
  simp only [WithinCoordinateRadius] at bounded ⊢
  constructor
  · rw [show firstX - secondX = -(secondX - firstX) by ring,
      Int.natAbs_neg]
    exact bounded.1
  · rw [show firstY - secondY = -(secondY - firstY) by ring,
      Int.natAbs_neg]
    exact bounded.2

/-- Membership in a closed coordinate-radius square recovers the equivalent
coordinate-radius predicate. -/
theorem withinCoordinateRadius_of_inClosedGridRectangle_coordinateRadius
    {radius : Nat} {center point : Cell}
    (bounded :
      InClosedGridRectangle
        (coordinateRadiusLower radius center)
        (coordinateRadiusUpper radius center)
        point) :
    WithinCoordinateRadius radius center point := by
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  rw [withinCoordinateRadius_iff_abs_le]
  simp only [InClosedGridRectangle,
    coordinateRadiusLower, coordinateRadiusUpper] at bounded
  constructor <;> apply abs_le.mpr <;> omega

/-- The two nested rectangle expansions used by the outer fan and retained
rasterizer amount to a coordinate-radius increase of exactly `297`. -/
private theorem withinCoordinateRadius_of_nestedScaledRectangle
    {factor radius : Nat} {center point : Cell}
    (bounded :
      InClosedGridRectangle
        (coordinateRadiusLower 9
          (coordinateRadiusLower 288
            (Cell.scale factor
              (coordinateRadiusLower radius center))))
        (coordinateRadiusUpper 9
          (coordinateRadiusUpper 288
            (Cell.scale factor
              (coordinateRadiusUpper radius center))))
        point) :
    WithinCoordinateRadius (factor * radius + 297)
      (Cell.scale factor center) point := by
  rcases center with ⟨centerX, centerY⟩
  rcases point with ⟨pointX, pointY⟩
  rw [withinCoordinateRadius_iff_abs_le]
  simp only [InClosedGridRectangle,
    coordinateRadiusLower, coordinateRadiusUpper,
    Cell.scale, Nat.cast_add, Nat.cast_mul] at bounded ⊢
  ring_nf at bounded ⊢
  constructor <;> apply abs_le.mpr <;> omega

/-- A source route of coordinate radius `radius`, uniformly scaled before
the ordinary outer-fan splice, acquires only the fixed `297`-cell local
margin. -/
theorem
    retainedAngularFanSourceScaledSplicedBoundaryRoute_point_withinCoordinateRadius
    {factor radius : Nat}
    (factorPositive : 0 < factor)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (retained : RetainedRayPolyline route)
    (center : Cell)
    (routeBounded :
      ∀ routePoint ∈ route,
        WithinCoordinateRadius radius center routePoint)
    {point : Cell}
    (pointMember :
      point ∈
        retainedAngularFanSplicedBoundaryRoute
          (scalePolyline factor route)
          (scaleRetainedTerminalData factor terminal)
          slot) :
    WithinCoordinateRadius
      ((retainedTerminalFanTotalRefinement * factor) * radius + 297)
      (Cell.scale
        (retainedTerminalFanTotalRefinement * factor) center)
      point := by
  let lower := coordinateRadiusLower radius center
  let upper := coordinateRadiusUpper radius center
  have sourceInRectangle :
      ∀ routePoint ∈ route,
        InClosedGridRectangle lower upper routePoint := by
    intro routePoint routePointMember
    exact inClosedGridRectangle_coordinateRadius
      (routeBounded routePoint routePointMember)
  let scaledRoute := scalePolyline factor route
  let scaledTerminal := scaleRetainedTerminalData factor terminal
  let splicedPolyline :=
    retainedAngularFanSplicedBoundaryPolyline
      scaledRoute scaledTerminal slot
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal] using
      routeTerminalVector_scale_classified
        factorPositive classified
  have scaledRetained : RetainedRayPolyline scaledRoute :=
    retained.scale factorPositive
  have splicedRetained : RetainedRayPolyline splicedPolyline := by
    simpa [splicedPolyline] using
      retainedAngularFanSplicedBoundaryPolyline_retained
        scaledRoute scaledTerminal slot scaledLength
        scaledClassified scaledRetained
  have splicedBounded :
      ∀ splicedPoint ∈ splicedPolyline,
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              lower))
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              upper))
          splicedPoint := by
    intro splicedPoint splicedPointMember
    exact
      retainedAngularFanSourceScaledSplicedBoundaryPolyline_point_in_routeRectangle
        factorPositive route terminal slot routeLength classified
        lower upper sourceInRectangle
        (by simpa [splicedPolyline, scaledRoute, scaledTerminal]
          using splicedPointMember)
  have rasterBounded :=
    rasterizeRetainedPolyline_point_in_expandedRectangle
      splicedRetained splicedBounded
      (by simpa [retainedAngularFanSplicedBoundaryRoute,
        splicedPolyline, scaledRoute, scaledTerminal]
        using pointMember)
  exact withinCoordinateRadius_of_nestedScaledRectangle
    (by simpa [lower, upper] using rasterBounded)

/-- The delayed-lane escaped outer-fan splice satisfies the same
variable-centered radius estimate. -/
theorem
    retainedAngularFanSourceScaledEscapedSplicedBoundaryRoute_point_withinCoordinateRadius
    {factor radius : Nat}
    (factorPositive : 0 < factor)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (retained : RetainedRayPolyline route)
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor terminal))
    (center : Cell)
    (routeBounded :
      ∀ routePoint ∈ route,
        WithinCoordinateRadius radius center routePoint)
    {point : Cell}
    (pointMember :
      point ∈
        retainedAngularFanEscapedSplicedBoundaryRoute
          (scalePolyline factor route)
          (scaleRetainedTerminalData factor terminal)
          slot) :
    WithinCoordinateRadius
      ((retainedTerminalFanTotalRefinement * factor) * radius + 297)
      (Cell.scale
        (retainedTerminalFanTotalRefinement * factor) center)
      point := by
  let lower := coordinateRadiusLower radius center
  let upper := coordinateRadiusUpper radius center
  have sourceInRectangle :
      ∀ routePoint ∈ route,
        InClosedGridRectangle lower upper routePoint := by
    intro routePoint routePointMember
    exact inClosedGridRectangle_coordinateRadius
      (routeBounded routePoint routePointMember)
  let scaledRoute := scalePolyline factor route
  let scaledTerminal := scaleRetainedTerminalData factor terminal
  let splicedPolyline :=
    retainedAngularFanEscapedSplicedBoundaryPolyline
      scaledRoute scaledTerminal slot
  have scaledLength : 2 ≤ scaledRoute.length := by
    simpa [scaledRoute, scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector scaledRoute) =
        some scaledTerminal := by
    simpa [scaledRoute, scaledTerminal] using
      routeTerminalVector_scale_classified
        factorPositive classified
  have scaledRetained : RetainedRayPolyline scaledRoute :=
    retained.scale factorPositive
  have splicedRetained : RetainedRayPolyline splicedPolyline := by
    simpa [splicedPolyline] using
      retainedAngularFanEscapedSplicedBoundaryPolyline_retained
        scaledRoute scaledTerminal slot scaledLength
        scaledClassified scaledRetained
        (by simpa [scaledTerminal] using escapeFits)
  have splicedBounded :
      ∀ splicedPoint ∈ splicedPolyline,
        InClosedGridRectangle
          (coordinateRadiusLower 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              lower))
          (coordinateRadiusUpper 288
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              upper))
          splicedPoint := by
    intro splicedPoint splicedPointMember
    exact
      retainedAngularFanSourceScaledEscapedSplicedBoundaryPolyline_point_in_routeRectangle
        factorPositive route terminal slot routeLength classified
        escapeFits lower upper sourceInRectangle
        (by simpa [splicedPolyline, scaledRoute, scaledTerminal]
          using splicedPointMember)
  have rasterBounded :=
    rasterizeRetainedPolyline_point_in_expandedRectangle
      splicedRetained splicedBounded
      (by simpa [retainedAngularFanEscapedSplicedBoundaryRoute,
        splicedPolyline, scaledRoute, scaledTerminal]
        using pointMember)
  exact withinCoordinateRadius_of_nestedScaledRectangle
    (by simpa [lower, upper] using rasterBounded)

/-- Adding the local Figure 7 suffix and recentering at its copied variable
costs another `48` cells beyond the boundary-splice estimate. -/
theorem
    retainedAngularFanSourceScaledSplicedOccurrenceRoute_point_withinCopiedLiteralRadius
    {Variable : Type*} [DecidableEq Variable]
    {factor radius : Nat}
    (factorPositive : 0 < factor)
    (source : PositionedPeriodicCNF Variable)
    (placement : PeriodicVariablePlacement Variable)
    (routes : PositionedPeriodicCNF.IncidenceRoutes)
    {clause : PositionedPeriodicClause Variable}
    {clauseIndex : Nat}
    (clauseMember :
      (clause, clauseIndex) ∈ source.clauses.zipIdx)
    {literal : PeriodicLiteral Variable}
    {literalIndex : Nat}
    (literalMember :
      (literal, literalIndex) ∈ clause.literals.zipIdx)
    (terminal : RetainedTerminalData)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            (routes clauseIndex literalIndex)) =
        some terminal)
    (routeLength :
      2 ≤ (routes clauseIndex literalIndex).length)
    (retained :
      RetainedRayPolyline
        (routes clauseIndex literalIndex))
    (routeBounded :
      ∀ routePoint ∈ routes clauseIndex literalIndex,
        WithinCoordinateRadius radius
          (PositionedPeriodicCNF.canonicalLiteralPosition
            placement clause literal)
          routePoint)
    {point : Cell}
    (pointMember :
      point ∈
        retainedAngularFanSplicedOccurrenceRoute
          (source.scale factor)
          (placement.scale factor)
          (PositionedPeriodicCNF.scaleIncidenceRoutes
            factor routes)
          (clause.scale factor) literal
          clauseIndex literalIndex) :
    let scaledSource := source.scale factor
    let scaledPlacement := placement.scale factor
    let scaledRoutes :=
      PositionedPeriodicCNF.scaleIncidenceRoutes factor routes
    let occurrencePorts :=
      occurrencePortsOfAngularOrder scaledSource.erase
        (angularOccurrenceOrder scaledSource.erase scaledRoutes)
    let copiedClause :=
      PeriodicEightOccurrenceSplitPositioned.occurrenceClause
        occurrencePorts clauseIndex (clause.scale factor)
    let copiedLiteral :=
      PeriodicEightOccurrenceSplit.occurrenceLiteral
        occurrencePorts clauseIndex literalIndex literal
    WithinCoordinateRadius
      ((retainedTerminalFanTotalRefinement * factor) * radius + 345)
      (Cell.scale retainedTerminalFanRoutingRefinement
        (PositionedPeriodicCNF.canonicalLiteralPosition
          (PeriodicEightOccurrenceSplitPositioned.placement
            scaledPlacement)
          copiedClause copiedLiteral))
      point := by
  dsimp only
  let scaledSource := source.scale factor
  let scaledPlacement := placement.scale factor
  let scaledRoutes :=
    PositionedPeriodicCNF.scaleIncidenceRoutes factor routes
  let order :=
    angularOccurrenceOrder scaledSource.erase scaledRoutes
  let occurrencePorts :=
    occurrencePortsOfAngularOrder scaledSource.erase order
  let copiedClause :=
    PeriodicEightOccurrenceSplitPositioned.occurrenceClause
      occurrencePorts clauseIndex (clause.scale factor)
  let copiedLiteral :=
    PeriodicEightOccurrenceSplit.occurrenceLiteral
      occurrencePorts clauseIndex literalIndex literal
  let sourceCenter :=
    PositionedPeriodicCNF.canonicalLiteralPosition
      placement clause literal
  let refinedSourceCenter :=
    Cell.scale
      (retainedTerminalFanTotalRefinement * factor)
      sourceCenter
  let copiedCenter :=
    Cell.scale retainedTerminalFanRoutingRefinement
      (PositionedPeriodicCNF.canonicalLiteralPosition
        (PeriodicEightOccurrenceSplitPositioned.placement
          scaledPlacement)
        copiedClause copiedLiteral)
  have scaledClauseMember :
      (clause.scale factor, clauseIndex) ∈
        scaledSource.clauses.zipIdx := by
    rw [PositionedPeriodicCNF.scale_clauses,
      List.zipIdx_map]
    exact List.mem_map.mpr
      ⟨(clause, clauseIndex), clauseMember, rfl⟩
  have scaledLiteralMember :
      (literal, literalIndex) ∈
        (clause.scale factor).literals.zipIdx := by
    simpa using literalMember
  have copiedCenterFromScaledSource :=
    occurrenceLiteralPosition_within_scaledSourceLiteral
      scaledPlacement occurrencePorts clauseIndex literalIndex
      (clause.scale factor) literal
  have copiedCenterFromSource :
      WithinCoordinateRadius 48
        refinedSourceCenter copiedCenter := by
    have refined :=
      copiedCenterFromScaledSource.scale
        retainedTerminalFanRoutingRefinement
    have refinedCenterEq :
        Cell.scale retainedTerminalFanRoutingRefinement
            (Cell.scale
              PeriodicEightOccurrenceSplitPositioned.refinementScale
              (PositionedPeriodicCNF.canonicalLiteralPosition
                scaledPlacement (clause.scale factor) literal)) =
          refinedSourceCenter := by
      rcases centerEq : sourceCenter with ⟨centerX, centerY⟩
      apply Prod.ext <;>
        simp [refinedSourceCenter, sourceCenter, scaledPlacement,
          PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale,
          Cell.scale_scale, retainedTerminalFanTotalRefinement_eq,
          retainedTerminalFanRoutingRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          Nat.cast_mul, centerEq] <;>
        ring_nf
    rw [refinedCenterEq] at refined
    simpa [copiedCenter, copiedClause, copiedLiteral,
      retainedTerminalFanRoutingRefinement]
      using refined
  have scaledTerminalEq :
      classifiedRetainedTerminalData
          (routeTerminalVector
            (scaledRoutes clauseIndex literalIndex)) =
        scaleRetainedTerminalData factor terminal := by
    unfold scaledRoutes
    rw [PositionedPeriodicCNF.scaleIncidenceRoutes_apply,
      routeTerminalVector_scalePolyline,
      classifiedRetainedTerminalData_scale_of_classified
        factorPositive classified,
      classifiedRetainedTerminalData_eq_of_classified classified]
  have scaledOccurrenceIndexEq :
      angularOccurrenceIndex
          (angularOccurrenceOrder scaledSource.erase scaledRoutes)
          literal clauseIndex literalIndex =
        angularOccurrenceIndex
          (angularOccurrenceOrder source.erase routes)
          literal clauseIndex literalIndex := by
    unfold angularOccurrenceIndex
    simp only [angularOccurrenceOrder_copies,
      scaledSource, scaledRoutes,
      PositionedPeriodicCNF.erase_scale]
    rw [angularOccurrenceVariables_scaleIncidenceRoutes
      source.erase factorPositive routes]
  change WithinCoordinateRadius
    ((retainedTerminalFanTotalRefinement * factor) * radius + 345)
    copiedCenter point
  unfold retainedAngularFanSplicedOccurrenceRoute at pointMember
  rcases mem_joinAtEndpoint pointMember with
    boundaryMember | suffixMember
  · rw [retainedAngularFanBoundaryIncidenceRoutes_of_members
      scaledSource scaledRoutes scaledClauseMember scaledLiteralMember]
      at boundaryMember
    simp only [scaledOccurrenceIndexEq, scaledTerminalEq]
      at boundaryMember
    have boundaryBounded :=
      retainedAngularFanSourceScaledSplicedBoundaryRoute_point_withinCoordinateRadius
        factorPositive (routes clauseIndex literalIndex)
        terminal
        (boundedRetainedTerminalSlot
          (angularOccurrenceIndex
            (angularOccurrenceOrder source.erase routes)
            literal clauseIndex literalIndex))
        routeLength classified retained sourceCenter
        (by simpa [sourceCenter] using routeBounded)
        (by simpa [scaledSource, scaledRoutes] using boundaryMember)
    have recentered :=
      copiedCenterFromSource.symm.trans boundaryBounded
    exact recentered.mono (by omega)
  · have suffixRectangle :=
      scaledAngularOccurrenceSuffix_point_in_centerRectangle
        scaledPlacement order (clause.scale factor) literal
        clauseIndex literalIndex suffixMember
    have suffixBounded :
        WithinCoordinateRadius 96
          refinedSourceCenter point := by
      apply
        withinCoordinateRadius_of_inClosedGridRectangle_coordinateRadius
      simpa [refinedSourceCenter, sourceCenter,
        scaledPlacement,
        PositionedPeriodicCNF.CanonicalRetainedRayIncidenceRoutes.canonicalLiteralPosition_scale,
        Cell.scale_scale, retainedTerminalFanTotalRefinement_eq,
        retainedTerminalFanRoutingRefinement,
        PeriodicEightOccurrenceSplitPositioned.refinementScale,
        Nat.cast_mul, mul_assoc] using suffixRectangle
    have recentered :=
      copiedCenterFromSource.symm.trans suffixBounded
    exact recentered.mono (by omega)

end PeriodicEightOccurrenceSplit
end LeanTrominoes
