import LeanTrominoes.RetainedAngularFanCarrierLensSingletonGeometry
import LeanTrominoes.RetainedAngularFanSourceSpliceBounds

/-!
# Cross-spoke separation for singleton equality-lens fallbacks

The exceptional equality-lens fallback has two remaining separation
obligations after its two boundary splices have been compared: each splice
must avoid the Figure 7 suffix attached to the other source route.  A
singleton lens route and the opposite variable endpoint occupy disjoint
integral rectangles; conversely, the singleton endpoint is disjoint from
the narrow rectangle occupied by its partner route.  The factor-four source
clearance leaves these rectangles disjoint after both are expanded by the
radius-288 splice bound.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicOrthocrossing
open PeriodicThreeSATThree
open PlanarThreeSAT
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

set_option maxHeartbeats 2000000

private theorem upperLeftRoute_point_in_segmentRectangle
    (origin : Cell) (direction : AxisDirection) (span : Int)
    {point : Cell}
    (pointMember :
      point ∈
        (axisEqualityLensDrawing
          origin direction span).routes 0 0) :
    let segment : GridSegment :=
      ⟨Cell.add origin (direction.orientPoint (3, 0)),
        Cell.add origin (direction.orientPoint (0, 0))⟩
    InClosedGridRectangle
      segment.coordinateLower segment.coordinateUpper point := by
  dsimp only
  simp [axisEqualityLensDrawing,
    EmbeddedCNFIncidenceDrawing.placeOnAxis,
    EmbeddedCNFIncidenceDrawing.orient,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedCNFIncidenceDrawing.mapPoints,
    horizontalEqualityLensDrawing,
    horizontalEqualityLensRoutes,
    horizontalEqualityLensUpperLeftRoute] at pointMember
  rcases pointMember with rfl | rfl
  · exact GridSegment.start_in_coordinateRectangle _
  · exact GridSegment.finish_in_coordinateRectangle _

private theorem upperRightRoute_point_in_rectangle
    (origin : Cell) (direction : AxisDirection) (span : Int)
    (spanLarge : 8 ≤ span)
    {point : Cell}
    (pointMember :
      point ∈
        (axisEqualityLensDrawing
          origin direction span).routes 0 1) :
    let diagonal : GridSegment :=
      ⟨Cell.add origin (direction.orientPoint (3, -2)),
        Cell.add origin (direction.orientPoint (span, 0))⟩
    InClosedGridRectangle
      diagonal.coordinateLower diagonal.coordinateUpper point := by
  dsimp only
  simp [axisEqualityLensDrawing,
    EmbeddedCNFIncidenceDrawing.placeOnAxis,
    EmbeddedCNFIncidenceDrawing.orient,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedCNFIncidenceDrawing.mapPoints,
    horizontalEqualityLensDrawing,
    horizontalEqualityLensRoutes,
    horizontalEqualityLensUpperRightRoute] at pointMember
  rcases origin with ⟨originX, originY⟩
  rcases pointMember with rfl | rfl | rfl | rfl
  all_goals
    cases direction <;>
      simp [InClosedGridRectangle,
        GridSegment.coordinateLower,
        GridSegment.coordinateUpper,
        AxisDirection.orientPoint, Cell.add] <;>
      omega

private theorem lowerRightRoute_point_in_segmentRectangle
    (origin : Cell) (direction : AxisDirection) (span : Int)
    {point : Cell}
    (pointMember :
      point ∈
        (axisEqualityLensDrawing
          origin direction span).routes 1 1) :
    let segment : GridSegment :=
      ⟨Cell.add origin (direction.orientPoint (6, 0)),
        Cell.add origin (direction.orientPoint (span, 0))⟩
    InClosedGridRectangle
      segment.coordinateLower segment.coordinateUpper point := by
  dsimp only
  simp [axisEqualityLensDrawing,
    EmbeddedCNFIncidenceDrawing.placeOnAxis,
    EmbeddedCNFIncidenceDrawing.orient,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedCNFIncidenceDrawing.mapPoints,
    horizontalEqualityLensDrawing,
    horizontalEqualityLensRoutes,
    horizontalEqualityLensLowerRightRoute] at pointMember
  rcases pointMember with rfl | rfl
  · exact GridSegment.start_in_coordinateRectangle _
  · exact GridSegment.finish_in_coordinateRectangle _

private theorem lowerLeftRoute_point_in_rectangle
    (origin : Cell) (direction : AxisDirection) (span : Int)
    {point : Cell}
    (pointMember :
      point ∈
        (axisEqualityLensDrawing
          origin direction span).routes 1 0) :
    let diagonal : GridSegment :=
      ⟨Cell.add origin (direction.orientPoint (0, 0)),
        Cell.add origin (direction.orientPoint (6, 1))⟩
    InClosedGridRectangle
      diagonal.coordinateLower diagonal.coordinateUpper point := by
  dsimp only
  simp [axisEqualityLensDrawing,
    EmbeddedCNFIncidenceDrawing.placeOnAxis,
    EmbeddedCNFIncidenceDrawing.orient,
    EmbeddedCNFIncidenceDrawing.translate,
    EmbeddedCNFIncidenceDrawing.mapPoints,
    horizontalEqualityLensDrawing,
    horizontalEqualityLensRoutes,
    horizontalEqualityLensLowerLeftRoute] at pointMember
  rcases origin with ⟨originX, originY⟩
  rcases pointMember with rfl | rfl | rfl | rfl
  all_goals
    cases direction <;>
      simp [InClosedGridRectangle,
        GridSegment.coordinateLower,
        GridSegment.coordinateUpper,
        AxisDirection.orientPoint, Cell.add]

private theorem upperSingletonRectangle_separated_target
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span) :
    let segment : GridSegment :=
      ⟨Cell.add origin (direction.orientPoint (3, 0)),
        Cell.add origin (direction.orientPoint (0, 0))⟩
    let target :=
      Cell.add origin (direction.orientPoint (span, 0))
    ClosedGridRectanglesSeparated
      segment.coordinateLower segment.coordinateUpper
      target target := by
  rcases origin with ⟨originX, originY⟩
  cases direction <;>
    simp [ClosedGridRectanglesSeparated,
      GridSegment.coordinateLower,
      GridSegment.coordinateUpper,
      AxisDirection.orientPoint, Cell.add] <;>
    omega

private theorem upperTarget_separated_partnerRectangle
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span) :
    let target :=
      Cell.add origin (direction.orientPoint (0, 0))
    let diagonal : GridSegment :=
      ⟨Cell.add origin (direction.orientPoint (3, -2)),
        Cell.add origin (direction.orientPoint (span, 0))⟩
    ClosedGridRectanglesSeparated
      target target
      diagonal.coordinateLower diagonal.coordinateUpper := by
  rcases origin with ⟨originX, originY⟩
  cases direction <;>
    simp [ClosedGridRectanglesSeparated,
      GridSegment.coordinateLower,
      GridSegment.coordinateUpper,
      AxisDirection.orientPoint, Cell.add] <;>
    omega

private theorem lowerSingletonRectangle_separated_target
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span) :
    let segment : GridSegment :=
      ⟨Cell.add origin (direction.orientPoint (6, 0)),
        Cell.add origin (direction.orientPoint (span, 0))⟩
    let target :=
      Cell.add origin (direction.orientPoint (0, 0))
    ClosedGridRectanglesSeparated
      segment.coordinateLower segment.coordinateUpper
      target target := by
  rcases origin with ⟨originX, originY⟩
  cases direction <;>
    simp [ClosedGridRectanglesSeparated,
      GridSegment.coordinateLower,
      GridSegment.coordinateUpper,
      AxisDirection.orientPoint, Cell.add] <;>
    omega

private theorem lowerTarget_separated_partnerRectangle
    (origin : Cell) (direction : AxisDirection)
    (span : Int) (spanLarge : 8 ≤ span) :
    let target :=
      Cell.add origin (direction.orientPoint (span, 0))
    let diagonal : GridSegment :=
      ⟨Cell.add origin (direction.orientPoint (0, 0)),
        Cell.add origin (direction.orientPoint (6, 1))⟩
    ClosedGridRectanglesSeparated
      target target
      diagonal.coordinateLower diagonal.coordinateUpper := by
  rcases origin with ⟨originX, originY⟩
  cases direction <;>
    simp [ClosedGridRectanglesSeparated,
      GridSegment.coordinateLower,
      GridSegment.coordinateUpper,
      AxisDirection.orientPoint, Cell.add] <;>
    omega

private theorem
    splices_crossSuffixes_strictlyAvoid_of_rectangles
    (firstRoute secondRoute : List Cell)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstLength : 2 ≤ firstRoute.length)
    (secondLength : 2 ≤ secondRoute.length)
    (firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector firstRoute) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector secondRoute) =
        some secondTerminal)
    (firstEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            firstTerminal))
    (firstLower firstUpper secondLower secondUpper : Cell)
    (firstRouteBounded :
      ∀ point ∈ firstRoute,
        InClosedGridRectangle firstLower firstUpper point)
    (secondRouteBounded :
      ∀ point ∈ secondRoute,
        InClosedGridRectangle secondLower secondUpper point)
    (firstTarget secondTarget : Cell)
    (firstRectangleSeparatedSecondTarget :
      ClosedGridRectanglesSeparated
        firstLower firstUpper secondTarget secondTarget)
    (firstTargetSeparatedSecondRectangle :
      ClosedGridRectanglesSeparated
        firstTarget firstTarget secondLower secondUpper)
    (firstSuffix secondSuffix : List Cell)
    (firstSuffixBounded :
      ∀ point ∈ firstSuffix,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              firstTarget))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              firstTarget))
          point)
    (secondSuffixBounded :
      ∀ point ∈ secondSuffix,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              secondTarget))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              secondTarget))
          point) :
    RoutesStrictlyAvoidEachOther
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          (scalePolyline
            retainedAngularFanSourceClearanceFactor firstRoute)
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor firstTerminal)
          firstSlot)
        secondSuffix ∧
      RoutesStrictlyAvoidEachOther
        firstSuffix
        (retainedAngularFanSplicedBoundaryPolyline
          (scalePolyline
            retainedAngularFanSourceClearanceFactor secondRoute)
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor secondTerminal)
          secondSlot) := by
  let combinedFactor :=
    retainedTerminalFanTotalRefinement *
      retainedAngularFanSourceClearanceFactor
  have combinedPositive : 0 < combinedFactor := by
    native_decide
  have clearance : 2 * 288 < combinedFactor := by
    native_decide
  constructor
  · apply
      routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
        (firstLower :=
          coordinateRadiusLower 288
            (Cell.scale combinedFactor firstLower))
        (firstUpper :=
          coordinateRadiusUpper 288
            (Cell.scale combinedFactor firstUpper))
        (secondLower :=
          coordinateRadiusLower 288
            (Cell.scale combinedFactor secondTarget))
        (secondUpper :=
          coordinateRadiusUpper 288
            (Cell.scale combinedFactor secondTarget))
    · intro point pointMember
      exact
        retainedAngularFanSourceScaledEscapedSplicedBoundaryPolyline_point_in_routeRectangle
          retainedAngularFanSourceClearanceFactor_pos
          firstRoute firstTerminal firstSlot
          firstLength firstClassified firstEscapeFits
          firstLower firstUpper firstRouteBounded
          pointMember
    · intro point pointMember
      exact
        inClosedGridRectangle_coordinateRadius_mono
          (secondSuffixBounded point pointMember)
          (by omega)
    · exact
        ClosedGridRectanglesSeparated.scale_both_coordinateRadius
          firstRectangleSeparatedSecondTarget
          combinedPositive clearance
  · apply
      routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
        (firstLower :=
          coordinateRadiusLower 288
            (Cell.scale combinedFactor firstTarget))
        (firstUpper :=
          coordinateRadiusUpper 288
            (Cell.scale combinedFactor firstTarget))
        (secondLower :=
          coordinateRadiusLower 288
            (Cell.scale combinedFactor secondLower))
        (secondUpper :=
          coordinateRadiusUpper 288
            (Cell.scale combinedFactor secondUpper))
    · intro point pointMember
      exact
        inClosedGridRectangle_coordinateRadius_mono
          (firstSuffixBounded point pointMember)
          (by omega)
    · intro point pointMember
      exact
        retainedAngularFanSourceScaledSplicedBoundaryPolyline_point_in_routeRectangle
          retainedAngularFanSourceClearanceFactor_pos
          secondRoute secondTerminal secondSlot
          secondLength secondClassified
          secondLower secondUpper secondRouteBounded
          pointMember
    · exact
        ClosedGridRectanglesSeparated.scale_both_coordinateRadius
        firstTargetSeparatedSecondRectangle
          combinedPositive clearance

/-- For the singleton route of either equality-lens clause, both completed
boundary splices strictly avoid the Figure 7 suffix attached to the other
literal.  The suffix hypotheses expose only their uniform radius-96 bound
around the corresponding source endpoint. -/
theorem axisEqualityLensRoutes_singletonSplices_crossSuffixes_strictlyAvoid
    (origin : Cell)
    (direction : AxisDirection)
    (span : Int)
    (spanLarge : 8 ≤ span)
    (clauseIndex firstLiteralIndex secondLiteralIndex : Nat)
    (indicesDifferent : firstLiteralIndex ≠ secondLiteralIndex)
    (secondLiteralIndexLt : secondLiteralIndex < 2)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstLength :
      2 ≤
        ((axisEqualityLensDrawing
          origin direction span).routes
            clauseIndex firstLiteralIndex).length)
    (secondLength :
      2 ≤
        ((axisEqualityLensDrawing
          origin direction span).routes
            clauseIndex secondLiteralIndex).length)
    (firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            ((axisEqualityLensDrawing
              origin direction span).routes
                clauseIndex firstLiteralIndex)) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            ((axisEqualityLensDrawing
              origin direction span).routes
                clauseIndex secondLiteralIndex)) =
        some secondTerminal)
    (firstEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            firstTerminal))
    (singletonPrefix :
      ((axisEqualityLensDrawing
        origin direction span).routes
          clauseIndex firstLiteralIndex).dropLast.length = 1)
    (firstSuffix secondSuffix : List Cell)
    (firstSuffixBounded :
      ∀ point ∈ firstSuffix,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              (((axisEqualityLensDrawing
                origin direction span).routes
                  clauseIndex firstLiteralIndex).getLastD (0, 0))))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              (((axisEqualityLensDrawing
                origin direction span).routes
                  clauseIndex firstLiteralIndex).getLastD (0, 0))))
          point)
    (secondSuffixBounded :
      ∀ point ∈ secondSuffix,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              (((axisEqualityLensDrawing
                origin direction span).routes
                  clauseIndex secondLiteralIndex).getLastD (0, 0))))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              (((axisEqualityLensDrawing
                origin direction span).routes
                  clauseIndex secondLiteralIndex).getLastD (0, 0))))
          point) :
    RoutesStrictlyAvoidEachOther
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          (scalePolyline retainedAngularFanSourceClearanceFactor
            ((axisEqualityLensDrawing
              origin direction span).routes
                clauseIndex firstLiteralIndex))
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor firstTerminal)
          firstSlot)
        secondSuffix ∧
      RoutesStrictlyAvoidEachOther
        firstSuffix
        (retainedAngularFanSplicedBoundaryPolyline
          (scalePolyline retainedAngularFanSourceClearanceFactor
            ((axisEqualityLensDrawing
              origin direction span).routes
                clauseIndex secondLiteralIndex))
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor secondTerminal)
          secondSlot) := by
  rcases clauseIndex with (_ | _ | clauseIndex) <;>
    rcases firstLiteralIndex with
      (_ | _ | firstLiteralIndex) <;>
    rcases secondLiteralIndex with
      (_ | _ | secondLiteralIndex)
  all_goals
    simp_all [axisEqualityLensDrawing,
      EmbeddedCNFIncidenceDrawing.placeOnAxis,
      EmbeddedCNFIncidenceDrawing.orient,
      EmbeddedCNFIncidenceDrawing.translate,
      EmbeddedCNFIncidenceDrawing.mapPoints,
      horizontalEqualityLensDrawing,
      horizontalEqualityLensRoutes,
      horizontalEqualityLensUpperLeftRoute,
      horizontalEqualityLensUpperRightRoute,
      horizontalEqualityLensLowerLeftRoute,
      horizontalEqualityLensLowerRightRoute]
  · let firstSegment : GridSegment :=
      ⟨Cell.add origin (direction.orientPoint (3, 0)),
        Cell.add origin (direction.orientPoint (0, 0))⟩
    let secondDiagonal : GridSegment :=
      ⟨Cell.add origin (direction.orientPoint (3, -2)),
        Cell.add origin (direction.orientPoint (span, 0))⟩
    have separated :=
      splices_crossSuffixes_strictlyAvoid_of_rectangles
        (firstRoute :=
          [Cell.add origin (direction.orientPoint (3, 0)),
            Cell.add origin (direction.orientPoint (0, 0))])
        (secondRoute :=
          [Cell.add origin (direction.orientPoint (3, 0)),
            Cell.add origin (direction.orientPoint (3, -2)),
            Cell.add origin (direction.orientPoint (span, -2)),
            Cell.add origin (direction.orientPoint (span, 0))])
        firstTerminal secondTerminal firstSlot secondSlot
        (by simp) (by simp)
        firstClassified secondClassified firstEscapeFits
        firstSegment.coordinateLower firstSegment.coordinateUpper
        secondDiagonal.coordinateLower secondDiagonal.coordinateUpper
        (by
          intro point pointMember
          apply upperLeftRoute_point_in_segmentRectangle
            origin direction span
          simpa [axisEqualityLensDrawing,
            EmbeddedCNFIncidenceDrawing.placeOnAxis,
            EmbeddedCNFIncidenceDrawing.orient,
            EmbeddedCNFIncidenceDrawing.translate,
            EmbeddedCNFIncidenceDrawing.mapPoints,
            horizontalEqualityLensDrawing,
            horizontalEqualityLensRoutes,
            horizontalEqualityLensUpperLeftRoute] using pointMember)
        (by
          intro point pointMember
          apply upperRightRoute_point_in_rectangle
            origin direction span spanLarge
          simpa [axisEqualityLensDrawing,
            EmbeddedCNFIncidenceDrawing.placeOnAxis,
            EmbeddedCNFIncidenceDrawing.orient,
            EmbeddedCNFIncidenceDrawing.translate,
            EmbeddedCNFIncidenceDrawing.mapPoints,
            horizontalEqualityLensDrawing,
            horizontalEqualityLensRoutes,
            horizontalEqualityLensUpperRightRoute] using pointMember)
        (Cell.add origin (direction.orientPoint (0, 0)))
        (Cell.add origin (direction.orientPoint (span, 0)))
        (by
          simpa [firstSegment] using
            upperSingletonRectangle_separated_target
              origin direction span spanLarge)
        (by
          simpa [secondDiagonal] using
            upperTarget_separated_partnerRectangle
              origin direction span spanLarge)
        firstSuffix secondSuffix
        (by
          simpa [retainedTerminalFanTotalRefinement_eq,
            retainedAngularFanSourceClearanceFactor_eq] using
              firstSuffixBounded)
        (by
          simpa [retainedTerminalFanTotalRefinement_eq,
            retainedAngularFanSourceClearanceFactor_eq] using
              secondSuffixBounded)
    simpa using separated
  · let firstSegment : GridSegment :=
      ⟨Cell.add origin (direction.orientPoint (6, 0)),
        Cell.add origin (direction.orientPoint (span, 0))⟩
    let secondDiagonal : GridSegment :=
      ⟨Cell.add origin (direction.orientPoint (0, 0)),
        Cell.add origin (direction.orientPoint (6, 1))⟩
    have separated :=
      splices_crossSuffixes_strictlyAvoid_of_rectangles
        (firstRoute :=
          [Cell.add origin (direction.orientPoint (6, 0)),
            Cell.add origin (direction.orientPoint (span, 0))])
        (secondRoute :=
          [Cell.add origin (direction.orientPoint (6, 0)),
            Cell.add origin (direction.orientPoint (6, 1)),
            Cell.add origin (direction.orientPoint (0, 1)),
            Cell.add origin (direction.orientPoint (0, 0))])
        firstTerminal secondTerminal firstSlot secondSlot
        (by simp) (by simp)
        firstClassified secondClassified firstEscapeFits
        firstSegment.coordinateLower firstSegment.coordinateUpper
        secondDiagonal.coordinateLower secondDiagonal.coordinateUpper
        (by
          intro point pointMember
          apply lowerRightRoute_point_in_segmentRectangle
            origin direction span
          simpa [axisEqualityLensDrawing,
            EmbeddedCNFIncidenceDrawing.placeOnAxis,
            EmbeddedCNFIncidenceDrawing.orient,
            EmbeddedCNFIncidenceDrawing.translate,
            EmbeddedCNFIncidenceDrawing.mapPoints,
            horizontalEqualityLensDrawing,
            horizontalEqualityLensRoutes,
            horizontalEqualityLensLowerRightRoute] using pointMember)
        (by
          intro point pointMember
          apply lowerLeftRoute_point_in_rectangle
            origin direction span
          simpa [axisEqualityLensDrawing,
            EmbeddedCNFIncidenceDrawing.placeOnAxis,
            EmbeddedCNFIncidenceDrawing.orient,
            EmbeddedCNFIncidenceDrawing.translate,
            EmbeddedCNFIncidenceDrawing.mapPoints,
            horizontalEqualityLensDrawing,
            horizontalEqualityLensRoutes,
            horizontalEqualityLensLowerLeftRoute] using pointMember)
        (Cell.add origin (direction.orientPoint (span, 0)))
        (Cell.add origin (direction.orientPoint (0, 0)))
        (by
          simpa [firstSegment] using
            lowerSingletonRectangle_separated_target
              origin direction span spanLarge)
        (by
          simpa [secondDiagonal] using
            lowerTarget_separated_partnerRectangle
              origin direction span spanLarge)
        firstSuffix secondSuffix
        (by
          simpa [retainedTerminalFanTotalRefinement_eq,
            retainedAngularFanSourceClearanceFactor_eq] using
              firstSuffixBounded)
        (by
          simpa [retainedTerminalFanTotalRefinement_eq,
            retainedAngularFanSourceClearanceFactor_eq] using
              secondSuffixBounded)
    simpa using separated

/-- Logical endpoint renaming preserves the two singleton-lens
splice/suffix separation certificates. -/
theorem
    drawingPlanarSATCarrierLensIncidenceDrawing_singletonSplices_crossSuffixes_strictlyAvoid
    {Variable : Type*} [DecidableEq Variable]
    (formula : PeriodicCNF Variable)
    (link : EqualityLink CarrierNode)
    (geometry :
      EqualityLink.LensGeometry
        (CarrierNode.position formula.incidenceGraph) link)
    (clauseIndex firstLiteralIndex secondLiteralIndex : Nat)
    (indicesDifferent : firstLiteralIndex ≠ secondLiteralIndex)
    (secondLiteralIndexLt : secondLiteralIndex < 2)
    (firstTerminal secondTerminal : RetainedTerminalData)
    (firstSlot secondSlot : RetainedTerminalSlot)
    (firstLength :
      2 ≤
        ((drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).routes
            clauseIndex firstLiteralIndex).length)
    (secondLength :
      2 ≤
        ((drawingPlanarSATCarrierLensIncidenceDrawing
          formula link).routes
            clauseIndex secondLiteralIndex).length)
    (firstClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            ((drawingPlanarSATCarrierLensIncidenceDrawing
              formula link).routes
                clauseIndex firstLiteralIndex)) =
        some firstTerminal)
    (secondClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            ((drawingPlanarSATCarrierLensIncidenceDrawing
              formula link).routes
                clauseIndex secondLiteralIndex)) =
        some secondTerminal)
    (firstEscapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor
            firstTerminal))
    (singletonPrefix :
      ((drawingPlanarSATCarrierLensIncidenceDrawing
        formula link).routes
          clauseIndex firstLiteralIndex).dropLast.length = 1)
    (firstSuffix secondSuffix : List Cell)
    (firstSuffixBounded :
      ∀ point ∈ firstSuffix,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              (((drawingPlanarSATCarrierLensIncidenceDrawing
                formula link).routes
                  clauseIndex firstLiteralIndex).getLastD (0, 0))))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              (((drawingPlanarSATCarrierLensIncidenceDrawing
                formula link).routes
                  clauseIndex firstLiteralIndex).getLastD (0, 0))))
          point)
    (secondSuffixBounded :
      ∀ point ∈ secondSuffix,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              (((drawingPlanarSATCarrierLensIncidenceDrawing
                formula link).routes
                  clauseIndex secondLiteralIndex).getLastD (0, 0))))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement *
                retainedAngularFanSourceClearanceFactor)
              (((drawingPlanarSATCarrierLensIncidenceDrawing
                formula link).routes
                  clauseIndex secondLiteralIndex).getLastD (0, 0))))
          point) :
    RoutesStrictlyAvoidEachOther
        (retainedAngularFanEscapedSplicedBoundaryPolyline
          (scalePolyline retainedAngularFanSourceClearanceFactor
            ((drawingPlanarSATCarrierLensIncidenceDrawing
              formula link).routes
                clauseIndex firstLiteralIndex))
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor firstTerminal)
          firstSlot)
        secondSuffix ∧
      RoutesStrictlyAvoidEachOther
        firstSuffix
        (retainedAngularFanSplicedBoundaryPolyline
          (scalePolyline retainedAngularFanSourceClearanceFactor
            ((drawingPlanarSATCarrierLensIncidenceDrawing
              formula link).routes
                clauseIndex secondLiteralIndex))
          (scaleRetainedTerminalData
            retainedAngularFanSourceClearanceFactor secondTerminal)
          secondSlot) := by
  simpa [drawingPlanarSATCarrierLensIncidenceDrawing,
    EqualityLink.lensDrawing, placedEqualityLensDrawing,
    EmbeddedCNFIncidenceDrawing.renameToImage,
    EmbeddedCNFIncidenceDrawing.rename] using
      axisEqualityLensRoutes_singletonSplices_crossSuffixes_strictlyAvoid
        (CarrierNode.position formula.incidenceGraph link.first)
        (AxisDirection.between
          (CarrierNode.position formula.incidenceGraph link.first)
          (CarrierNode.position formula.incidenceGraph link.second))
        (AxisDirection.axisSpan
          (CarrierNode.position formula.incidenceGraph link.first)
          (CarrierNode.position formula.incidenceGraph link.second))
        geometry.spanLarge clauseIndex
        firstLiteralIndex secondLiteralIndex
        indicesDifferent secondLiteralIndexLt
        firstTerminal secondTerminal firstSlot secondSlot
        firstLength secondLength firstClassified secondClassified
        firstEscapeFits singletonPrefix
        firstSuffix secondSuffix
        firstSuffixBounded secondSuffixBounded

end PeriodicEightOccurrenceSplit
end LeanTrominoes
