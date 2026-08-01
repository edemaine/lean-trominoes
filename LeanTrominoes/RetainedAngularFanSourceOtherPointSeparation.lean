import LeanTrominoes.RetainedAngularFanSourceEscapedSplicePointSeparation
import LeanTrominoes.RetainedAngularFanSuffixPointSeparation

/-!
# Separating completed source splices from another source neighborhood

The source-side boundary splice already has a point-neighborhood separation
certificate.  When the scaled source route is orthogonal, retained-ray
rasterization is the identity, so that certificate applies to the public
boundary route.  A Figure 7 suffix centered at a different source point is
strictly separated by the factor-288 macrocell clearance.  Joining these two
pieces gives the corresponding certificate for a completed ordinary or
escaped copied-source occurrence route.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplitPositioned
open PeriodicOrthocrossing
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- The rasterized ordinary source boundary inherits the point-neighborhood
separation of its pre-rasterized polyline when the scaled source is already
orthogonal. -/
theorem
    retainedAngularFanSourceScaledSplicedBoundaryRoute_strictlyAvoids_pointNeighborhood
    {factor : Nat}
    (factorPositive : 0 < factor)
    (clearance :
      2 * 288 <
        retainedTerminalFanTotalRefinement * factor)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      OrthogonalPolyline (scalePolyline factor route))
    (target : Cell)
    (prefixPointsAvoid :
      ∀ point ∈ route.dropLast, point ≠ target)
    (prefixSegmentsAvoid :
      ∀ segment ∈ gridPolylineSegments route.dropLast,
        segment.IsAxisAligned →
          ¬segment.Contains target)
    (finalAligned :
      (⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned)
    (finalAvoidsTarget :
      ¬(⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ :
        GridSegment).Contains target)
    (nearby : List Cell)
    (nearbyBounded :
      ∀ point ∈ nearby,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              target))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              target))
          point) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanSplicedBoundaryRoute
        (scalePolyline factor route)
        (scaleRetainedTerminalData factor terminal)
        slot)
      nearby := by
  have polylineAvoid :=
    retainedAngularFanSourceScaledSplicedBoundaryPolyline_strictlyAvoids_pointNeighborhood
      factorPositive clearance route terminal slot
      routeLength classified target
      prefixPointsAvoid prefixSegmentsAvoid
      finalAligned finalAvoidsTarget nearby nearbyBounded
  have scaledLength :
      2 ≤ (scalePolyline factor route).length := by
    simpa [scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            (scalePolyline factor route)) =
        some (scaleRetainedTerminalData factor terminal) := by
    simpa using
      routeTerminalVector_scale_classified
        factorPositive classified
  have polylineOrthogonal :=
    retainedAngularFanSplicedBoundaryPolyline_orthogonal
      (scalePolyline factor route)
      (scaleRetainedTerminalData factor terminal)
      slot scaledLength scaledClassified routeOrthogonal
  simpa [retainedAngularFanSplicedBoundaryRoute,
    rasterizeRetainedPolyline_eq_of_orthogonal
      polylineOrthogonal] using polylineAvoid

/-- The rasterized escaped source boundary inherits the same
point-neighborhood certificate when its delayed lane fits. -/
theorem
    retainedAngularFanSourceScaledEscapedSplicedBoundaryRoute_strictlyAvoids_pointNeighborhood
    {factor : Nat}
    (factorPositive : 0 < factor)
    (clearance :
      2 * 288 <
        retainedTerminalFanTotalRefinement * factor)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      OrthogonalPolyline (scalePolyline factor route))
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor terminal))
    (target : Cell)
    (prefixPointsAvoid :
      ∀ point ∈ route.dropLast, point ≠ target)
    (prefixSegmentsAvoid :
      ∀ segment ∈ gridPolylineSegments route.dropLast,
        segment.IsAxisAligned →
          ¬segment.Contains target)
    (finalAligned :
      (⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned)
    (finalAvoidsTarget :
      ¬(⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ :
        GridSegment).Contains target)
    (nearby : List Cell)
    (nearbyBounded :
      ∀ point ∈ nearby,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              target))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              target))
          point) :
    RoutesStrictlyAvoidEachOther
      (retainedAngularFanEscapedSplicedBoundaryRoute
        (scalePolyline factor route)
        (scaleRetainedTerminalData factor terminal)
        slot)
      nearby := by
  have polylineAvoid :=
    retainedAngularFanSourceScaledEscapedSplicedBoundaryPolyline_strictlyAvoids_pointNeighborhood
      factorPositive clearance route terminal slot
      routeLength classified escapeFits target
      prefixPointsAvoid prefixSegmentsAvoid
      finalAligned finalAvoidsTarget nearby nearbyBounded
  have scaledLength :
      2 ≤ (scalePolyline factor route).length := by
    simpa [scalePolyline] using routeLength
  have scaledClassified :
      retainedTerminalDirectionClassify
          (routeTerminalVector
            (scalePolyline factor route)) =
        some (scaleRetainedTerminalData factor terminal) := by
    simpa using
      routeTerminalVector_scale_classified
        factorPositive classified
  have polylineOrthogonal :=
    retainedAngularFanEscapedSplicedBoundaryPolyline_orthogonal
      (scalePolyline factor route)
      (scaleRetainedTerminalData factor terminal)
      slot scaledLength scaledClassified routeOrthogonal
      escapeFits
  simpa [retainedAngularFanEscapedSplicedBoundaryRoute,
    rasterizeRetainedPolyline_eq_of_orthogonal
      polylineOrthogonal] using polylineAvoid

/-- Joining an ordinary copied-source boundary to its Figure 7 suffix
preserves strict separation from a bounded route centered at a different
source point. -/
theorem
    retainedAngularFanSourceScaledSplicedOccurrenceRoute_strictlyAvoids_otherPointNeighborhood
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    {factor : Nat}
    (factorPositive : 0 < factor)
    (clearance :
      2 * 288 <
        retainedTerminalFanTotalRefinement * factor)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      OrthogonalPolyline (scalePolyline factor route))
    (target : Cell)
    (prefixPointsAvoid :
      ∀ point ∈ route.dropLast, point ≠ target)
    (prefixSegmentsAvoid :
      ∀ segment ∈ gridPolylineSegments route.dropLast,
        segment.IsAxisAligned →
          ¬segment.Contains target)
    (finalAligned :
      (⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned)
    (finalAvoidsTarget :
      ¬(⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ :
        GridSegment).Contains target)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          sourcePlacement clause literal ≠
        Cell.scale factor target)
    (nearby : List Cell)
    (nearbyBounded :
      ∀ point ∈ nearby,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              target))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              target))
          point)
    (middle : Cell)
    (boundaryLast :
      (retainedAngularFanSplicedBoundaryRoute
        (scalePolyline factor route)
        (scaleRetainedTerminalData factor terminal)
        slot).getLast? = some middle)
    (suffixHead :
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix sourcePlacement order
          clause literal clauseIndex literalIndex)).head? =
        some middle) :
    RoutesStrictlyAvoidEachOther
      (joinAtEndpoint
        (retainedAngularFanSplicedBoundaryRoute
          (scalePolyline factor route)
          (scaleRetainedTerminalData factor terminal)
          slot)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix sourcePlacement order
            clause literal clauseIndex literalIndex)))
      nearby := by
  have boundaryAvoid :=
    retainedAngularFanSourceScaledSplicedBoundaryRoute_strictlyAvoids_pointNeighborhood
      factorPositive clearance route terminal slot
      routeLength classified routeOrthogonal target
      prefixPointsAvoid prefixSegmentsAvoid
      finalAligned finalAvoidsTarget nearby nearbyBounded
  have suffixAvoid :=
    scaledAngularOccurrenceSuffix_strictlyAvoids_otherPointNeighborhood
      sourcePlacement order clause literal
      clauseIndex literalIndex
      (Cell.scale factor target) centersDifferent
      nearby (by
        intro point pointMember
        simpa [retainedTerminalFanTotalRefinement_eq,
          retainedTerminalFanRoutingRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          Cell.scale_scale, Nat.cast_mul] using
          nearbyBounded point pointMember)
  exact
    boundaryAvoid.join_left suffixAvoid
      boundaryLast suffixHead

/-- The completed escaped copied-source occurrence satisfies the same
different-center neighborhood certificate. -/
theorem
    retainedAngularFanSourceScaledEscapedSplicedOccurrenceRoute_strictlyAvoids_otherPointNeighborhood
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    {factor : Nat}
    (factorPositive : 0 < factor)
    (clearance :
      2 * 288 <
        retainedTerminalFanTotalRefinement * factor)
    (route : List Cell)
    (terminal : RetainedTerminalData)
    (slot : RetainedTerminalSlot)
    (routeLength : 2 ≤ route.length)
    (classified :
      retainedTerminalDirectionClassify
          (routeTerminalVector route) =
        some terminal)
    (routeOrthogonal :
      OrthogonalPolyline (scalePolyline factor route))
    (escapeFits :
      retainedTerminalFanOuterSourceEscapeLength ≤
        retainedTerminalFanOuterRadialLength
          (scaleRetainedTerminalData factor terminal))
    (target : Cell)
    (prefixPointsAvoid :
      ∀ point ∈ route.dropLast, point ≠ target)
    (prefixSegmentsAvoid :
      ∀ segment ∈ gridPolylineSegments route.dropLast,
        segment.IsAxisAligned →
          ¬segment.Contains target)
    (finalAligned :
      (⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ :
        GridSegment).IsAxisAligned)
    (finalAvoidsTarget :
      ¬(⟨polylineLastEntrance route,
          route.getLastD (0, 0)⟩ :
        GridSegment).Contains target)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          sourcePlacement clause literal ≠
        Cell.scale factor target)
    (nearby : List Cell)
    (nearbyBounded :
      ∀ point ∈ nearby,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              target))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanTotalRefinement * factor)
              target))
          point)
    (middle : Cell)
    (boundaryLast :
      (retainedAngularFanEscapedSplicedBoundaryRoute
        (scalePolyline factor route)
        (scaleRetainedTerminalData factor terminal)
        slot).getLast? = some middle)
    (suffixHead :
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix sourcePlacement order
          clause literal clauseIndex literalIndex)).head? =
        some middle) :
    RoutesStrictlyAvoidEachOther
      (joinAtEndpoint
        (retainedAngularFanEscapedSplicedBoundaryRoute
          (scalePolyline factor route)
          (scaleRetainedTerminalData factor terminal)
          slot)
        (scalePolyline retainedTerminalFanRoutingRefinement
          (angularOccurrenceSuffix sourcePlacement order
            clause literal clauseIndex literalIndex)))
      nearby := by
  have boundaryAvoid :=
    retainedAngularFanSourceScaledEscapedSplicedBoundaryRoute_strictlyAvoids_pointNeighborhood
      factorPositive clearance route terminal slot
      routeLength classified routeOrthogonal escapeFits target
      prefixPointsAvoid prefixSegmentsAvoid
      finalAligned finalAvoidsTarget nearby nearbyBounded
  have suffixAvoid :=
    scaledAngularOccurrenceSuffix_strictlyAvoids_otherPointNeighborhood
      sourcePlacement order clause literal
      clauseIndex literalIndex
      (Cell.scale factor target) centersDifferent
      nearby (by
        intro point pointMember
        simpa [retainedTerminalFanTotalRefinement_eq,
          retainedTerminalFanRoutingRefinement,
          PeriodicEightOccurrenceSplitPositioned.refinementScale,
          Cell.scale_scale, Nat.cast_mul] using
          nearbyBounded point pointMember)
  exact
    boundaryAvoid.join_left suffixAvoid
      boundaryLast suffixHead

end PeriodicEightOccurrenceSplit
end LeanTrominoes
