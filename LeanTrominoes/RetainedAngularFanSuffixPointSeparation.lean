import LeanTrominoes.RetainedAngularFanSourceSpliceBounds
import LeanTrominoes.RetainedRayRasterizationSeparation

/-!
# Separating a Figure 7 suffix from another source neighborhood

Every retained Figure 7 spoke lies in a radius-96 box around its canonical
source center.  Distinct integral source centers are at least one unit apart,
and the factor-288 Figure 7 refinement leaves enough clearance between the
two radius-96 boxes.  This file packages that observation for the mixed
copied-source/implication-cycle planarity proof.
-/

namespace LeanTrominoes
namespace PeriodicEightOccurrenceSplit

open OccurrenceSplitRing
open PeriodicEightOccurrenceSplitPositioned
open PeriodicThreeSATThree
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing

/-- Routes confined to equal-radius neighborhoods of two distinct integral
points are strictly separated after a sufficiently large common scaling. -/
theorem
    routesStrictlyAvoidEachOther_of_distinct_scaledPointNeighborhoods
    {first second : List Cell}
    {firstCenter secondCenter : Cell}
    {factor radius : Nat}
    (centersDifferent : firstCenter ≠ secondCenter)
    (factorPositive : 0 < factor)
    (clearance : 2 * radius < factor)
    (firstBounded :
      ∀ point ∈ first,
        InClosedGridRectangle
          (coordinateRadiusLower radius
            (Cell.scale factor firstCenter))
          (coordinateRadiusUpper radius
            (Cell.scale factor firstCenter))
          point)
    (secondBounded :
      ∀ point ∈ second,
        InClosedGridRectangle
          (coordinateRadiusLower radius
            (Cell.scale factor secondCenter))
          (coordinateRadiusUpper radius
            (Cell.scale factor secondCenter))
          point) :
    RoutesStrictlyAvoidEachOther first second := by
  apply
    routesStrictlyAvoidEachOther_of_inSeparatedClosedGridRectangles
      (firstLower :=
        coordinateRadiusLower radius
          (Cell.scale factor firstCenter))
      (firstUpper :=
        coordinateRadiusUpper radius
          (Cell.scale factor firstCenter))
      (secondLower :=
        coordinateRadiusLower radius
          (Cell.scale factor secondCenter))
      (secondUpper :=
        coordinateRadiusUpper radius
          (Cell.scale factor secondCenter))
  · exact firstBounded
  · exact secondBounded
  · exact
      ClosedGridRectanglesSeparated.scale_both_coordinateRadius
        (closedGridSingletons_separated_of_ne centersDifferent)
        factorPositive clearance

/-- A retained Figure 7 suffix strictly avoids every route in the standard
radius-96 neighborhood of a different scaled source point. -/
theorem
    scaledAngularOccurrenceSuffix_strictlyAvoids_otherPointNeighborhood
    {Variable : Type*} [DecidableEq Variable]
    {source : PositionedPeriodicCNF Variable}
    (sourcePlacement : PeriodicVariablePlacement Variable)
    (order : OccurrenceOrder source.erase)
    (clause : PositionedPeriodicClause Variable)
    (literal : PeriodicLiteral Variable)
    (clauseIndex literalIndex : Nat)
    (target : Cell)
    (centersDifferent :
      PositionedPeriodicCNF.canonicalLiteralPosition
          sourcePlacement clause literal ≠
        target)
    (nearby : List Cell)
    (nearbyBounded :
      ∀ point ∈ nearby,
        InClosedGridRectangle
          (coordinateRadiusLower 96
            (Cell.scale
              (retainedTerminalFanRoutingRefinement *
                PeriodicEightOccurrenceSplitPositioned.refinementScale)
              target))
          (coordinateRadiusUpper 96
            (Cell.scale
              (retainedTerminalFanRoutingRefinement *
                PeriodicEightOccurrenceSplitPositioned.refinementScale)
              target))
          point) :
    RoutesStrictlyAvoidEachOther
      (scalePolyline retainedTerminalFanRoutingRefinement
        (angularOccurrenceSuffix sourcePlacement order
          clause literal clauseIndex literalIndex))
      nearby := by
  apply
    routesStrictlyAvoidEachOther_of_distinct_scaledPointNeighborhoods
      (firstCenter :=
        PositionedPeriodicCNF.canonicalLiteralPosition
          sourcePlacement clause literal)
      (secondCenter := target)
      (factor := 288)
      (radius := 96)
      centersDifferent
  · native_decide
  · native_decide
  · intro point pointMember
    simpa [retainedTerminalFanRoutingRefinement,
      PeriodicEightOccurrenceSplitPositioned.refinementScale] using
      scaledAngularOccurrenceSuffix_point_in_centerRectangle
        sourcePlacement order clause literal
        clauseIndex literalIndex pointMember
  · simpa [retainedTerminalFanRoutingRefinement,
      PeriodicEightOccurrenceSplitPositioned.refinementScale] using
      nearbyBounded

end PeriodicEightOccurrenceSplit
end LeanTrominoes
