import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoreLocalGates
import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoordinatedFans
import LeanTrominoes.OrthogonalPolylineTailReplacementSeparation

/-!
# Variable-site cores versus complete coordinated ribbon fans

The finite variable-site drawing lies inside the protected center of a
ribbon macrocell, while the physical-lane outer route selected for a routed
incidence stays in the safe frame around that center.  This file checks that
exact finite interface and combines it with the core-to-local-gate interface.

For the routed triple and color, the complete variable-site route and the
complete coordinated fan route can consequently be joined without creating
any additional continuous contact.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

namespace VariableRibbonFanData

/-- Every route in every finite variable-site table lies in the protected
central rectangle. -/
theorem all_variableSiteRoute_points_in_coreRectangle :
    ∀ (countPred : Fin 3)
      (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      (triple : ActiveVariableSiteTriple (countPred + 1) kind)
      (color : WireColor) (point : Cell),
      point ∈
          translatePolyline standardThreeStrandLayout.variableOffset
            ((variableSiteDrawing (countPred + 1) kind polarity).route
              triple color) →
        InClosedGridRectangle (11, 48) (109, 107) point := by
  native_decide

/-- A route in the protected central rectangle is strictly separated from
an outer route whose points and segments remain in the four-arm safe frame. -/
theorem routesStrictlyAvoidEachOther_of_coreRectangle_outerSafeFrame
    {core outer : List Cell}
    (coreBounded :
      ∀ point ∈ core,
        InClosedGridRectangle (11, 48) (109, 107) point)
    (outerBounded :
      ∀ point ∈ outer, VariableOuterFanData.InOuterSafeFrame point)
    (outerSegments :
      ∀ segment ∈ gridPolylineSegments outer,
        VariableOuterFanData.OuterSafeFrameSegment segment) :
    RoutesStrictlyAvoidEachOther core outer := by
  have upperSeparated :
      ClosedGridRectanglesSeparated
        (11, 48) (109, 107) (0, 108) (128, 128) := by decide
  have leftSeparated :
      ClosedGridRectanglesSeparated
        (11, 48) (109, 107) (0, 0) (10, 128) := by decide
  have rightSeparated :
      ClosedGridRectanglesSeparated
        (11, 48) (109, 107) (110, 0) (128, 128) := by decide
  have lowerSeparated :
      ClosedGridRectanglesSeparated
        (11, 48) (109, 107) (0, 0) (128, 46) := by decide
  unfold RoutesStrictlyAvoidEachOther
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro coreSegment coreMember outerSegment outerMember
    have coreEndpoints := gridPolylineSegments_endpoints_mem coreMember
    rcases outerSegments outerSegment outerMember with
      upper | left | right | lower
    · exact not_interiorsMeet_of_inClosedGridRectangles_of_separated
        (coreBounded _ coreEndpoints.1)
        (coreBounded _ coreEndpoints.2) upper.1 upper.2 upperSeparated
    · exact not_interiorsMeet_of_inClosedGridRectangles_of_separated
        (coreBounded _ coreEndpoints.1)
        (coreBounded _ coreEndpoints.2) left.1 left.2 leftSeparated
    · exact not_interiorsMeet_of_inClosedGridRectangles_of_separated
        (coreBounded _ coreEndpoints.1)
        (coreBounded _ coreEndpoints.2) right.1 right.2 rightSeparated
    · exact not_interiorsMeet_of_inClosedGridRectangles_of_separated
        (coreBounded _ coreEndpoints.1)
        (coreBounded _ coreEndpoints.2) lower.1 lower.2 lowerSeparated
  · intro corePoint coreMember outerSegment outerMember
    rcases outerSegments outerSegment outerMember with
      upper | left | right | lower
    · exact not_interiorContains_of_inClosedGridRectangles_of_separated
        (coreBounded _ coreMember) upper.1 upper.2 upperSeparated
    · exact not_interiorContains_of_inClosedGridRectangles_of_separated
        (coreBounded _ coreMember) left.1 left.2 leftSeparated
    · exact not_interiorContains_of_inClosedGridRectangles_of_separated
        (coreBounded _ coreMember) right.1 right.2 rightSeparated
    · exact not_interiorContains_of_inClosedGridRectangles_of_separated
        (coreBounded _ coreMember) lower.1 lower.2 lowerSeparated
  · intro outerPoint outerMember coreSegment coreMember
    have coreEndpoints := gridPolylineSegments_endpoints_mem coreMember
    rcases outerBounded outerPoint outerMember with
      upper | left | right | lower
    · exact not_interiorContains_of_inClosedGridRectangles_of_separated
        upper (coreBounded _ coreEndpoints.1)
        (coreBounded _ coreEndpoints.2) upperSeparated.symm
    · exact not_interiorContains_of_inClosedGridRectangles_of_separated
        left (coreBounded _ coreEndpoints.1)
        (coreBounded _ coreEndpoints.2) leftSeparated.symm
    · exact not_interiorContains_of_inClosedGridRectangles_of_separated
        right (coreBounded _ coreEndpoints.1)
        (coreBounded _ coreEndpoints.2) rightSeparated.symm
    · exact not_interiorContains_of_inClosedGridRectangles_of_separated
        lower (coreBounded _ coreEndpoints.1)
        (coreBounded _ coreEndpoints.2) lowerSeparated.symm
  · intro corePoint coreMember outerPoint outerMember
    rcases outerBounded outerPoint outerMember with
      upper | left | right | lower
    · exact ne_of_inClosedGridRectangles_of_separated
        (coreBounded _ coreMember) upper upperSeparated
    · exact ne_of_inClosedGridRectangles_of_separated
        (coreBounded _ coreMember) left leftSeparated
    · exact ne_of_inClosedGridRectangles_of_separated
        (coreBounded _ coreMember) right rightSeparated
    · exact ne_of_inClosedGridRectangles_of_separated
        (coreBounded _ coreMember) lower lowerSeparated

/-- Every finite variable-site route is contact-free from every selected
physical-lane outer route. -/
theorem variableSiteRoute_strictlyAvoids_outerRoute
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (triple : ActiveVariableSiteTriple data.count data.kind)
    (routeColor gateColor : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          triple routeColor))
      (data.outerData.outerRoute slot
        ((data.kind slot).ribbonLaneForColor gateColor)) := by
  apply routesStrictlyAvoidEachOther_of_coreRectangle_outerSafeFrame
  · exact all_variableSiteRoute_points_in_coreRectangle
      data.countPred data.kind data.polarity triple routeColor
  · exact data.outerData.outerRoute_points_in_safeFrame
      compatible slot active
      ((data.kind slot).ribbonLaneForColor gateColor)
  · exact data.outerData.outerRoute_segments_in_safeFrame
      compatible slot active
      ((data.kind slot).ribbonLaneForColor gateColor)

/-- Every finite variable-site route avoids the segment interiors of every
complete coordinated fan route.  Listed-point contacts with a nonmatching
local gate are harmless here and are intentionally retained. -/
theorem variableSiteRoute_avoids_coordinatedRouteInteriors
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (triple : ActiveVariableSiteTriple data.count data.kind)
    (routeColor gateColor : WireColor) :
    RoutesAvoidInteriorContacts
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          triple routeColor))
      (data.coordinatedRoute slot gateColor) := by
  apply RoutesAvoidInteriorContacts.join_right
    (data.variableSiteRoute_avoids_localGateRoute
      slot active triple routeColor gateColor)
    (RoutesStrictlyAvoidEachOther.toRoutesAvoidInteriorContacts
      (data.variableSiteRoute_strictlyAvoids_outerRoute
        compatible slot active triple routeColor gateColor))
  · exact standardVariableLocalGateRoute_getLast?
      slot (data.kind slot) (data.polarity slot) gateColor
  · exact data.outerData.outerRoute_head?
      compatible slot active
      ((data.kind slot).ribbonLaneForColor gateColor)

/-- The finite variable-site route selected by a colored occurrence is
contact-free from the matching physical-lane outer route. -/
theorem routedVariableSiteRoute_strictlyAvoids_outerRoute
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) :
    RoutesStrictlyAvoidEachOther
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          (data.activeRoutedTriple slot active color) color))
      (data.outerData.outerRoute slot
        ((data.kind slot).ribbonLaneForColor color)) := by
  native_decide +revert

/-- The finite variable-site route selected by a colored occurrence avoids
the entire coordinated local-plus-outer fan route for that occurrence. -/
theorem routedVariableSiteRoute_avoids_coordinatedRoute
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) :
    RoutesAvoidEachOther
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          (data.activeRoutedTriple slot active color) color))
      (data.coordinatedRoute slot color) := by
  apply RoutesAvoidEachOther.join_right_of_strict_suffix
    (data.routedVariableSiteRoute_avoids_localGateRoute
      slot active color)
    (data.routedVariableSiteRoute_strictlyAvoids_outerRoute
      compatible slot active color)
  · exact standardVariableLocalGateRoute_getLast?
      slot (data.kind slot) (data.polarity slot) color
  · exact data.outerData.outerRoute_head?
      compatible slot active
      ((data.kind slot).ribbonLaneForColor color)

/-- The advertised variable port is the only listed point shared by the
routed finite variable-site route and its complete coordinated fan. -/
theorem routedVariableSiteRoute_coordinatedRoute_only_common
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor)
    (point : Cell)
    (coreMember :
      point ∈
        translatePolyline standardThreeStrandLayout.variableOffset
          ((variableSiteDrawing data.count data.kind data.polarity).route
            (data.activeRoutedTriple slot active color) color))
    (fanMember : point ∈ data.coordinatedRoute slot color) :
    point = data.port slot active color := by
  native_decide +revert

end VariableRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
