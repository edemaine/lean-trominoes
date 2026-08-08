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

end VariableRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
