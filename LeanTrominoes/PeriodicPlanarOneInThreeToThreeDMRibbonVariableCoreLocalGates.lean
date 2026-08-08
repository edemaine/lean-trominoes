import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableCoordinatedFans

/-!
# Variable-site cores versus coordinated ribbon gates

The finite variable-site drawing ends routed incidences at connector ports,
while the coordinated ribbon construction starts its local gates at those
same ports.  This module checks the exact interface between the two finite
tables.  Every site route and every active local gate have disjoint segment
interiors and mutually avoid the other route's segment interiors.  The
colored site route selected for a gate has the stronger endpoint-permitting
separation certificate: its only listed contact with the gate is their
advertised splice port.

These statements are independent of the outer fan direction.  They are
therefore checked over just the one-, two-, and three-module variable-site
configurations and then packaged for `VariableRibbonFanData`.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- The three continuous-separation fields used by periodic continuous
planarity, without imposing any condition on listed point-to-point
contacts. -/
def RoutesAvoidInteriorContacts
    (first second : List Cell) : Prop :=
  SegmentInteriorsDisjoint first second ∧
    RoutePointsAvoidInteriors first second ∧
    RoutePointsAvoidInteriors second first

instance (first second : List Cell) :
    Decidable (RoutesAvoidInteriorContacts first second) := by
  unfold RoutesAvoidInteriorContacts
  infer_instance

/-- Every route in a complete one-, two-, or three-module variable site
avoids the continuous interiors of every active local gate, in both
directions. -/
theorem variableSiteRoute_avoids_standardVariableLocalGateRoute :
    ∀ (countPred : Fin 3)
      (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      (slot : VariableSiteSlot),
      ∀ (_active : slot.index < countPred + 1)
        (triple : ActiveVariableSiteTriple (countPred + 1) kind)
        (routeColor gateColor : WireColor),
        RoutesAvoidInteriorContacts
          (translatePolyline standardThreeStrandLayout.variableOffset
            ((variableSiteDrawing (countPred + 1) kind polarity).route
              triple routeColor))
          (standardVariableLocalGateRoute
            slot (kind slot) (polarity slot) gateColor) := by
  native_decide

/-- The finite variable-site route selected for an active gate has
endpoint-permitting continuous separation from that gate. -/
theorem routedVariableSiteRoute_avoids_standardVariableLocalGateRoute :
    ∀ (countPred : Fin 3)
      (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      (slot : VariableSiteSlot),
      ∀ (active : slot.index < countPred + 1),
        ∀ (gateColor : WireColor),
          RoutesAvoidEachOther
            (translatePolyline standardThreeStrandLayout.variableOffset
              ((variableSiteDrawing (countPred + 1) kind polarity).route
                ⟨(VariableRibbonFanData.routedTriple
                    ⟨countPred, kind, polarity, fun _ => .invalid⟩
                    slot gateColor),
                  VariableRibbonFanData.routedTriple_matches
                    ⟨countPred, kind, polarity, fun _ => .invalid⟩
                    slot active gateColor⟩
                gateColor))
            (standardVariableLocalGateRoute
              slot (kind slot) (polarity slot) gateColor) := by
  native_decide

namespace VariableRibbonFanData

/-- Data-packaged form of the complete core-to-gate interior-avoidance
interface. -/
theorem variableSiteRoute_avoids_localGateRoute
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (triple : ActiveVariableSiteTriple data.count data.kind)
    (routeColor gateColor : WireColor) :
    RoutesAvoidInteriorContacts
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          triple routeColor))
      (standardVariableLocalGateRoute
        slot (data.kind slot) (data.polarity slot) gateColor) := by
  exact variableSiteRoute_avoids_standardVariableLocalGateRoute
    data.countPred data.kind data.polarity slot active
    triple routeColor gateColor

/-- Data-packaged form of the advertised core-to-gate splice interface. -/
theorem routedVariableSiteRoute_avoids_localGateRoute
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (gateColor : WireColor) :
    RoutesAvoidEachOther
      (translatePolyline standardThreeStrandLayout.variableOffset
        ((variableSiteDrawing data.count data.kind data.polarity).route
          (data.activeRoutedTriple slot active gateColor) gateColor))
      (standardVariableLocalGateRoute
        slot (data.kind slot) (data.polarity slot) gateColor) := by
  exact routedVariableSiteRoute_avoids_standardVariableLocalGateRoute
    data.countPred data.kind data.polarity slot active
    gateColor

end VariableRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
