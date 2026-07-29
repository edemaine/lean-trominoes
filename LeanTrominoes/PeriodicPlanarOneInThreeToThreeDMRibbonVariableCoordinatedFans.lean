import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableOuterFans

/-!
# Complete coordinated variable-side ribbon fans

This file joins the connector-dependent local gate routes to the cyclic
outer-fan tables.  The only source-level premise is that the active
occurrence directions appear in one of the 28 clockwise boundary orders.

Finite checking establishes the interface between the two table families:
an outer route meets its own local route only at their common gate and
strictly avoids every other local route.  The generic join lemmas then prove
that complete variable stubs belonging to distinct RGB strands are strictly
separated.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-! ## Finite interface between the two route tables -/

/-- Every selected outer route avoids the local gate route with which it is
joined; their advertised common gate is the only possible contact. -/
theorem standardVariableLocalGateRoute_avoids_outerRoute :
    ∀ (outer : VariableOuterFanData),
      outer.IsClockwiseCompatible →
      ∀ localSlot outerSlot,
        outer.SlotActive localSlot →
        outer.SlotActive outerSlot →
        ∀ kind polarity localColor outerColor,
          RoutesAvoidEachOther
            (standardVariableLocalGateRoute
              localSlot kind polarity localColor)
            (outer.outerRoute outerSlot outerColor) := by
  native_decide

/-- If the strands differ, the local and outer table pieces have no contact
at all. -/
theorem standardVariableLocalGateRoute_strictlyAvoids_outerRoute :
    ∀ (outer : VariableOuterFanData),
      outer.IsClockwiseCompatible →
      ∀ localSlot outerSlot,
        outer.SlotActive localSlot →
        outer.SlotActive outerSlot →
        ∀ kind polarity localColor outerColor,
          (localSlot, localColor) ≠ (outerSlot, outerColor) →
          RoutesStrictlyAvoidEachOther
            (standardVariableLocalGateRoute
              localSlot kind polarity localColor)
            (outer.outerRoute outerSlot outerColor) := by
  native_decide

/-- Each complete finite local-plus-outer route is geometrically simple. -/
theorem joinedVariableGateOuterRoute_simple :
    ∀ (outer : VariableOuterFanData),
      outer.IsClockwiseCompatible →
      ∀ slot, outer.SlotActive slot →
        ∀ kind polarity color,
          LocalIncidenceDrawing.RouteIsSimple
            (joinAtEndpoint
              (standardVariableLocalGateRoute
                slot kind polarity color)
              (outer.outerRoute slot color)) := by
  native_decide

namespace VariableRibbonFanData

/-- Direction-only projection used by the finite outer routing table. -/
def outerData
    (data : VariableRibbonFanData) : VariableOuterFanData :=
  VariableOuterFanData.ofVariableRibbonFanData data

/-- Whether this full connector configuration has the cyclic direction
order required by the outer routing table. -/
def IsClockwiseCompatible
    (data : VariableRibbonFanData) : Prop :=
  data.outerData.IsClockwiseCompatible

instance (data : VariableRibbonFanData) :
    Decidable data.IsClockwiseCompatible := by
  unfold IsClockwiseCompatible
  infer_instance

@[simp]
theorem outerData_slotActive
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot) :
    data.outerData.SlotActive slot ↔
      data.SlotActive slot := by
  rfl

/-- Complete standard-macrocell variable route from an exact finite-gadget
port to the corresponding colored ribbon exit. -/
def coordinatedRoute
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (color : WireColor) : List Cell :=
  joinAtEndpoint
    (standardVariableLocalGateRoute
      slot (data.kind slot) (data.polarity slot) color)
    (data.outerData.outerRoute slot color)

/-- The joined route begins at the exact selected connector port. -/
@[simp]
theorem coordinatedRoute_head?
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) :
    (data.coordinatedRoute slot color).head? =
      some (data.port slot active color) := by
  apply joinAtEndpoint_head?
  exact data.localGateRoute_head? slot active color

/-- Under the cyclic-order premise, the joined route ends at the exact
direction-dependent ribbon exit. -/
@[simp]
theorem coordinatedRoute_getLast?
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) :
    (data.coordinatedRoute slot color).getLast? =
      some
        (standardRibbonMacrocellExit
          (data.direction slot) color) := by
  apply joinAtEndpoint_getLast?
  · exact standardVariableLocalGateRoute_getLast?
      slot (data.kind slot) (data.polarity slot) color
  · exact VariableOuterFanData.outerRoute_head?
      data.outerData compatible slot active color
  · exact VariableOuterFanData.outerRoute_getLast?
      data.outerData compatible slot active color

/-- Every complete coordinated variable route is rectilinear. -/
theorem coordinatedRoute_orthogonal
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) :
    OrthogonalPolyline (data.coordinatedRoute slot color) := by
  apply
    (standardVariableLocalGateRoute_orthogonal
      slot (data.kind slot) (data.polarity slot) color).joinAtEndpoint
  · exact VariableOuterFanData.outerRoute_orthogonal
      data.outerData compatible slot active color
  · exact standardVariableLocalGateRoute_getLast?
      slot (data.kind slot) (data.polarity slot) color
  · exact VariableOuterFanData.outerRoute_head?
      data.outerData compatible slot active color

/-- Every listed point of a complete coordinated variable route remains in
the standard ribbon macrocell. -/
theorem coordinatedRoute_points_bounded
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor)
    {point : Cell}
    (member : point ∈ data.coordinatedRoute slot color) :
    InStandardRibbonMacrocell point := by
  rcases mem_joinAtEndpoint member with localMember | outerMember
  · exact standardVariableLocalGateRoute_points_bounded
      slot (data.kind slot) (data.polarity slot)
      color point localMember
  · exact VariableOuterFanData.outerRoute_points_bounded
      data.outerData compatible
      slot active color point outerMember

/-- Each complete coordinated variable route is geometrically simple. -/
theorem coordinatedRoute_simple
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) :
    LocalIncidenceDrawing.RouteIsSimple
      (data.coordinatedRoute slot color) := by
  exact joinedVariableGateOuterRoute_simple
    data.outerData compatible slot active
    (data.kind slot) (data.polarity slot) color

/-- Distinct active RGB strands in a complete coordinated variable fan have
no continuous or listed-point contact. -/
theorem coordinatedRoutes_strictlyAvoidEachOther
    (data : VariableRibbonFanData)
    (compatible : data.IsClockwiseCompatible)
    (firstSlot secondSlot : VariableSiteSlot)
    (firstActive : data.SlotActive firstSlot)
    (secondActive : data.SlotActive secondSlot)
    (firstColor secondColor : WireColor)
    (different :
      (firstSlot, firstColor) ≠ (secondSlot, secondColor)) :
    RoutesStrictlyAvoidEachOther
      (data.coordinatedRoute firstSlot firstColor)
      (data.coordinatedRoute secondSlot secondColor) := by
  let outer := data.outerData
  have localLocal :
      RoutesStrictlyAvoidEachOther
        (standardVariableLocalGateRoute
          firstSlot (data.kind firstSlot)
          (data.polarity firstSlot) firstColor)
        (standardVariableLocalGateRoute
          secondSlot (data.kind secondSlot)
          (data.polarity secondSlot) secondColor) :=
    standardVariableLocalGateRoutes_strictlyAvoidEachOther
      data.kind data.polarity
      firstSlot firstColor secondSlot secondColor different
  have localOuter :
      RoutesStrictlyAvoidEachOther
        (standardVariableLocalGateRoute
          firstSlot (data.kind firstSlot)
          (data.polarity firstSlot) firstColor)
        (outer.outerRoute secondSlot secondColor) :=
    standardVariableLocalGateRoute_strictlyAvoids_outerRoute
      outer compatible firstSlot secondSlot
      firstActive secondActive
      (data.kind firstSlot) (data.polarity firstSlot)
      firstColor secondColor different
  have outerLocal :
      RoutesStrictlyAvoidEachOther
        (outer.outerRoute firstSlot firstColor)
        (standardVariableLocalGateRoute
          secondSlot (data.kind secondSlot)
          (data.polarity secondSlot) secondColor) :=
    (standardVariableLocalGateRoute_strictlyAvoids_outerRoute
      outer compatible secondSlot firstSlot
      secondActive firstActive
      (data.kind secondSlot) (data.polarity secondSlot)
      secondColor firstColor
      (Ne.symm different)).symm
  have outerOuter :
      RoutesStrictlyAvoidEachOther
        (outer.outerRoute firstSlot firstColor)
        (outer.outerRoute secondSlot secondColor) :=
    outer.outerRoutes_strictlyAvoidEachOther
      compatible firstSlot secondSlot
      firstActive secondActive
      firstColor secondColor different
  have firstJoinedAvoidsSecondLocal :=
    localLocal.join_left outerLocal
      (standardVariableLocalGateRoute_getLast?
        firstSlot (data.kind firstSlot)
        (data.polarity firstSlot) firstColor)
      (outer.outerRoute_head?
        compatible firstSlot firstActive firstColor)
  have firstJoinedAvoidsSecondOuter :=
    localOuter.join_left outerOuter
      (standardVariableLocalGateRoute_getLast?
        firstSlot (data.kind firstSlot)
        (data.polarity firstSlot) firstColor)
      (outer.outerRoute_head?
        compatible firstSlot firstActive firstColor)
  exact
    firstJoinedAvoidsSecondLocal.join_right
      firstJoinedAvoidsSecondOuter
      (standardVariableLocalGateRoute_getLast?
        secondSlot (data.kind secondSlot)
        (data.polarity secondSlot) secondColor)
      (outer.outerRoute_head?
        compatible secondSlot secondActive secondColor)

end VariableRibbonFanData
end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
