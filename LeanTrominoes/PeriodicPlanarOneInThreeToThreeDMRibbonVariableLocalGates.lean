import LeanTrominoes.PeriodicPlanarOneInThreeToThreeDMRibbonVariableFanFinite

/-!
# Coordinated variable-port gates

The exact RGB connector ports of a variable occurrence have six possible
local patterns: three connector kinds and two polarities.  This file routes
each pattern to the same three gates above its occurrence module.  The
tables were chosen together, so unlike the old independent elbows, their
three routes are continuously disjoint.

Every route for slot `s` is a translation by `32 * s` of one finite table.
The tables for adjacent slots occupy disjoint vertical strips.  Consequently
all active occurrence colors reach a common, kind-independent interface:

* red at `(20 + 32s, 108)`;
* green at `(24 + 32s, 108)`; and
* blue at `(28 + 32s, 108)`.

A later finite construction connects these gates to the direction-dependent
ribbon-macrocell boundary.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- Kind-independent gate above one occurrence module. -/
def standardVariableOuterGate
    (slot : VariableSiteSlot)
    (color : WireColor) : Cell :=
  Cell.add (variableModuleOrigin slot) <|
    match color with
    | .red => (20, 108)
    | .green => (24, 108)
    | .blue => (28, 108)

/-- Coordinated route from one slot-zero connector port to its standardized
outer gate.  All coordinates are even, except where a unit-width private
track is useful to preserve order. -/
def standardVariableLocalGateRouteAtFirst
    (kind : VariableConnectorKind)
    (polarity : Bool)
    (color : WireColor) : List Cell :=
  match kind, polarity, color with
  | .fixedRed, false, .red =>
      [(32, 76), (20, 76), (20, 108)]
  | .fixedRed, false, .green =>
      [(22, 80), (24, 80), (24, 108)]
  | .fixedRed, false, .blue =>
      [(26, 80), (28, 80), (28, 108)]
  | .fixedRed, true, .red =>
      [(24, 76), (24, 98), (22, 98), (22, 100),
        (20, 100), (20, 108)]
  | .fixedRed, true, .green =>
      [(34, 80), (34, 98), (26, 98), (26, 100),
        (24, 100), (24, 108)]
  | .fixedRed, true, .blue =>
      [(30, 80), (32, 80), (32, 78), (36, 78),
        (36, 100), (28, 100), (28, 108)]
  | .fixedGreen, false, .red =>
      [(16, 64), (20, 64), (20, 108)]
  | .fixedGreen, false, .green =>
      [(32, 72), (32, 98), (26, 98), (26, 100),
        (24, 100), (24, 108)]
  | .fixedGreen, false, .blue =>
      [(16, 72), (14, 72), (14, 62), (34, 62),
        (34, 100), (28, 100), (28, 108)]
  | .fixedGreen, true, .red =>
      [(40, 64), (20, 64), (20, 108)]
  | .fixedGreen, true, .green =>
      [(24, 72), (24, 108)]
  | .fixedGreen, true, .blue =>
      [(40, 72), (28, 72), (28, 108)]
  | .fixedBlue, false, .red =>
      [(16, 64), (20, 64), (20, 108)]
  | .fixedBlue, false, .green =>
      [(16, 72), (14, 72), (14, 62), (24, 62),
        (24, 108)]
  | .fixedBlue, false, .blue =>
      [(32, 72), (32, 100), (28, 100), (28, 108)]
  | .fixedBlue, true, .red =>
      [(40, 64), (20, 64), (20, 108)]
  | .fixedBlue, true, .green =>
      [(40, 72), (26, 72), (26, 74), (24, 74),
        (24, 108)]
  | .fixedBlue, true, .blue =>
      [(24, 72), (24, 70), (42, 70), (42, 74),
        (28, 74), (28, 108)]

/-- Translate the six slot-zero tables to an arbitrary occurrence slot. -/
def standardVariableLocalGateRoute
    (slot : VariableSiteSlot)
    (kind : VariableConnectorKind)
    (polarity : Bool)
    (color : WireColor) : List Cell :=
  translatePolyline (variableModuleOrigin slot)
    (standardVariableLocalGateRouteAtFirst kind polarity color)

/-- Every local gate route ends at the standardized gate. -/
@[simp]
theorem standardVariableLocalGateRoute_getLast?
    (slot : VariableSiteSlot)
    (kind : VariableConnectorKind)
    (polarity : Bool)
    (color : WireColor) :
    (standardVariableLocalGateRoute
      slot kind polarity color).getLast? =
        some (standardVariableOuterGate slot color) := by
  cases slot <;> cases kind <;> cases polarity <;> cases color <;>
    native_decide

/-- Every local gate table is rectilinear. -/
theorem standardVariableLocalGateRoute_orthogonal
    (slot : VariableSiteSlot)
    (kind : VariableConnectorKind)
    (polarity : Bool)
    (color : WireColor) :
    OrthogonalPolyline
      (standardVariableLocalGateRoute
        slot kind polarity color) := by
  apply OrthogonalPolyline.translate
  cases kind <;> cases polarity <;> cases color <;>
    simp [standardVariableLocalGateRouteAtFirst,
      OrthogonalPolyline, GridSegment.IsAxisAligned,
      GridSegment.IsHorizontal, GridSegment.IsVertical]

/-- Every listed gate-route point stays in the standard ribbon macrocell. -/
theorem standardVariableLocalGateRoute_points_bounded :
    ∀ slot kind polarity color point,
      point ∈ standardVariableLocalGateRoute
        slot kind polarity color →
      InStandardRibbonMacrocell point := by
  native_decide

/-- Selecting one pattern independently in every slot still gives a
pairwise contact-free family of local gate routes. -/
theorem standardVariableLocalGateRoutes_strictlyAvoidEachOther :
    ∀ (kind : VariableSiteSlot → VariableConnectorKind)
      (polarity : VariableSiteSlot → Bool)
      firstSlot firstColor secondSlot secondColor,
      (firstSlot, firstColor) ≠ (secondSlot, secondColor) →
      RoutesStrictlyAvoidEachOther
        (standardVariableLocalGateRoute
          firstSlot (kind firstSlot)
          (polarity firstSlot) firstColor)
        (standardVariableLocalGateRoute
          secondSlot (kind secondSlot)
          (polarity secondSlot) secondColor) := by
  native_decide

/-- The first point of the selected gate table is exactly the finite-gadget
port in every active finite variable configuration. -/
theorem VariableRibbonFanData.localGateRoute_head?
    (data : VariableRibbonFanData)
    (slot : VariableSiteSlot)
    (active : data.SlotActive slot)
    (color : WireColor) :
    (standardVariableLocalGateRoute
      slot (data.kind slot) (data.polarity slot) color).head? =
        some (data.port slot active color) := by
  native_decide +revert

end PeriodicPlanarOneInThreeToThreeDM
end LeanTrominoes
