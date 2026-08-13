/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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
all active occurrence colors reach a common physical-lane interface:

* the red lane at `(20 + 32s, 108)`;
* the green lane at `(24 + 32s, 108)`; and
* the blue lane at `(28 + 32s, 108)`.

A later finite construction connects these gates to the direction-dependent
ribbon-macrocell boundary.
-/

namespace LeanTrominoes
namespace PeriodicPlanarOneInThreeToThreeDM

open Gadget PlanarThreeDM
open PlanarThreeSAT.EmbeddedCNFIncidenceDrawing
open PeriodicOrthocrossing

/-- Kind-independent physical-lane gate above one occurrence module. -/
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
      [(32, 76), (31, 76), (31, 77), (30, 77),
        (30, 78), (29, 78), (29, 80), (28, 80),
        (28, 108)]
  | .fixedRed, false, .green =>
      [(22, 80), (22, 81), (21, 81), (21, 82),
        (20, 82), (20, 108)]
  | .fixedRed, false, .blue =>
      [(26, 80), (25, 80), (25, 81), (24, 81),
        (24, 108)]
  | .fixedRed, true, .red =>
      [(24, 76), (24, 78), (26, 78), (26, 81),
        (27, 81), (27, 82), (28, 82), (28, 108)]
  | .fixedRed, true, .green =>
      [(34, 80), (34, 81), (37, 81), (37, 77),
        (33, 77), (33, 72), (32, 72), (28, 72),
        (28, 70), (28, 69), (25, 69), (25, 68),
        (24, 68), (23, 68), (23, 69), (21, 69),
        (21, 70), (20, 70), (20, 108)]
  | .fixedRed, true, .blue =>
      [(30, 80), (28, 80), (28, 74), (28, 73),
        (25, 73), (25, 72), (24, 72), (23, 72),
        (23, 80), (24, 80), (24, 108)]
  | .fixedGreen, false, .red =>
      [(16, 64), (15, 64), (15, 95), (24, 95),
        (24, 108)]
  | .fixedGreen, false, .green =>
      [(16, 72), (16, 81), (28, 81), (28, 108)]
  | .fixedGreen, false, .blue =>
      [(32, 72), (33, 72), (33, 47), (14, 47),
        (14, 107), (20, 107), (20, 108)]
  | .fixedGreen, true, .red =>
      [(24, 76), (24, 108)]
  | .fixedGreen, true, .green =>
      [(28, 76), (28, 108)]
  | .fixedGreen, true, .blue =>
      [(20, 76), (20, 108)]
  | .fixedBlue, false, .red =>
      [(16, 64), (14, 64), (14, 73), (20, 73),
        (20, 108)]
  | .fixedBlue, false, .green =>
      [(16, 72), (24, 72), (24, 108)]
  | .fixedBlue, false, .blue =>
      [(32, 72), (28, 72), (28, 108)]
  | .fixedBlue, true, .red =>
      [(40, 64), (39, 64), (39, 65), (38, 65),
        (38, 67), (36, 67), (36, 68), (36, 71), (34, 71),
        (34, 72), (26, 72), (26, 73), (25, 73),
        (25, 74), (24, 74), (24, 77), (23, 77),
        (23, 78), (22, 78), (22, 79), (20, 79),
        (20, 108)]
  | .fixedBlue, true, .green =>
      [(40, 72), (37, 72), (37, 76), (34, 76),
        (34, 77), (33, 77), (33, 78), (31, 78),
        (31, 80), (30, 80), (30, 82), (29, 82),
        (29, 83), (28, 83), (28, 84), (27, 84),
        (27, 86), (26, 86), (26, 87), (25, 87),
        (25, 90), (24, 90), (24, 108)]
  | .fixedBlue, true, .blue =>
      [(24, 72), (25, 72), (25, 71), (28, 71),
        (28, 68), (28, 66), (30, 66), (30, 65),
        (31, 65), (31, 64), (32, 64), (33, 64),
        (33, 63), (41, 63),
        (41, 73), (40, 73), (40, 74), (39, 74),
        (39, 79), (37, 79), (37, 83), (36, 83),
        (36, 86), (35, 86), (35, 88), (31, 88),
        (31, 89), (28, 89), (28, 108)]

/-- Translate the six slot-zero tables to an arbitrary occurrence slot. -/
def standardVariableLocalGateRoute
    (slot : VariableSiteSlot)
    (kind : VariableConnectorKind)
    (polarity : Bool)
    (color : WireColor) : List Cell :=
  translatePolyline (variableModuleOrigin slot)
    (standardVariableLocalGateRouteAtFirst kind polarity color)

/-- Every semantic-color route ends at its assigned physical-lane gate. -/
@[simp]
theorem standardVariableLocalGateRoute_getLast?
    (slot : VariableSiteSlot)
    (kind : VariableConnectorKind)
    (polarity : Bool)
    (color : WireColor) :
    (standardVariableLocalGateRoute
      slot kind polarity color).getLast? =
        some
          (standardVariableOuterGate
            slot (kind.ribbonLaneForColor color)) := by
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
