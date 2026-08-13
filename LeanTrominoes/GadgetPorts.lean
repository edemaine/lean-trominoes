/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetLibrary
import LeanTrominoes.GadgetWire

/-!
# Four-sided tromino gadget ports

This file extends the horizontal transfer states used for straight wires to
all four sides of a gadget window.  Opposite ports are normalized into the
same coordinate system, so neighboring windows are compatible exactly when
their corresponding finite port states are equal.
-/

namespace LeanTrominoes
namespace Gadget

/-- A cardinal side of a rectangular gadget window. -/
inductive Side
  | north
  | east
  | south
  | west
  deriving DecidableEq, Repr, Fintype

/-- Does a footprint cross the north side of a window based at `y = 0`? -/
def crossesNorth (footprint : Finset Cell) : Prop :=
  ∃ cell ∈ footprint, cell.2 < 0

/-- Does a footprint cross the south side of a height-`height` window? -/
def crossesSouth (height : Nat) (footprint : Finset Cell) : Prop :=
  ∃ cell ∈ footprint, (height : Int) ≤ cell.2

instance (footprint : Finset Cell) : Decidable (crossesNorth footprint) := by
  unfold crossesNorth
  infer_instance

instance (height : Nat) (footprint : Finset Cell) :
    Decidable (crossesSouth height footprint) := by
  unfold crossesSouth
  infer_instance

/-- North-crossing footprints, in coordinates relative to the gadget below
the horizontal interface. -/
def northPortState (signature : PortState) : PortState :=
  signature.filter crossesNorth

/-- South-crossing footprints, translated into coordinates relative to the
gadget below the horizontal interface. -/
def southPortState (height : Nat) (signature : PortState) : PortState :=
  (signature.filter (crossesSouth height)).image fun footprint =>
    translateFootprint (0, -(height : Int)) footprint

/-- Extract and normalize one side of a geometric boundary signature. -/
def sidePortState (gadget : Gadget) (side : Side)
    (signature : PortState) : PortState :=
  match side with
  | .north => northPortState signature
  | .east => rightPortState gadget.width signature
  | .south => southPortState gadget.height signature
  | .west => leftPortState signature

/-- The four normalized port states induced by one local tiling. -/
structure PortConfiguration where
  north : PortState
  east : PortState
  south : PortState
  west : PortState
  deriving DecidableEq

/-- Select a side from a four-port configuration. -/
def PortConfiguration.get (configuration : PortConfiguration) :
    Side → PortState
  | .north => configuration.north
  | .east => configuration.east
  | .south => configuration.south
  | .west => configuration.west

/-- Package every normalized side state of a local tiling. -/
def portConfiguration (tromino : Tromino) (gadget : Gadget)
    (placements : Finset (Placement Unit)) : PortConfiguration :=
  let signature := boundarySignature tromino gadget.window placements
  { north := northPortState signature
    east := rightPortState gadget.width signature
    south := southPortState gadget.height signature
    west := leftPortState signature }

theorem portConfiguration_get (tromino : Tromino) (gadget : Gadget)
    (placements : Finset (Placement Unit)) (side : Side) :
    (portConfiguration tromino gadget placements).get side =
      sidePortState gadget side
        (boundarySignature tromino gadget.window placements) := by
  cases side <;> rfl

/-- All four-port configurations produced by verified exact-cover search. -/
def exactPortConfigurations (tromino : Tromino) (gadget : Gadget)
    (regionCells : List Cell) : Finset PortConfiguration :=
  ((exactWindowTilings tromino gadget regionCells).map
    (portConfiguration tromino gadget)).toFinset

theorem mem_exactPortConfigurations_iff (tromino : Tromino)
    (gadget : Gadget) (wellFormed : gadget.IsWellFormed)
    (regionCells : List Cell) (regionEquality : regionCells.toFinset = gadget.region)
    (configuration : PortConfiguration) :
    configuration ∈ exactPortConfigurations tromino gadget regionCells ↔
      ∃ placements, IsWindowTiling tromino gadget.window gadget.region placements ∧
        portConfiguration tromino gadget placements = configuration := by
  simp only [exactPortConfigurations, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨placements, member, equality⟩
    exact ⟨placements,
      (mem_exactWindowTilings_iff tromino gadget wellFormed
        regionCells regionEquality placements).mp member,
      equality⟩
  · rintro ⟨placements, tiling, equality⟩
    exact ⟨placements,
      (mem_exactWindowTilings_iff tromino gadget wellFormed
        regionCells regionEquality placements).mpr tiling,
      equality⟩

/-- Horizontal neighbors agree on their shared geometric trominoes. -/
def HorizontallyCompatible (left right : PortConfiguration) : Prop :=
  left.east = right.west

/-- Vertical neighbors agree on their shared geometric trominoes. -/
def VerticallyCompatible (top bottom : PortConfiguration) : Prop :=
  top.south = bottom.north

instance (left right : PortConfiguration) :
    Decidable (HorizontallyCompatible left right) := by
  unfold HorizontallyCompatible
  infer_instance

instance (top bottom : PortConfiguration) :
    Decidable (VerticallyCompatible top bottom) := by
  unfold VerticallyCompatible
  infer_instance

/-- Project a four-port configuration to the two sides of one wire axis. -/
def axisTransition (axis : WireAxis)
    (configuration : PortConfiguration) : PortState × PortState :=
  match axis with
  | .horizontal => (configuration.west, configuration.east)
  | .vertical => (configuration.north, configuration.south)

/-- The exact local transfer relation along one axis. -/
def exactAxisTransitions (tromino : Tromino) (gadget : Gadget)
    (axis : WireAxis) (regionCells : List Cell) :
    Finset (PortState × PortState) :=
  (exactPortConfigurations tromino gadget regionCells).image
    (axisTransition axis)

end Gadget
end LeanTrominoes
