/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetBehavior

/-!
# Verified local orientation behavior of the Figure 11 L gadgets

Open gadget windows contain transient boundary states.  We first remove every
port configuration lacking a compatible neighbor on one of its four sides.
For the L-tromino library, the remaining colored ports admit a uniform Boolean
interpretation depending only on the edge color, its axis, and whether a
tromino crosses the block boundary.  Native certificates check that every
supported local state satisfies the intended wire/vertex constraint and that
every satisfying local orientation is represented.

The I-tromino gadgets require a later context-sensitive phase argument: their
supported local table has no single universal Boolean labeling of port states.
-/

namespace LeanTrominoes
namespace Gadget

/-- All local drawing-cell types paired with their exact geometric port
configurations. -/
def globalCellPortTable (tromino : Tromino) :
    Finset (OrthogonalCellType × PortConfiguration) :=
  Finset.univ.biUnion fun cellType =>
    (exactCellPortConfigurations tromino cellType).image fun configuration =>
      (cellType, configuration)

/-- The four geometric ports selected by one local assignment state. -/
def selectedPortConfiguration (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (location : Cell) : PortConfiguration :=
  portConfiguration tromino
    (orthogonalCellGadget tromino (drawing.getAt location))
    (assignment location)

/-- A locally exact assignment state contributes an entry to the complete
finite port table. -/
theorem selectedPortEntry_mem_global (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (location : Cell) :
    (drawing.getAt location, selectedPortConfiguration tromino drawing
      assignment location) ∈ globalCellPortTable tromino := by
  apply Finset.mem_biUnion.mpr
  refine ⟨drawing.getAt location, Finset.mem_univ _, ?_⟩
  apply Finset.mem_image.mpr
  refine ⟨selectedPortConfiguration tromino drawing assignment location,
    ?_, rfl⟩
  apply (mem_exactCellPortConfigurations_iff tromino
    (drawing.getAt location) _).mpr
  refine ⟨assignment location, ?_, rfl⟩
  exact (mem_exactCellTilings_iff tromino (drawing.getAt location)
    (assignment location)).mp (locallyTiled location)

/-- Port compatibility gives equality on any requested side, including west
and north by applying the stored east/south condition at the neighbor. -/
theorem selectedPortConfiguration_neighbor (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (compatible : IsPortCompatible tromino drawing assignment)
    (location : Cell) (side : Side) :
    (selectedPortConfiguration tromino drawing assignment location).get side =
      (selectedPortConfiguration tromino drawing assignment
        (PeriodicOrthogonalDrawing.latticeNeighbor location side)).get
          side.opposite := by
  cases side with
  | east => exact compatible.1 location
  | south => exact compatible.2 location
  | west =>
      have neighborCompatibility := compatible.1
        (PeriodicOrthogonalDrawing.latticeNeighbor location .west)
      have back : PeriodicOrthogonalDrawing.latticeNeighbor
          (PeriodicOrthogonalDrawing.latticeNeighbor location .west) .east =
          location := by
        simp [PeriodicOrthogonalDrawing.latticeNeighbor]
      rw [back] at neighborCompatibility
      simpa [selectedPortConfiguration, HorizontallyCompatible,
        PortConfiguration.get, Side.opposite] using
        neighborCompatibility.symm
  | north =>
      have neighborCompatibility := compatible.2
        (PeriodicOrthogonalDrawing.latticeNeighbor location .north)
      have back : PeriodicOrthogonalDrawing.latticeNeighbor
          (PeriodicOrthogonalDrawing.latticeNeighbor location .north) .south =
          location := by
        simp [PeriodicOrthogonalDrawing.latticeNeighbor]
      rw [back] at neighborCompatibility
      simpa [selectedPortConfiguration, VerticallyCompatible,
        PortConfiguration.get, Side.opposite] using
        neighborCompatibility.symm

/-- One side of a local state has a potential matching neighbor in the
current table, or is empty when the drawing cell has no edge on that side. -/
def CellPortEntrySupported
    (table : Finset (OrthogonalCellType × PortConfiguration))
    (entry : OrthogonalCellType × PortConfiguration) (side : Side) : Prop :=
  match entry.1.portColor side with
  | none => entry.2.get side = ∅
  | some color =>
      ∃ neighbor : { neighbor // neighbor ∈ table },
        neighbor.1.1.portColor side.opposite = some color ∧
          entry.2.get side = neighbor.1.2.get side.opposite

instance (table : Finset (OrthogonalCellType × PortConfiguration))
    (entry : OrthogonalCellType × PortConfiguration) (side : Side) :
    Decidable (CellPortEntrySupported table entry side) := by
  unfold CellPortEntrySupported
  split <;> infer_instance

/-- Delete every local state lacking support on at least one side. -/
def pruneCellPortTable
    (table : Finset (OrthogonalCellType × PortConfiguration)) :
    Finset (OrthogonalCellType × PortConfiguration) :=
  table.filter fun entry => ∀ side, CellPortEntrySupported table entry side

/-- The one-step supported core of the constant Figure 11/12 table.  A native
certificate below verifies that another pruning round changes nothing. -/
def supportedCellPortTable (tromino : Tromino) :
    Finset (OrthogonalCellType × PortConfiguration) :=
  pruneCellPortTable (globalCellPortTable tromino)

/-- The supported core is already a fixed point for both tromino libraries. -/
theorem supportedCellPortTable_fixed (tromino : Tromino) :
    pruneCellPortTable (supportedCellPortTable tromino) =
      supportedCellPortTable tromino := by
  cases tromino <;> native_decide

/-- The wire axis perpendicular to a block side. -/
def Side.axis : Side → WireAxis
  | .north | .south => .vertical
  | .east | .west => .horizontal

/-- East and south reverse the base port truth value used by west and north. -/
def Side.reversesPortValue : Side → Bool
  | .north | .west => false
  | .east | .south => true

@[simp]
theorem Side.axis_opposite (side : Side) :
    side.opposite.axis = side.axis := by
  cases side <;> rfl

/-- Base truth value of a colored L-tromino port.  Red uses nonemptiness on
both axes; green reverses the horizontal convention; blue reverses the
vertical convention. -/
def lPortBaseValue (color : WireColor) (axis : WireAxis)
    (port : PortState) : Bool :=
  let nonempty := decide (port ≠ ∅)
  match color, axis with
  | .red, _ => nonempty
  | .green, .vertical => nonempty
  | .green, .horizontal => !nonempty
  | .blue, .vertical => !nonempty
  | .blue, .horizontal => nonempty

/-- Inward half-edge value encoded by one normalized L-tromino port. -/
def lPortInward (color : WireColor) (side : Side)
    (port : PortState) : Bool :=
  xor (lPortBaseValue color side.axis port) side.reversesPortValue

/-- Colored inward values read from a complete L-tromino port configuration;
unused sides are normalized to `false`. -/
def lConfigurationInward (cellType : OrthogonalCellType)
    (configuration : PortConfiguration) (side : Side) : Bool :=
  match cellType.portColor side with
  | none => false
  | some color => lPortInward color side (configuration.get side)

/-- Equal ports on opposite sides always encode complementary inward values. -/
theorem lPortInward_opposite (color : WireColor) (side : Side)
    (port : PortState) :
    lPortInward color side port =
      !(lPortInward color side.opposite port) := by
  cases color <;> cases side <;>
    simp [lPortInward, lPortBaseValue, Side.axis, Side.reversesPortValue,
      Side.opposite, xor]

/-- Every supported L-gadget state satisfies its intended local orientation
constraint. -/
def LTableOrientationSound
    (table : Finset (OrthogonalCellType × PortConfiguration)) : Prop :=
  ∀ entry : { entry // entry ∈ table },
    PeriodicOrthogonalDrawing.satisfiesOrientation entry.1.1
      (lConfigurationInward entry.1.1 entry.1.2)

/-- Every satisfying inward pattern is represented by a supported L-gadget
state of the requested drawing-cell type. -/
def LTableOrientationComplete
    (table : Finset (OrthogonalCellType × PortConfiguration)) : Prop :=
  ∀ cellType inward,
    PeriodicOrthogonalDrawing.satisfiesOrientation cellType inward →
      ∃ entry : { entry // entry ∈ table },
        entry.1.1 = cellType ∧
          ∀ side, (cellType.portColor side).isSome →
            lConfigurationInward cellType entry.1.2 side = inward side

/-- Sides unused by the drawing alphabet carry no crossing trominoes. -/
def TableUnusedPortsEmpty
    (table : Finset (OrthogonalCellType × PortConfiguration)) : Prop :=
  ∀ entry : { entry // entry ∈ table }, ∀ side,
    entry.1.1.portColor side = none → entry.1.2.get side = ∅

instance (table : Finset (OrthogonalCellType × PortConfiguration)) :
    Decidable (LTableOrientationSound table) := by
  unfold LTableOrientationSound
  infer_instance

instance (table : Finset (OrthogonalCellType × PortConfiguration)) :
    Decidable (LTableOrientationComplete table) := by
  unfold LTableOrientationComplete
  infer_instance

instance (table : Finset (OrthogonalCellType × PortConfiguration)) :
    Decidable (TableUnusedPortsEmpty table) := by
  unfold TableUnusedPortsEmpty
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Every unused side in the complete raw Figure 11 table has an empty
geometric port. -/
theorem lGlobalCellPortTable_unused :
    TableUnusedPortsEmpty (globalCellPortTable .L) := by
  native_decide

/-- Actual neighboring states witness one-step support for every side of a
locally exact, port-compatible assignment. -/
theorem selectedPortEntry_supported (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (compatible : IsPortCompatible tromino drawing assignment)
    (rawUnused : TableUnusedPortsEmpty (globalCellPortTable tromino))
    (location : Cell) (side : Side) :
    CellPortEntrySupported (globalCellPortTable tromino)
      (drawing.getAt location,
        selectedPortConfiguration tromino drawing assignment location) side := by
  cases colorMatch : (drawing.getAt location).portColor side with
  | none =>
      unfold CellPortEntrySupported
      rw [colorMatch]
      exact rawUnused
        ⟨_, selectedPortEntry_mem_global tromino drawing assignment
          locallyTiled location⟩ side colorMatch
  | some color =>
      unfold CellPortEntrySupported
      rw [colorMatch]
      let neighborLocation :=
        PeriodicOrthogonalDrawing.latticeNeighbor location side
      let neighborEntry : OrthogonalCellType × PortConfiguration :=
        (drawing.getAt neighborLocation,
          selectedPortConfiguration tromino drawing assignment neighborLocation)
      refine ⟨⟨neighborEntry, ?_⟩, ?_, ?_⟩
      · exact selectedPortEntry_mem_global tromino drawing assignment
          locallyTiled neighborLocation
      · have colors := drawing.portColor_latticeNeighbor_eq
          wellFormed location side
        rw [colorMatch] at colors
        exact colors.symm
      · exact selectedPortConfiguration_neighbor tromino drawing assignment
          compatible location side

/-- Every state used by an actual well-formed compatible assignment belongs
to the supported finite core. -/
theorem selectedPortEntry_mem_supported (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (compatible : IsPortCompatible tromino drawing assignment)
    (rawUnused : TableUnusedPortsEmpty (globalCellPortTable tromino))
    (location : Cell) :
    (drawing.getAt location, selectedPortConfiguration tromino drawing
      assignment location) ∈ supportedCellPortTable tromino := by
  apply Finset.mem_filter.mpr
  exact ⟨selectedPortEntry_mem_global tromino drawing assignment
      locallyTiled location,
    selectedPortEntry_supported tromino drawing wellFormed assignment
      locallyTiled compatible rawUnused location⟩

/-- The finite local properties needed from the Figure 11 L-tromino gadget
library. -/
def LLocalOrientationTableCorrect : Prop :=
  let table := supportedCellPortTable .L
  LTableOrientationSound table ∧
    LTableOrientationComplete table ∧
    TableUnusedPortsEmpty table

instance : Decidable LLocalOrientationTableCorrect := by
  unfold LLocalOrientationTableCorrect
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Exhaustive certificate for all Figure 11 local states. -/
theorem lLocalOrientationTableCorrect : LLocalOrientationTableCorrect := by
  native_decide

/-- The orientation read from every local state of an L-gadget assignment. -/
def lOrientationFromAssignment (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment .L drawing) : drawing.Orientation :=
  fun location => lConfigurationInward (drawing.getAt location)
    (selectedPortConfiguration .L drawing assignment location)

/-- A compatible Figure 11 assignment over a well-formed drawing induces a
valid trichromatic graph orientation. -/
theorem lIsOrientation_of_compatibleAssignment
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (assignment : LocalTilingAssignment .L drawing)
    (locallyTiled : IsLocallyTiled .L drawing assignment)
    (compatible : IsPortCompatible .L drawing assignment) :
    drawing.IsOrientation (lOrientationFromAssignment drawing assignment) := by
  constructor
  · intro location
    have sound : LTableOrientationSound (supportedCellPortTable .L) :=
      lLocalOrientationTableCorrect.1
    exact sound ⟨_, selectedPortEntry_mem_supported .L drawing
      wellFormed assignment locallyTiled compatible
      lGlobalCellPortTable_unused location⟩
  · intro location side active
    cases colorMatch : (drawing.getAt location).portColor side with
    | none => simp [colorMatch] at active
    | some color =>
        have neighborColor := drawing.portColor_latticeNeighbor_eq
          wellFormed location side
        rw [colorMatch] at neighborColor
        have ports := selectedPortConfiguration_neighbor .L drawing
          assignment compatible location side
        simp only [lOrientationFromAssignment, lConfigurationInward,
          colorMatch, neighborColor.symm]
        rw [← ports]
        exact lPortInward_opposite color side _

/-- Soundness half of Figure 11 gadget behavior: on well-formed normalized
drawings, compatible local L-tromino states imply an orientation. -/
theorem lHasOrientation_of_hasCompatibleGadgetTiling
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (compatibleTiling : HasCompatibleGadgetTiling .L drawing) :
    drawing.HasOrientation := by
  obtain ⟨assignment, locallyTiled, compatible⟩ := compatibleTiling
  exact ⟨wellFormed, assignment |> lOrientationFromAssignment drawing,
    lIsOrientation_of_compatibleAssignment drawing wellFormed assignment
      locallyTiled compatible⟩

end Gadget
end LeanTrominoes
