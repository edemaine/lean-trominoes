/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetOrientationBehavior
import LeanTrominoes.GadgetColoring

/-!
# Verified local orientation behavior of the Figure 12 I gadgets

The paper orients an edge by the vector from the center of its crossing
I-tromino to the pixel carrying the edge color.  A geometric port retains the
whole crossing footprint, so this vector can be recovered without choosing a
particular placement representation.  This file defines that recovery and
certifies the local Figure 12 orientation table.
-/

namespace LeanTrominoes
namespace Gadget

/-- The horizontal length-three I footprint centered at a lattice cell. -/
def horizontalIFootprint (center : Cell) : Finset Cell :=
  {Cell.add center (-1, 0), center, Cell.add center (1, 0)}

/-- The vertical length-three I footprint centered at a lattice cell. -/
def verticalIFootprint (center : Cell) : Finset Cell :=
  {Cell.add center (0, -1), center, Cell.add center (0, 1)}

/-- Recover the middle cell of a geometric I-tromino footprint.  The result is
a finset so that the definition remains total on arbitrary port data. -/
def iFootprintCenters (footprint : Finset Cell) : Finset Cell :=
  footprint.filter fun center =>
    horizontalIFootprint center = footprint ∨
      verticalIFootprint center = footprint

/-- All center-to-colored-pixel vectors carried by the I footprints in one
normalized geometric port. -/
def iPortColorVectors (color : WireColor) (port : PortState) : Finset Cell :=
  port.biUnion fun footprint =>
    (iFootprintCenters footprint).biUnion fun center =>
      (footprint.filter fun cell => iPixelColor cell = some color).image
        fun cell => Cell.sub cell center

/-- The unit vector pointing from a block boundary into that block. -/
def Side.inwardVector : Side → Cell
  | .north => (0, 1)
  | .east => (-1, 0)
  | .south => (0, -1)
  | .west => (1, 0)

/-- The inward value fixed by a nonzero center-to-marker vector.  A neutral
phase, where the marker is the center or no tromino crosses this particular
side, deliberately returns `none`: its direction must be inferred from the
rest of the local gadget. -/
def iPortSpecifiedInward (color : WireColor) (side : Side)
    (port : PortState) : Option Bool :=
  let vectors := iPortColorVectors color port
  if side.inwardVector ∈ vectors then some true
  else if side.opposite.inwardVector ∈ vectors then some false
  else none

/-- Bit position used to enumerate the sixteen Boolean patterns on four
sides. -/
def Side.bitIndex : Side → Nat
  | .north => 0
  | .east => 1
  | .south => 2
  | .west => 3

/-- Base value for a neutral I phase.  The marker coloring shifts green
horizontal wires and blue vertical wires by one phase; in all cases opposite
sides receive complementary values. -/
def iNeutralInward (cellType : OrthogonalCellType) (side : Side) : Bool :=
  let phase :=
    match cellType.portColor side, side.axis with
    | some .green, .horizontal => true
    | some .blue, .vertical => true
    | _, _ => false
  xor phase side.reversesPortValue

/-- Enumerate local patterns as deviations from the color-sensitive neutral
phase convention. -/
def iInwardPattern (cellType : OrthogonalCellType)
    (mask : Nat) (side : Side) : Bool :=
  xor (iNeutralInward cellType side) (mask.testBit side.bitIndex)

/-- The trichromatic gadget has one central 0-or-3 phase, represented by its
distinguished north/red arm.  Its other two arm vectors follow that phase
rather than acting as independent direction constraints. -/
def OrthogonalCellType.iVectorSideRelevant
    (cellType : OrthogonalCellType) (side : Side) : Bool :=
  match cellType with
  | .trichromaticVertex _ => side == .north
  | _ => true

/-- A local Boolean pattern satisfies the drawing-cell constraint and agrees
with every nonzero center-to-marker vector visible at its ports. -/
def IInwardPatternFits (cellType : OrthogonalCellType)
    (configuration : PortConfiguration) (mask : Nat) : Prop :=
  PeriodicOrthogonalDrawing.satisfiesOrientation cellType
      (iInwardPattern cellType mask) ∧
    ∀ side color, cellType.portColor side = some color →
      cellType.iVectorSideRelevant side →
        match iPortSpecifiedInward color side (configuration.get side) with
        | none => True
        | some inward => iInwardPattern cellType mask side = inward

instance (cellType : OrthogonalCellType)
    (configuration : PortConfiguration) (mask : Nat) :
    Decidable (IInwardPatternFits cellType configuration mask) := by
  unfold IInwardPatternFits
  letI : Decidable (∀ side color,
      cellType.portColor side = some color →
        cellType.iVectorSideRelevant side →
          match iPortSpecifiedInward color side
              (configuration.get side) with
          | none => True
          | some inward => iInwardPattern cellType mask side = inward) := by
    let sideDecidable (side : Side) : Decidable (∀ color,
        cellType.portColor side = some color →
          cellType.iVectorSideRelevant side →
            match iPortSpecifiedInward color side
                (configuration.get side) with
            | none => True
            | some inward => iInwardPattern cellType mask side = inward) := by
      letI : ∀ color, Decidable
          (cellType.portColor side = some color →
            cellType.iVectorSideRelevant side →
              match iPortSpecifiedInward color side
                  (configuration.get side) with
              | none => True
              | some inward => iInwardPattern cellType mask side = inward) :=
        fun color => by
          by_cases colorMatch : cellType.portColor side = some color
          · simp only [colorMatch, true_implies]
            by_cases relevant : cellType.iVectorSideRelevant side
            · simp only [relevant, true_implies]
              cases specified :
                  iPortSpecifiedInward color side
                    (configuration.get side) with
              | none => exact isTrue trivial
              | some inward =>
                  infer_instance
            · exact isTrue fun contradiction =>
                (relevant contradiction).elim
          · exact isTrue fun contradiction =>
              (colorMatch contradiction).elim
      exact Fintype.decidableForallFintype
    letI : ∀ side, Decidable (∀ color,
        cellType.portColor side = some color →
          cellType.iVectorSideRelevant side →
            match iPortSpecifiedInward color side
                (configuration.get side) with
            | none => True
            | some inward => iInwardPattern cellType mask side = inward) :=
      sideDecidable
    exact Fintype.decidableForallFintype
  infer_instance

/-- The first locally legal completion of the partial vector directions,
preferring the opposite-side-compatible neutral convention. -/
def iConfigurationMask (cellType : OrthogonalCellType)
    (configuration : PortConfiguration) : Nat :=
  ((List.range 16).find? fun mask =>
    decide (IInwardPatternFits cellType configuration mask)).getD 0

/-- Colored inward values read from a complete I-tromino port configuration;
neutral phases are completed using all ports of the local drawing cell. -/
def iConfigurationInward (cellType : OrthogonalCellType)
    (configuration : PortConfiguration) (side : Side) : Bool :=
  iInwardPattern cellType (iConfigurationMask cellType configuration) side

/-- Every supported I-gadget state satisfies its intended local orientation
constraint. -/
def ITableOrientationSound
    (table : Finset (OrthogonalCellType × PortConfiguration)) : Prop :=
  ∀ entry : { entry // entry ∈ table },
    PeriodicOrthogonalDrawing.satisfiesOrientation entry.1.1
      (iConfigurationInward entry.1.1 entry.1.2)

/-- Every satisfying inward pattern is represented by a supported I-gadget
state of the requested drawing-cell type. -/
def ITableOrientationComplete
    (table : Finset (OrthogonalCellType × PortConfiguration)) : Prop :=
  ∀ cellType inward,
    PeriodicOrthogonalDrawing.satisfiesOrientation cellType inward →
      ∃ entry : { entry // entry ∈ table },
        entry.1.1 = cellType ∧
          ∀ side, (cellType.portColor side).isSome →
            iConfigurationInward cellType entry.1.2 side = inward side

/-- A supported local state is viable in a vertex-separated drawing.  Routing
states are always retained; a vertex state is retained only when each active
arm has an exactly matching nonvertex state. -/
def IEntrySeparatedSupported
    (table : Finset (OrthogonalCellType × PortConfiguration))
    (entry : OrthogonalCellType × PortConfiguration) : Prop :=
  entry.1.isVertex = true →
    ∀ side color, entry.1.portColor side = some color →
      ∃ neighbor : { neighbor // neighbor ∈ table },
        neighbor.1.1.isVertex = false ∧
          neighbor.1.1.portColor side.opposite = some color ∧
            entry.2.get side = neighbor.1.2.get side.opposite

instance (table : Finset (OrthogonalCellType × PortConfiguration))
    (entry : OrthogonalCellType × PortConfiguration) :
    Decidable (IEntrySeparatedSupported table entry) := by
  unfold IEntrySeparatedSupported
  infer_instance

/-- The Figure 12 state table after enforcing the vertex-separation invariant
of the normalized orthogonal drawing. -/
def iSeparatedCellPortTable :
    Finset (OrthogonalCellType × PortConfiguration) :=
  (supportedCellPortTable .I).filter fun entry =>
    IEntrySeparatedSupported (supportedCellPortTable .I) entry

/-- Equal viable I ports of matching color give opposite inward values, even
when either local cell had to complete a neutral vector phase. -/
def ISupportedPortsOpposite : Prop :=
  ∀ left right : { entry // entry ∈ iSeparatedCellPortTable },
    ∀ side color,
      left.1.1.portColor side = some color →
      right.1.1.portColor side.opposite = some color →
      left.1.2.get side = right.1.2.get side.opposite →
        iConfigurationInward left.1.1 left.1.2 side =
          !(iConfigurationInward right.1.1 right.1.2 side.opposite)

instance (table : Finset (OrthogonalCellType × PortConfiguration)) :
    Decidable (ITableOrientationSound table) := by
  unfold ITableOrientationSound
  infer_instance

instance (table : Finset (OrthogonalCellType × PortConfiguration)) :
    Decidable (ITableOrientationComplete table) := by
  unfold ITableOrientationComplete
  infer_instance

instance : Decidable ISupportedPortsOpposite := by
  unfold ISupportedPortsOpposite
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 1000000 in
/-- Every unused side in the complete raw Figure 12 table has an empty
geometric port. -/
theorem iGlobalCellPortTable_unused :
    TableUnusedPortsEmpty (globalCellPortTable .I) := by
  native_decide

/-- The finite local properties needed from the Figure 12 I-tromino gadget
library. -/
def ILocalOrientationTableCorrect : Prop :=
  let table := iSeparatedCellPortTable
  ITableOrientationSound table ∧
    ITableOrientationComplete table ∧
    TableUnusedPortsEmpty table ∧
    ISupportedPortsOpposite

instance : Decidable ILocalOrientationTableCorrect := by
  unfold ILocalOrientationTableCorrect
  infer_instance

set_option maxRecDepth 100000 in
set_option maxHeartbeats 5000000 in
/-- Exhaustive certificate for all Figure 12 local states and their geometric
center-to-marker vectors. -/
theorem iLocalOrientationTableCorrect : ILocalOrientationTableCorrect := by
  native_decide

/-- Every state selected by a compatible assignment on a vertex-separated
drawing belongs to the viable Figure 12 table. -/
theorem selectedPortEntry_mem_iSeparated
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (separated : drawing.VerticesSeparated)
    (assignment : LocalTilingAssignment .I drawing)
    (locallyTiled : IsLocallyTiled .I drawing assignment)
    (compatible : IsPortCompatible .I drawing assignment)
    (location : Cell) :
    (drawing.getAt location, selectedPortConfiguration .I drawing
      assignment location) ∈ iSeparatedCellPortTable := by
  apply Finset.mem_filter.mpr
  refine ⟨selectedPortEntry_mem_supported .I drawing wellFormed assignment
    locallyTiled compatible iGlobalCellPortTable_unused location, ?_⟩
  unfold IEntrySeparatedSupported
  intro isVertex side color colorMatch
  let neighbor :=
    PeriodicOrthogonalDrawing.latticeNeighbor location side
  refine ⟨⟨(drawing.getAt neighbor,
      selectedPortConfiguration .I drawing assignment neighbor), ?_⟩,
    ?_, ?_, ?_⟩
  · exact selectedPortEntry_mem_supported .I drawing wellFormed assignment
      locallyTiled compatible iGlobalCellPortTable_unused neighbor
  · exact drawing.verticesSeparatedAt separated location side isVertex
  · have colors :=
      drawing.portColor_latticeNeighbor_eq wellFormed location side
    rw [colorMatch] at colors
    exact colors.symm
  · exact selectedPortConfiguration_neighbor .I drawing assignment
      compatible location side

/-- The orientation read from every local state of an I-gadget assignment. -/
def iOrientationFromAssignment (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment .I drawing) : drawing.Orientation :=
  fun location => iConfigurationInward (drawing.getAt location)
    (selectedPortConfiguration .I drawing assignment location)

/-- A compatible Figure 12 assignment over a separated well-formed drawing
induces a valid trichromatic graph orientation. -/
theorem iIsOrientation_of_compatibleAssignment
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (separated : drawing.VerticesSeparated)
    (assignment : LocalTilingAssignment .I drawing)
    (locallyTiled : IsLocallyTiled .I drawing assignment)
    (compatible : IsPortCompatible .I drawing assignment) :
    drawing.IsOrientation (iOrientationFromAssignment drawing assignment) := by
  constructor
  · intro location
    have sound : ITableOrientationSound iSeparatedCellPortTable :=
      iLocalOrientationTableCorrect.1
    exact sound ⟨_, selectedPortEntry_mem_iSeparated drawing wellFormed
      separated assignment locallyTiled compatible location⟩
  · intro location side active
    cases colorMatch : (drawing.getAt location).portColor side with
    | none => simp [colorMatch] at active
    | some color =>
        let neighbor :=
          PeriodicOrthogonalDrawing.latticeNeighbor location side
        have neighborColor :=
          drawing.portColor_latticeNeighbor_eq wellFormed location side
        rw [colorMatch] at neighborColor
        have ports := selectedPortConfiguration_neighbor .I drawing
          assignment compatible location side
        have opposite : ISupportedPortsOpposite :=
          iLocalOrientationTableCorrect.2.2.2
        exact opposite
          ⟨_, selectedPortEntry_mem_iSeparated drawing wellFormed separated
            assignment locallyTiled compatible location⟩
          ⟨_, selectedPortEntry_mem_iSeparated drawing wellFormed separated
            assignment locallyTiled compatible neighbor⟩
          side color colorMatch neighborColor.symm ports

/-- Soundness half of Figure 12 gadget behavior on normalized drawings. -/
theorem iHasOrientation_of_hasCompatibleGadgetTiling
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (separated : drawing.VerticesSeparated)
    (compatibleTiling : HasCompatibleGadgetTiling .I drawing) :
    drawing.HasOrientation := by
  obtain ⟨assignment, locallyTiled, compatible⟩ := compatibleTiling
  exact ⟨wellFormed, iOrientationFromAssignment drawing assignment,
    iIsOrientation_of_compatibleAssignment drawing wellFormed separated
      assignment locallyTiled compatible⟩

end Gadget
end LeanTrominoes
