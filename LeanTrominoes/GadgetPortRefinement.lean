/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetOrientationBehavior

/-!
# Geometric port-phase refinements of L-gadget orientations

The Boolean inward orientation forgets which of two distinct nonempty
geometric port states crosses a colored block boundary.  This file retains
that finite phase information explicitly.  It proves that compatible local
L-tromino tilings are equivalent to valid orientations equipped with a
globally coherent supported-port refinement, isolating the remaining
phase-lifting lemma needed for gadget completeness.
-/

namespace LeanTrominoes
namespace Gadget

/-- A geometric phase refinement of a Boolean orientation: every drawing
cell selects a supported exact port configuration, reads the requested
inward values, and agrees exactly with all four neighbors. -/
def HasLPortRefinement (drawing : PeriodicOrthogonalDrawing)
    (orientation : drawing.Orientation) : Prop :=
  ∃ configurations : Cell → PortConfiguration,
    (∀ location,
      (drawing.getAt location, configurations location) ∈
        supportedCellPortTable .L) ∧
    (∀ location side,
      ((drawing.getAt location).portColor side).isSome →
      lConfigurationInward (drawing.getAt location)
        (configurations location) side = orientation location side) ∧
    ∀ location side,
      (configurations location).get side =
        (configurations
          (PeriodicOrthogonalDrawing.latticeNeighbor location side)).get
            side.opposite

/-- A supported port entry comes from an exact local L-tromino tiling. -/
theorem exists_exactCellTiling_of_mem_lSupported
    (cellType : OrthogonalCellType) (configuration : PortConfiguration)
    (member :
      (cellType, configuration) ∈ supportedCellPortTable .L) :
    ∃ placements,
      placements ∈ exactCellTilings .L cellType ∧
        portConfiguration .L
          (orthogonalCellGadget .L cellType) placements =
            configuration := by
  have raw :
      (cellType, configuration) ∈ globalCellPortTable .L :=
    (Finset.mem_filter.mp member).1
  apply Finset.mem_biUnion.mp at raw
  obtain ⟨entryType, -, entryMember⟩ := raw
  obtain ⟨entryConfiguration, exactMember, entryEquality⟩ :=
    Finset.mem_image.mp entryMember
  have typeEquality : entryType = cellType := by
    simpa using congrArg Prod.fst entryEquality
  subst entryType
  have configurationEquality :
      entryConfiguration = configuration := by
    simpa using congrArg Prod.snd entryEquality
  subst entryConfiguration
  obtain ⟨placements, tiling, ports⟩ :=
    (mem_exactCellPortConfigurations_iff .L cellType
      configuration).mp exactMember
  exact ⟨placements,
    (mem_exactCellTilings_iff .L cellType placements).mpr tiling,
    ports⟩

/-- A compatible local assignment supplies the geometric phase refinement
of its induced Boolean orientation. -/
theorem hasLPortRefinement_of_compatibleAssignment
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed)
    (assignment : LocalTilingAssignment .L drawing)
    (locallyTiled : IsLocallyTiled .L drawing assignment)
    (compatible : IsPortCompatible .L drawing assignment) :
    HasLPortRefinement drawing
      (lOrientationFromAssignment drawing assignment) := by
  refine ⟨selectedPortConfiguration .L drawing assignment, ?_, ?_, ?_⟩
  · intro location
    exact selectedPortEntry_mem_supported .L drawing wellFormed assignment
      locallyTiled compatible lGlobalCellPortTable_unused location
  · intro location side _
    rfl
  · intro location side
    exact selectedPortConfiguration_neighbor .L drawing assignment
      compatible location side

/-- Any globally coherent selection of supported L-port configurations can
be lifted back to compatible exact local tilings. -/
theorem hasCompatibleGadgetTiling_of_hasLPortRefinement
    (drawing : PeriodicOrthogonalDrawing)
    (orientation : drawing.Orientation)
    (refinement : HasLPortRefinement drawing orientation) :
    HasCompatibleGadgetTiling .L drawing := by
  classical
  obtain ⟨configurations, locallySupported, -, portsAgree⟩ := refinement
  have localWitness (location : Cell) :
      ∃ placements,
        placements ∈ exactCellTilings .L (drawing.getAt location) ∧
          portConfiguration .L
            (orthogonalCellGadget .L (drawing.getAt location)) placements =
              configurations location :=
    exists_exactCellTiling_of_mem_lSupported _ _
      (locallySupported location)
  choose assignment assignmentTiled assignmentPorts using localWitness
  refine ⟨assignment, assignmentTiled, ?_, ?_⟩
  · intro location
    unfold HorizontallyCompatible
    rw [assignmentPorts location,
      assignmentPorts
        (PeriodicOrthogonalDrawing.latticeNeighbor location .east)]
    exact portsAgree location .east
  · intro location
    unfold VerticallyCompatible
    rw [assignmentPorts location,
      assignmentPorts
        (PeriodicOrthogonalDrawing.latticeNeighbor location .south)]
    exact portsAgree location .south

/-- For a well-formed drawing, compatible L-gadget tilings are exactly valid
orientations equipped with a coherent geometric port-phase refinement. -/
theorem hasCompatibleGadgetTiling_iff_orientation_with_lPortRefinement
    (drawing : PeriodicOrthogonalDrawing)
    (wellFormed : drawing.IsWellFormed) :
    HasCompatibleGadgetTiling .L drawing ↔
      ∃ orientation : drawing.Orientation,
        drawing.IsOrientation orientation ∧
          HasLPortRefinement drawing orientation := by
  constructor
  · rintro ⟨assignment, locallyTiled, compatible⟩
    exact ⟨lOrientationFromAssignment drawing assignment,
      lIsOrientation_of_compatibleAssignment drawing wellFormed assignment
        locallyTiled compatible,
      hasLPortRefinement_of_compatibleAssignment drawing wellFormed
        assignment locallyTiled compatible⟩
  · rintro ⟨orientation, -, refinement⟩
    exact hasCompatibleGadgetTiling_of_hasLPortRefinement
      drawing orientation refinement

end Gadget
end LeanTrominoes
