/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetIOrientationBehavior

/-!
# Geometric port-phase refinements of I-gadget orientations

The Boolean inward orientation forgets the exact geometric state crossing a
colored block boundary.  This file retains that finite phase information for
the vertex-separated Figure 12 table.  It also proves that any coherent
selection of viable I-port states lifts to exact compatible local tilings.
-/

namespace LeanTrominoes
namespace Gadget

/-- A geometric phase refinement of a Boolean I-gadget orientation. -/
def HasIPortRefinement (drawing : PeriodicOrthogonalDrawing)
    (orientation : drawing.Orientation) : Prop :=
  ∃ configurations : Cell → PortConfiguration,
    (∀ location,
      (drawing.getAt location, configurations location) ∈
        iSeparatedCellPortTable) ∧
    (∀ location side,
      ((drawing.getAt location).portColor side).isSome →
      iConfigurationInward (drawing.getAt location)
        (configurations location) side = orientation location side) ∧
    ∀ location side,
      (configurations location).get side =
        (configurations
          (PeriodicOrthogonalDrawing.latticeNeighbor location side)).get
            side.opposite

/-- A viable separated-table entry comes from an exact local I-tromino
tiling. -/
theorem exists_exactCellTiling_of_mem_iSeparated
    (cellType : OrthogonalCellType) (configuration : PortConfiguration)
    (member :
      (cellType, configuration) ∈ iSeparatedCellPortTable) :
    ∃ placements,
      placements ∈ exactCellTilings .I cellType ∧
        portConfiguration .I
          (orthogonalCellGadget .I cellType) placements =
            configuration := by
  have supported :
      (cellType, configuration) ∈ supportedCellPortTable .I :=
    (Finset.mem_filter.mp member).1
  have raw :
      (cellType, configuration) ∈ globalCellPortTable .I :=
    (Finset.mem_filter.mp supported).1
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
    (mem_exactCellPortConfigurations_iff .I cellType
      configuration).mp exactMember
  exact ⟨placements,
    (mem_exactCellTilings_iff .I cellType placements).mpr tiling,
    ports⟩

/-- Any globally coherent selection of viable separated I-port
configurations lifts to compatible exact local tilings. -/
theorem hasCompatibleGadgetTiling_of_hasIPortRefinement
    (drawing : PeriodicOrthogonalDrawing)
    (orientation : drawing.Orientation)
    (refinement : HasIPortRefinement drawing orientation) :
    HasCompatibleGadgetTiling .I drawing := by
  classical
  obtain ⟨configurations, locallySupported, -, portsAgree⟩ := refinement
  have localWitness (location : Cell) :
      ∃ placements,
        placements ∈ exactCellTilings .I (drawing.getAt location) ∧
          portConfiguration .I
            (orthogonalCellGadget .I (drawing.getAt location)) placements =
              configurations location :=
    exists_exactCellTiling_of_mem_iSeparated _ _
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

end Gadget
end LeanTrominoes
