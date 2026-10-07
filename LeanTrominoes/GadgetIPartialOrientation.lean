/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetIOrientationBehavior
import LeanTrominoes.GadgetPartialPortCompatibility
import Lean.Util.CollectAxioms

/-! # Reading I-gadget orientations from a bounded neighborhood

The soundness argument needs only two neighboring layers of local geometric
port states. It applies inside a partially tiled region, including the
quadrant forced by a prescribed Q placement.
-/
namespace LeanTrominoes.Gadget
namespace PartialIOrientation
set_option maxHeartbeats 800000
attribute [local irreducible] localAssignmentFromGlobal

def entry (drawing : PeriodicOrthogonalDrawing) (config : Cell → PortConfiguration)
    (cell : Cell) : OrthogonalCellType × PortConfiguration :=
  (drawing.getAt cell,config cell)

def RawCompatibleAt (drawing : PeriodicOrthogonalDrawing)
    (config : Cell → PortConfiguration) (cell : Cell) : Prop :=
  entry drawing config cell ∈ globalCellPortTable .I ∧
    ∀ side,
      entry drawing config (PeriodicOrthogonalDrawing.latticeNeighbor cell side) ∈ globalCellPortTable .I ∧
        (config cell).get side =
          (config (PeriodicOrthogonalDrawing.latticeNeighbor cell side)).get side.opposite

theorem entry_supported (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed)
    (config : Cell → PortConfiguration) (cell : Cell)
    (nearby : RawCompatibleAt drawing config cell) :
    entry drawing config cell ∈ supportedCellPortTable .I := by
  apply Finset.mem_filter.mpr
  refine ⟨nearby.1,?_⟩
  intro side
  cases colorMatch : (drawing.getAt cell).portColor side with
  | none =>
      simp only [CellPortEntrySupported,entry,colorMatch]
      exact iGlobalCellPortTable_unused ⟨_,nearby.1⟩ side colorMatch
  | some color =>
      simp only [CellPortEntrySupported,entry,colorMatch]
      refine ⟨⟨entry drawing config (PeriodicOrthogonalDrawing.latticeNeighbor cell side),
        (nearby.2 side).1⟩,?_,(nearby.2 side).2⟩
      have colors := drawing.portColor_latticeNeighbor_eq wf cell side
      rw [colorMatch] at colors
      exact colors.symm

theorem entry_separated (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed)
    (separated : drawing.VerticesSeparated) (config : Cell → PortConfiguration) (cell : Cell)
    (nearby : RawCompatibleAt drawing config cell)
    (neighbors : ∀ side, RawCompatibleAt drawing config
      (PeriodicOrthogonalDrawing.latticeNeighbor cell side)) :
    entry drawing config cell ∈ iSeparatedCellPortTable := by
  apply Finset.mem_filter.mpr
  refine ⟨entry_supported drawing wf config cell nearby,?_⟩
  intro isVertex side color colorMatch
  dsimp only [entry] at isVertex colorMatch
  refine ⟨⟨entry drawing config (PeriodicOrthogonalDrawing.latticeNeighbor cell side),
    entry_supported drawing wf config _ (neighbors side)⟩,?_,?_,(nearby.2 side).2⟩
  · exact drawing.verticesSeparatedAt separated cell side isVertex
  · have colors := drawing.portColor_latticeNeighbor_eq wf cell side
    rw [colorMatch] at colors
    exact colors.symm

def inward (drawing : PeriodicOrthogonalDrawing) (config : Cell → PortConfiguration)
    (cell : Cell) : Side → Bool := iConfigurationInward (drawing.getAt cell) (config cell)

theorem entry_of_state (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment .I drawing) (cell : Cell)
    (state : assignment cell ∈ exactCellTilings .I (drawing.getAt cell)) :
    entry drawing (selectedPortConfiguration .I drawing assignment) cell ∈ globalCellPortTable .I := by
  apply Finset.mem_biUnion.mpr
  refine ⟨drawing.getAt cell,Finset.mem_univ _,?_⟩
  apply Finset.mem_image.mpr
  refine ⟨selectedPortConfiguration .I drawing assignment cell,?_,rfl⟩
  apply (mem_exactCellPortConfigurations_iff .I (drawing.getAt cell) _).mpr
  exact ⟨assignment cell,(mem_exactCellTilings_iff .I (drawing.getAt cell) _).mp state,rfl⟩

private theorem extracted_coherent (drawing : PeriodicOrthogonalDrawing)
    (placements : Set (Placement Unit)) :
    IsGeometricallyCoherent .I drawing (localAssignmentFromGlobal .I drawing placements) :=
  isGeometricallyCoherent_of_mem_iff .I drawing _ placements
    (mem_drawingBlockFootprints_localAssignmentFromGlobal_iff .I drawing placements)

/-- Restricting a common placement set supplies local port compatibility
wherever the current and neighboring gadget windows have exact covers. -/
theorem raw_from_placements (drawing : PeriodicOrthogonalDrawing)
    (placements : Set (Placement Unit)) (cell : Cell)
    (state : localAssignmentFromGlobal .I drawing placements cell ∈ exactCellTilings .I (drawing.getAt cell))
    (neighbors : ∀ side,
      localAssignmentFromGlobal .I drawing placements (PeriodicOrthogonalDrawing.latticeNeighbor cell side) ∈
        exactCellTilings .I (drawing.getAt (PeriodicOrthogonalDrawing.latticeNeighbor cell side))) :
    RawCompatibleAt drawing
      (selectedPortConfiguration .I drawing (localAssignmentFromGlobal .I drawing placements)) cell := by
  refine ⟨entry_of_state drawing _ cell state,?_⟩
  intro side
  refine ⟨entry_of_state drawing _ _ (neighbors side),?_⟩
  exact PartialPortCompatibility.ports_agree .I drawing
    (localAssignmentFromGlobal .I drawing placements) cell state neighbors
    (extracted_coherent drawing placements) side

/-- The vertex constraint can be checked from local states within two
neighboring layers, without a tiling outside that neighborhood. -/
theorem vertex_sound (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed)
    (separated : drawing.VerticesSeparated) (config : Cell → PortConfiguration) (cell : Cell)
    (nearby : RawCompatibleAt drawing config cell)
    (neighbors : ∀ side, RawCompatibleAt drawing config
      (PeriodicOrthogonalDrawing.latticeNeighbor cell side)) :
    PeriodicOrthogonalDrawing.satisfiesOrientation (drawing.getAt cell) (inward drawing config cell) :=
  iLocalOrientationTableCorrect.1 ⟨_,entry_separated drawing wf separated config cell nearby neighbors⟩

/-- Adjacent states read opposite inward values on a shared colored edge. -/
theorem edge_opposite (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed)
    (separated : drawing.VerticesSeparated) (config : Cell → PortConfiguration)
    (cell : Cell) (side : Side) (color : WireColor)
    (colorMatch : (drawing.getAt cell).portColor side = some color)
    (nearby : RawCompatibleAt drawing config cell)
    (neighbors : ∀ s, RawCompatibleAt drawing config
      (PeriodicOrthogonalDrawing.latticeNeighbor cell s))
    (secondNeighbors : ∀ s, RawCompatibleAt drawing config
      (PeriodicOrthogonalDrawing.latticeNeighbor
        (PeriodicOrthogonalDrawing.latticeNeighbor cell side) s)) :
    inward drawing config cell side =
      !(inward drawing config (PeriodicOrthogonalDrawing.latticeNeighbor cell side) side.opposite) := by
  have colors := drawing.portColor_latticeNeighbor_eq wf cell side
  rw [colorMatch] at colors
  exact iLocalOrientationTableCorrect.2.2.2
    ⟨_,entry_separated drawing wf separated config cell nearby neighbors⟩
    ⟨_,entry_separated drawing wf separated config _ (neighbors side) secondNeighbors⟩
    side color colorMatch colors.symm (nearby.2 side).2

open Lean Elab Command in
run_cmd do
  for name in [``vertex_sound,``edge_opposite] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end PartialIOrientation
end LeanTrominoes.Gadget
