/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetITrichromaticPins
import LeanTrominoes.GadgetWindowPinRigidity
import LeanTrominoes.BumpySeedRefinement

/-! # Finite vertex prescriptions retain canonical I placements -/
noncomputable section
namespace LeanTrominoes.Gadget.CanonicalISelection

abbrev VertexSeed := List ((Cell × TrichromaticOrder) × Bool)

def Checked (drawing : PeriodicOrthogonalDrawing) (seed : VertexSeed) : Prop :=
  ∀ pin ∈ seed, drawing.getAt pin.1.1 = .trichromaticVertex pin.1.2

def Prescribed (drawing : PeriodicOrthogonalDrawing) (seed : VertexSeed) : Prop :=
  ∃ inward : drawing.Orientation, drawing.IsOrientation inward ∧
    ∀ pin ∈ seed, inward pin.1.1 .north = pin.2

def seedPlacements (seed : VertexSeed) : List (Placement Unit) :=
  seed.flatMap fun pin => (trichromaticPattern pin.1.2 pin.2).toList.map
    (translatePlacement (latticeBlockOrigin pin.1.1))

theorem prescribed_tiling (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed)
    (seed : VertexSeed) (checked : Checked drawing seed) (prescribed : Prescribed drawing seed) :
    PlusRefinement.Seeded Tromino.I.cells (drawing.periodicRegion .I).carrier (seedPlacements seed) := by
  obtain ⟨inward,valid,pins⟩ := prescribed
  refine ⟨placements drawing inward,placements_tiling drawing wf inward valid,?_⟩
  intro p member
  obtain ⟨pin,hpin,member⟩ := List.mem_flatMap.mp member
  obtain ⟨q,hq,rfl⟩ := List.mem_map.mp member
  refine ⟨pin.1.1,Finset.mem_image.mpr ⟨q,?_,rfl⟩⟩
  change q ∈ pattern (drawing.getAt pin.1.1) (inward pin.1.1)
  rw [checked pin hpin]
  rw [trichromaticPattern_eq _ _ (by simpa only [← checked pin hpin] using valid.1 pin.1.1)
    pin.2 (pins pin hpin)]
  exact Finset.mem_toList.mp hq

private theorem inverse_translate (cell : Cell) (pattern : Finset (Placement Unit)) :
    translatePlacements (inverseLatticeBlockOrigin cell)
      (translatePlacements (latticeBlockOrigin cell) pattern) = pattern := by
  simp only [translatePlacements,Finset.image_image,Function.comp_def]
  have inverse (p : Placement Unit) : translatePlacement (inverseLatticeBlockOrigin cell)
      (translatePlacement (latticeBlockOrigin cell) p) = p := by
    apply Placement.ext
    · rfl
    · rfl
    · ext <;> simp [translatePlacement,inverseLatticeBlockOrigin,latticeBlockOrigin,Cell.add]
  simp_rw [inverse]
  exact Finset.image_id

theorem local_state_of_pins (drawing : PeriodicOrthogonalDrawing)
    (ps : Set (Placement Unit))
    (tiling : IsTiling (fun _ => Tromino.I.cells) (drawing.periodicRegion .I).carrier ps)
    (cell : Cell) (pattern : Finset (Placement Unit))
    (valid : pattern ∈ exactCellTilings .I (drawing.getAt cell))
    (pins : ∀ p ∈ translatePlacements (latticeBlockOrigin cell) pattern, p ∈ ps) :
    localAssignmentFromGlobal .I drawing ps cell = pattern := by
  have translated : IsWindowTiling .I (latticeBlockWindow cell)
      (drawingBlockRegion .I drawing cell) (translatePlacements (latticeBlockOrigin cell) pattern) := by
    simpa only [latticeBlockWindow,drawingBlockRegion,latticeBlockRegion,
      orthogonalCellGadget,paperGadget,Gadget.window,Gadget.region] using
      ((mem_exactCellTilings_iff _ _ _).1 valid).translate (latticeBlockOrigin cell)
  have fixed := window_pin_rigidity .I (drawing.periodicRegion .I).carrier ps tiling.tilesInside
    (fun _ hp _ hq different => tiling.disjoint_cells hp hq different)
    (latticeBlockWindow cell) (drawingBlockRegion .I drawing cell)
    (fun c member => mem_periodicRegion_carrier_iff_of_mem_blockWindow .I drawing cell c member)
    (translatePlacements (latticeBlockOrigin cell) pattern) translated pins
  unfold localAssignmentFromGlobal localPlacementsFromGlobal
  rw [fixed,inverse_translate]

theorem seeded_tiling_iff (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed)
    (separated : drawing.VerticesSeparated) (seed : VertexSeed) (checked : Checked drawing seed) :
    PlusRefinement.Seeded Tromino.I.cells (drawing.periodicRegion .I).carrier (seedPlacements seed) ↔
      Prescribed drawing seed := by
  constructor
  · rintro ⟨ps,tiling,pins⟩
    let assignment := localAssignmentFromGlobal .I drawing ps
    refine ⟨iOrientationFromAssignment drawing assignment,
      iIsOrientation_of_compatibleAssignment drawing wf separated assignment
        (localAssignmentFromGlobal_isLocallyTiled .I drawing ps tiling)
        (localAssignmentFromGlobal_isPortCompatible .I drawing ps tiling),?_⟩
    intro pin hpin
    have state := local_state_of_pins drawing ps tiling pin.1.1
      (trichromaticPattern pin.1.2 pin.2)
      (by rw [checked pin hpin]; exact trichromaticPattern_exact _ _) (by
        intro p hp
        obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp hp
        exact pins _ (List.mem_flatMap.mpr ⟨pin,hpin,
          List.mem_map.mpr ⟨q,Finset.mem_toList.mpr hq,rfl⟩⟩))
    change iConfigurationInward (drawing.getAt pin.1.1)
      (portConfiguration .I (orthogonalCellGadget .I (drawing.getAt pin.1.1))
        (localAssignmentFromGlobal .I drawing ps pin.1.1)) .north = pin.2
    rw [state,checked pin hpin]
    exact trichromaticPattern_readout _ _
  · exact prescribed_tiling drawing wf seed checked

end LeanTrominoes.Gadget.CanonicalISelection
