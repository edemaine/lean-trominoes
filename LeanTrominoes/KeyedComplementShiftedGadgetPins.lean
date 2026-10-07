/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementShiftedGadgetStates
import LeanTrominoes.GadgetITrichromaticPins

/-! # Prescribed P patterns fix gadget states after the corner translation -/
noncomputable section
namespace LeanTrominoes.KeyedPeriodicComplement.ShiftedGadgetReadout
open PlusRefinement Gadget
attribute [local irreducible] localAssignmentFromGlobal
attribute [local irreducible] globalWindowPlacements exactCellTilings admissibleCandidates windowCandidates

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

theorem states_eq_of_deep_pins {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (drawing : PeriodicOrthogonalDrawing) (shift : Cell)
    (carrier : holesRegion n holes = region (original drawing shift))
    (ps : Set (Placement Bool))
    (tiling : LeanTrominoes.IsTiling (pairTiles bumpy (tile n holes)) Set.univ ps)
    (seed : referencePlacement ∈ ps) (cell : Cell) (safe : Deep n 0 shift cell)
    (pattern : Finset (Placement Unit))
    (valid : pattern ∈ exactCellTilings .I (drawing.getAt cell))
    (pins : ∀ p ∈ translatePlacements (latticeBlockOrigin cell) pattern,
      (expandPlacement (p.shift (inverseOffset shift))).tag false ∈ ps) :
    states drawing shift ps cell = pattern := by
  have translated : IsWindowTiling .I (latticeBlockWindow cell)
      (drawingBlockRegion .I drawing cell) (translatePlacements (latticeBlockOrigin cell) pattern) := by
    simpa only [latticeBlockWindow,drawingBlockRegion,latticeBlockRegion,
      orthogonalCellGadget,paperGadget,Gadget.window,Gadget.region] using
      ((mem_exactCellTilings_iff _ _ _).1 valid).translate (latticeBlockOrigin cell)
  have fixedPins : ∀ p ∈ translatePlacements (latticeBlockOrigin cell) pattern,
      p ∈ coarse drawing shift ps := by
    intro p member
    have candidate := translated.1 member
    obtain ⟨c,hc,cover⟩ := ((mem_admissibleCandidates_iff .I
      (latticeBlockWindow cell) (drawingBlockRegion .I drawing cell) p).1 candidate).1
    have bounds := window_deep safe c hc
    exact ⟨pins p member,deep_coarse_pin_inside hn period holes admissible _ carrier ps tiling seed
      (p.shift (inverseOffset shift)) (pins p member)
      ((Placement.mem_shift_cells _ _ _ _).2 cover) bounds.1 bounds.2⟩
  have shiftedTiling := (recoveredCoarse_tiling (original drawing shift) ps tiling).recenter_region (inverseOffset shift)
  have fixed := window_pin_rigidity .I (drawing.periodicRegion .I).carrier
    (coarse drawing shift ps) (fun _ member => coarse_inside drawing shift ps member)
    (fun _ hp _ hq different => shiftedTiling.disjoint_cells hp hq different)
    (latticeBlockWindow cell) (drawingBlockRegion .I drawing cell)
    (fun c member => mem_periodicRegion_carrier_iff_of_mem_blockWindow .I drawing cell c member)
    (translatePlacements (latticeBlockOrigin cell) pattern) translated fixedPins
  unfold states localAssignmentFromGlobal localPlacementsFromGlobal
  rw [fixed,inverse_translate]

theorem readout_eq_of_deep_pins {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
    (holes : Polyomino) (admissible : AdmissibleHoles n holes)
    (drawing : PeriodicOrthogonalDrawing) (shift : Cell)
    (carrier : holesRegion n holes = region (original drawing shift))
    (ps : Set (Placement Bool))
    (tiling : LeanTrominoes.IsTiling (pairTiles bumpy (tile n holes)) Set.univ ps)
    (seed : referencePlacement ∈ ps) (cell : Cell) (safe : Deep n 0 shift cell)
    (pattern : Finset (Placement Unit))
    (valid : pattern ∈ exactCellTilings .I (drawing.getAt cell))
    (pins : ∀ p ∈ translatePlacements (latticeBlockOrigin cell) pattern,
      (expandPlacement (p.shift (inverseOffset shift))).tag false ∈ ps) :
    readout drawing shift ps cell = iConfigurationInward (drawing.getAt cell)
      (portConfiguration .I (orthogonalCellGadget .I (drawing.getAt cell)) pattern) := by
  unfold readout PartialIOrientation.inward config selectedPortConfiguration
  rw [states_eq_of_deep_pins hn period holes admissible drawing shift carrier ps tiling seed
    cell safe pattern valid pins]

end LeanTrominoes.KeyedPeriodicComplement.ShiftedGadgetReadout
