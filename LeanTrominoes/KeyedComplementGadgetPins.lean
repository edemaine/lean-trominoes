/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementPartialGadgetReadout
import LeanTrominoes.GadgetWindowPinRigidity

/-! # Finite P prescriptions fix the recovered gadget orientation -/
namespace LeanTrominoes.KeyedPeriodicComplement.PartialGadgetReadout
open PlusRefinement Gadget

private theorem translatePlacements_inverse (cell : Cell) (pattern : Finset (Placement Unit)) :
    translatePlacements (inverseLatticeBlockOrigin cell)
      (translatePlacements (latticeBlockOrigin cell) pattern) = pattern := by
  simp only [translatePlacements,Finset.image_image,Function.comp_def]
  have inverse (p : Placement Unit) :
      translatePlacement (inverseLatticeBlockOrigin cell)
        (translatePlacement (latticeBlockOrigin cell) p) = p := by
    apply Placement.ext
    · rfl
    · rfl
    · apply Prod.ext <;>
        simp [translatePlacement,inverseLatticeBlockOrigin,latticeBlockOrigin,Cell.add]
  simp_rw [inverse]
  exact Finset.image_id

/-- Prescribing the translated refined copies of a finite exact local
pattern forces that pattern to be the decoded gadget state. -/
theorem states_eq_of_pins (drawing : PeriodicOrthogonalDrawing) (ps : Set (Placement Bool))
    {q : Polyomino} (tiling : LeanTrominoes.IsTiling (pairTiles bumpy q) Set.univ ps)
    (cell : Cell) (pattern : Finset (Placement Unit))
    (valid : IsWindowTiling .I
      (orthogonalCellGadget .I (drawing.getAt cell)).window
      (orthogonalCellGadget .I (drawing.getAt cell)).region pattern)
    (inside : ∀ p ∈ translatePlacements (latticeBlockOrigin cell) pattern,
      ∀ c ∈ p.cells (fun _ => Tromino.I.cells), c ∈ (drawing.periodicRegion .I).carrier)
    (pins : ∀ p ∈ translatePlacements (latticeBlockOrigin cell) pattern,
      (expandPlacement p).tag false ∈ ps) : states drawing ps cell = pattern := by
  have translated : IsWindowTiling .I (latticeBlockWindow cell)
      (drawingBlockRegion .I drawing cell) (translatePlacements (latticeBlockOrigin cell) pattern) := by
    simpa only [latticeBlockWindow,drawingBlockRegion,latticeBlockRegion,
      orthogonalCellGadget,paperGadget,Gadget.window,Gadget.region] using
      valid.translate (latticeBlockOrigin cell)
  have fixed := recovered_window_pin_rigidity (drawing.periodicRegion .I).carrier ps tiling
    (latticeBlockWindow cell) (drawingBlockRegion .I drawing cell)
    (fun c member => mem_periodicRegion_carrier_iff_of_mem_blockWindow .I drawing cell c member)
    (translatePlacements (latticeBlockOrigin cell) pattern) translated inside pins
  unfold states localAssignmentFromGlobal localPlacementsFromGlobal coarse
  rw [fixed,translatePlacements_inverse]

theorem readout_eq_of_pins (drawing : PeriodicOrthogonalDrawing) (ps : Set (Placement Bool))
    {q : Polyomino} (tiling : LeanTrominoes.IsTiling (pairTiles bumpy q) Set.univ ps)
    (cell : Cell) (pattern : Finset (Placement Unit))
    (valid : IsWindowTiling .I
      (orthogonalCellGadget .I (drawing.getAt cell)).window
      (orthogonalCellGadget .I (drawing.getAt cell)).region pattern)
    (inside : ∀ p ∈ translatePlacements (latticeBlockOrigin cell) pattern,
      ∀ c ∈ p.cells (fun _ => Tromino.I.cells), c ∈ (drawing.periodicRegion .I).carrier)
    (pins : ∀ p ∈ translatePlacements (latticeBlockOrigin cell) pattern,
      (expandPlacement p).tag false ∈ ps) :
    readout drawing ps cell = iConfigurationInward (drawing.getAt cell)
      (portConfiguration .I (orthogonalCellGadget .I (drawing.getAt cell)) pattern) := by
  unfold readout PartialIOrientation.inward config selectedPortConfiguration
  rw [states_eq_of_pins drawing ps tiling cell pattern valid inside pins]

open Lean Elab Command in
run_cmd do
  let name := ``readout_eq_of_pins
  let axioms ← Lean.collectAxioms name
  let extra := axioms.filter fun ax =>
    ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
  unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.KeyedPeriodicComplement.PartialGadgetReadout
