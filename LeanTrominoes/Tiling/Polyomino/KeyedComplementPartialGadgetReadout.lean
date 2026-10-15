/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Polyomino.KeyedComplementRecoveredWindowTilings
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetIPartialOrientation

/-! # Local graph orientations read from the original seeded P/Q tiling -/
namespace LeanTrominoes.KeyedPeriodicComplement.PartialGadgetReadout
open PlusRefinement Gadget

def Deep (n radius : Nat) (cell : Cell) : Prop :=
  (n : Int)+4+6*radius ≤ 6*cell.1 ∧
    6*cell.2+5 ≤ -(n : Int)-4-6*radius

theorem deep_mono {n small large : Nat} {cell : Cell}
    (bound : small ≤ large) (safe : Deep n large cell) : Deep n small cell := by
  dsimp [Deep] at safe ⊢
  omega

theorem deep_neighbor {n radius : Nat} {cell : Cell} (safe : Deep n (radius+1) cell) (side : Side) :
    Deep n radius (PeriodicOrthogonalDrawing.latticeNeighbor cell side) := by
  cases side <;> dsimp [Deep,PeriodicOrthogonalDrawing.latticeNeighbor] at safe ⊢ <;> omega

theorem window_deep {n : Nat} {cell : Cell} (safe : Deep n 0 cell) :
    ∀ p ∈ latticeBlockWindow cell, (n : Int)+4 ≤ p.1 ∧ p.2 ≤ -(n : Int)-4 := by
  intro p member
  obtain ⟨source,sourceMember,rfl⟩ := Finset.mem_image.mp member
  have bounds := (mem_rectangleCells_iff 6 6 source).mp sourceMember
  dsimp [Deep] at safe
  dsimp [latticeBlockOrigin,Cell.add]
  omega

def coarse (drawing : PeriodicOrthogonalDrawing) (ps : Set (Placement Bool)) : Set (Placement Unit) :=
  recoveredCoarse (drawing.periodicRegion .I).carrier ps

noncomputable def states (drawing : PeriodicOrthogonalDrawing) (ps : Set (Placement Bool)) :
    LocalTilingAssignment .I drawing := localAssignmentFromGlobal .I drawing (coarse drawing ps)

noncomputable def config (drawing : PeriodicOrthogonalDrawing) (ps : Set (Placement Bool)) :
    Cell → PortConfiguration := selectedPortConfiguration .I drawing (states drawing ps)

noncomputable def readout (drawing : PeriodicOrthogonalDrawing) (ps : Set (Placement Bool)) :
    drawing.Orientation := PartialIOrientation.inward drawing (config drawing ps)

section SeededTiling
variable {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
  (holes : Polyomino) (admissible : AdmissibleHoles n holes)
  (drawing : PeriodicOrthogonalDrawing)
  (carrier : holesRegion n holes = region (drawing.periodicRegion .I).carrier)
  (ps : Set (Placement Bool))
  (tiling : LeanTrominoes.IsTiling (pairTiles bumpy (tile n holes)) Set.univ ps)
  (seed : referencePlacement ∈ ps)
include hn period admissible carrier tiling seed

theorem localState {cell : Cell} (safe : Deep n 0 cell) :
    states drawing ps cell ∈ exactCellTilings .I (drawing.getAt cell) := by
  have restricted := recoveredCoarse_windowTiling hn period holes admissible
    (drawing.periodicRegion .I).carrier carrier ps tiling seed
    (latticeBlockWindow cell) (drawingBlockRegion .I drawing cell)
    (drawingBlockRegion_subset_window .I drawing cell)
    (fun p member => mem_periodicRegion_carrier_iff_of_mem_blockWindow .I drawing cell p member)
    (window_deep safe)
  have translated := restricted.translate (inverseLatticeBlockOrigin cell)
  apply (mem_exactCellTilings_iff .I (drawing.getAt cell) _).mpr
  change IsWindowTiling .I (rectangleCells 6 6)
    (orthogonalCellPixels .I (drawing.getAt cell)).toFinset
    (translatePlacements (inverseLatticeBlockOrigin cell)
      (globalWindowPlacements .I (latticeBlockWindow cell)
        (recoveredCoarse (drawing.periodicRegion .I).carrier ps)))
  simpa only [drawingBlockRegion,translate_inverse_latticeBlockWindow,
    translate_inverse_latticeBlockRegion] using translated

theorem rawCompatible {cell : Cell} (safe : Deep n 1 cell) :
    PartialIOrientation.RawCompatibleAt drawing (config drawing ps) cell := by
  apply PartialIOrientation.raw_from_placements drawing (coarse drawing ps) cell
  · exact localState hn period holes admissible drawing carrier ps tiling seed
      (deep_mono (by decide : 0 ≤ 1) safe)
  · intro side
    exact localState hn period holes admissible drawing carrier ps tiling seed
      (deep_neighbor safe side)

/-- Every sufficiently deep drawing vertex satisfies its orientation rule
in the original mixed tiling containing the prescribed Q. -/
theorem vertex_sound (wf : drawing.IsWellFormed) (separated : drawing.VerticesSeparated)
    {cell : Cell} (safe : Deep n 2 cell) :
    PeriodicOrthogonalDrawing.satisfiesOrientation (drawing.getAt cell) (readout drawing ps cell) := by
  apply PartialIOrientation.vertex_sound drawing wf separated (config drawing ps) cell
  · exact rawCompatible hn period holes admissible drawing carrier ps tiling seed
      (deep_mono (by decide : 1 ≤ 2) safe)
  · intro side
    exact rawCompatible hn period holes admissible drawing carrier ps tiling seed
      (deep_neighbor safe side)

/-- Readouts on both ends of a sufficiently deep colored edge are opposite. -/
theorem edge_opposite (wf : drawing.IsWellFormed) (separated : drawing.VerticesSeparated)
    {cell : Cell} (safe : Deep n 3 cell) (side : Side) (color : WireColor)
    (colorMatch : (drawing.getAt cell).portColor side = some color) :
    readout drawing ps cell side =
      !(readout drawing ps (PeriodicOrthogonalDrawing.latticeNeighbor cell side) side.opposite) := by
  apply PartialIOrientation.edge_opposite drawing wf separated (config drawing ps) cell side color colorMatch
  · exact rawCompatible hn period holes admissible drawing carrier ps tiling seed
      (deep_mono (by decide : 1 ≤ 3) safe)
  · intro s
    exact rawCompatible hn period holes admissible drawing carrier ps tiling seed
      (deep_mono (by decide : 1 ≤ 2) (deep_neighbor safe s))
  · intro s
    exact rawCompatible hn period holes admissible drawing carrier ps tiling seed
      (deep_neighbor (deep_neighbor safe side) s)

end SeededTiling

open Lean Elab Command in
run_cmd do
  for name in [``vertex_sound,``edge_opposite] do
    let axioms ← Lean.collectAxioms name
    let extra := axioms.filter fun ax =>
      ax != ``propext && ax != ``Classical.choice && ax != ``Quot.sound
    unless extra.isEmpty do throwError "{name} depends on unexpected axioms: {extra}"

end LeanTrominoes.KeyedPeriodicComplement.PartialGadgetReadout
