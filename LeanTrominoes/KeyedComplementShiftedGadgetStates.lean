/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.KeyedComplementDeepPins
import LeanTrominoes.TilingRegionTranslation

/-! # Recovering gadget states after the fixed corner-margin translation -/
noncomputable section
namespace LeanTrominoes.KeyedPeriodicComplement.ShiftedGadgetReadout
open PlusRefinement Gadget
attribute [local irreducible] localAssignmentFromGlobal
attribute [local irreducible] globalWindowPlacements exactCellTilings admissibleCandidates windowCandidates

def original (drawing : PeriodicOrthogonalDrawing) (shift : Cell) : Set Cell :=
  {c | Cell.add (latticeBlockOrigin shift) c ∈ (drawing.periodicRegion .I).carrier}

def inverseOffset (shift : Cell) : Cell := Cell.sub (0,0) (latticeBlockOrigin shift)

def coarse (drawing : PeriodicOrthogonalDrawing) (shift : Cell) (ps : Set (Placement Bool)) :
    Set (Placement Unit) := {p | p.shift (inverseOffset shift) ∈ recoveredCoarse (original drawing shift) ps}

def states (drawing : PeriodicOrthogonalDrawing) (shift : Cell) (ps : Set (Placement Bool)) :
    LocalTilingAssignment .I drawing := localAssignmentFromGlobal .I drawing (coarse drawing shift ps)

def config (drawing : PeriodicOrthogonalDrawing) (shift : Cell) (ps : Set (Placement Bool)) :
    Cell → PortConfiguration := selectedPortConfiguration .I drawing (states drawing shift ps)

def readout (drawing : PeriodicOrthogonalDrawing) (shift : Cell) (ps : Set (Placement Bool)) :
    drawing.Orientation := PartialIOrientation.inward drawing (config drawing shift ps)

def Deep (n radius : Nat) (shift cell : Cell) : Prop := PartialGadgetReadout.Deep n radius (Cell.sub cell shift)

theorem deep_mono {n small large : Nat} {shift cell : Cell} (bound : small ≤ large)
    (safe : Deep n large shift cell) : Deep n small shift cell := PartialGadgetReadout.deep_mono bound safe

theorem deep_neighbor {n radius : Nat} {shift cell : Cell} (safe : Deep n (radius+1) shift cell)
    (side : Side) : Deep n radius shift (PeriodicOrthogonalDrawing.latticeNeighbor cell side) := by
  have neighbor := PartialGadgetReadout.deep_neighbor safe side
  have equal : Cell.sub (PeriodicOrthogonalDrawing.latticeNeighbor cell side) shift =
      PeriodicOrthogonalDrawing.latticeNeighbor (Cell.sub cell shift) side := by
    cases side <;> ext <;> simp [Cell.sub,PeriodicOrthogonalDrawing.latticeNeighbor] <;> omega
  simpa only [Deep,equal] using neighbor

theorem window_deep {n : Nat} {shift cell : Cell} (safe : Deep n 0 shift cell) :
    ∀ c ∈ latticeBlockWindow cell,
      (n : Int)+4 ≤ (Cell.add (inverseOffset shift) c).1 ∧
        (Cell.add (inverseOffset shift) c).2 ≤ -(n : Int)-4 := by
  intro c member
  obtain ⟨pixel,hpixel,rfl⟩ := Finset.mem_image.mp member
  have bounds := (mem_rectangleCells_iff 6 6 pixel).1 hpixel
  dsimp [Deep,PartialGadgetReadout.Deep,Cell.sub] at safe
  dsimp [inverseOffset,latticeBlockOrigin,Cell.add,Cell.sub]
  omega

theorem original_back (drawing : PeriodicOrthogonalDrawing) (shift c : Cell) :
    Cell.add (inverseOffset shift) c ∈ original drawing shift ↔
      c ∈ (drawing.periodicRegion .I).carrier := by
  have cancel : Cell.add (latticeBlockOrigin shift) (Cell.add (inverseOffset shift) c) = c := by
    ext <;> simp [inverseOffset,Cell.sub,Cell.add]
  change _ ∈ (drawing.periodicRegion .I).carrier ↔ _
  rw [cancel]

theorem coarse_inside (drawing : PeriodicOrthogonalDrawing) (shift : Cell) (ps : Set (Placement Bool))
    {p : Placement Unit} (member : p ∈ coarse drawing shift ps) :
    ∀ c ∈ p.cells (fun _ => Tromino.I.cells), c ∈ (drawing.periodicRegion .I).carrier := by
  intro c hc
  apply (original_back drawing shift c).1
  exact member.2 _ ((Placement.mem_shift_cells _ _ _ _).2 hc)

section SeededTiling
variable {n : Nat} (hn : 96 ≤ n) (period : (n : Int) % 3 = 0)
  (holes : Polyomino) (admissible : AdmissibleHoles n holes)
  (drawing : PeriodicOrthogonalDrawing) (shift : Cell)
  (carrier : holesRegion n holes = region (original drawing shift))
  (ps : Set (Placement Bool))
  (tiling : LeanTrominoes.IsTiling (pairTiles bumpy (tile n holes)) Set.univ ps)
  (seed : referencePlacement ∈ ps)
include hn period admissible carrier tiling seed

theorem localState {cell : Cell} (safe : Deep n 0 shift cell) :
    states drawing shift ps cell ∈ exactCellTilings .I (drawing.getAt cell) := by
  have shiftedTiling := (recoveredCoarse_tiling (original drawing shift) ps tiling).recenter_region (inverseOffset shift)
  have restricted := Gadget.IsTiling.isWindowTiling shiftedTiling
    (latticeBlockWindow cell) (drawingBlockRegion .I drawing cell)
    (drawingBlockRegion_subset_window .I drawing cell) (by
      intro c hc
      rw [← mem_periodicRegion_carrier_iff_of_mem_blockWindow .I drawing cell c hc]
      change Cell.add (inverseOffset shift) c ∈ recoveredRegion (original drawing shift) ps ↔ _
      constructor
      · rintro ⟨p,member,cover⟩
        exact (original_back drawing shift c).1 (member.2 _ cover)
      · intro member
        have bounds := window_deep safe c hc
        obtain ⟨p,⟨hp,cover⟩,_⟩ := recoveredCoarse_uniqueCover hn period holes admissible
          (original drawing shift) carrier ps tiling seed ((original_back drawing shift c).2 member)
          bounds.1 bounds.2
        exact ⟨p,hp,cover⟩)
  have translated := restricted.translate (inverseLatticeBlockOrigin cell)
  apply (mem_exactCellTilings_iff .I (drawing.getAt cell) _).2
  unfold states localAssignmentFromGlobal localPlacementsFromGlobal
  change IsWindowTiling .I (rectangleCells 6 6)
    (orthogonalCellPixels .I (drawing.getAt cell)).toFinset
    (translatePlacements (inverseLatticeBlockOrigin cell)
      (globalWindowPlacements .I (latticeBlockWindow cell) (coarse drawing shift ps)))
  simpa only [coarse,drawingBlockRegion,translate_inverse_latticeBlockWindow,
    translate_inverse_latticeBlockRegion] using translated

theorem rawCompatible {cell : Cell} (safe : Deep n 1 shift cell) :
    PartialIOrientation.RawCompatibleAt drawing (config drawing shift ps) cell := by
  apply PartialIOrientation.raw_from_placements drawing (coarse drawing shift ps) cell
  · exact localState hn period holes admissible drawing shift carrier ps tiling seed (deep_mono (by decide) safe)
  · intro side
    exact localState hn period holes admissible drawing shift carrier ps tiling seed (deep_neighbor safe side)

theorem vertex_sound (wf : drawing.IsWellFormed) (separated : drawing.VerticesSeparated)
    {cell : Cell} (safe : Deep n 2 shift cell) :
    PeriodicOrthogonalDrawing.satisfiesOrientation (drawing.getAt cell) (readout drawing shift ps cell) := by
  apply PartialIOrientation.vertex_sound drawing wf separated (config drawing shift ps) cell
  · exact rawCompatible hn period holes admissible drawing shift carrier ps tiling seed (deep_mono (by decide) safe)
  · intro side
    exact rawCompatible hn period holes admissible drawing shift carrier ps tiling seed (deep_neighbor safe side)

theorem edge_opposite (wf : drawing.IsWellFormed) (separated : drawing.VerticesSeparated)
    {cell : Cell} (safe : Deep n 3 shift cell) (side : Side) (color : WireColor)
    (colorMatch : (drawing.getAt cell).portColor side = some color) :
    readout drawing shift ps cell side =
      !(readout drawing shift ps (PeriodicOrthogonalDrawing.latticeNeighbor cell side) side.opposite) := by
  apply PartialIOrientation.edge_opposite drawing wf separated (config drawing shift ps) cell side color colorMatch
  · exact rawCompatible hn period holes admissible drawing shift carrier ps tiling seed (deep_mono (by decide) safe)
  · intro s
    exact rawCompatible hn period holes admissible drawing shift carrier ps tiling seed
      (deep_mono (by decide) (deep_neighbor safe s))
  · intro s
    exact rawCompatible hn period holes admissible drawing shift carrier ps tiling seed
      (deep_neighbor (deep_neighbor safe side) s)

end SeededTiling
end LeanTrominoes.KeyedPeriodicComplement.ShiftedGadgetReadout
