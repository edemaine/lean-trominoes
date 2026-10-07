/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.GadgetIPreferredSelection
import LeanTrominoes.CanonicalIPlacements
import LeanTrominoes.GadgetWindowTilingImage

/-! # A global I tiling retaining every canonical local placement -/
noncomputable section
namespace LeanTrominoes.Gadget.CanonicalISelection

def pattern (kind : OrthogonalCellType) (inward : Side → Bool) : Finset (Placement Unit) :=
  (PreferredISelection.pattern kind inward).image CanonicalI.normalize

theorem pattern_exact (kind : OrthogonalCellType) (inward : Side → Bool)
    (valid : PeriodicOrthogonalDrawing.satisfiesOrientation kind inward) :
    pattern kind inward ∈ exactCellTilings .I kind :=
  (mem_exactCellTilings_iff _ _ _).2
    (IsWindowTiling.image_same_cells
      ((mem_exactCellTilings_iff _ _ _).1 (PreferredISelection.pattern_spec kind inward valid).1)
      CanonicalI.normalize CanonicalI.normalize_cells)

theorem pattern_canonical (kind : OrthogonalCellType) (inward : Side → Bool)
    {p : Placement Unit} (member : p ∈ pattern kind inward) : CanonicalI.Canonical p := by
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp member
  exact CanonicalI.normalize_canonical q

theorem pattern_ports (kind : OrthogonalCellType) (inward : Side → Bool) :
    portConfiguration .I (orthogonalCellGadget .I kind) (pattern kind inward) =
      portConfiguration .I (orthogonalCellGadget .I kind) (PreferredISelection.pattern kind inward) :=
  portConfiguration_image_same_cells _ _ _ _ CanonicalI.normalize_cells

theorem pattern_eq_of_active_eq (kind : OrthogonalCellType) (a b : Side → Bool)
    (same : ∀ side, (kind.portColor side).isSome → a side = b side) :
    pattern kind a = pattern kind b :=
  congrArg (Finset.image CanonicalI.normalize) (PreferredISelection.pattern_eq_of_active_eq kind a b same)

def assignment (drawing : PeriodicOrthogonalDrawing) (inward : drawing.Orientation) :
    LocalTilingAssignment .I drawing := fun cell => pattern (drawing.getAt cell) (inward cell)

theorem assignment_locallyTiled (drawing : PeriodicOrthogonalDrawing)
    (inward : drawing.Orientation) (valid : drawing.IsOrientation inward) :
    IsLocallyTiled .I drawing (assignment drawing inward) :=
  fun cell => pattern_exact _ _ (valid.1 cell)

theorem assignment_ports (drawing : PeriodicOrthogonalDrawing) (inward : drawing.Orientation) (cell : Cell) :
    selectedPortConfiguration .I drawing (assignment drawing inward) cell =
      selectedPortConfiguration .I drawing (PreferredISelection.assignment drawing inward) cell :=
  pattern_ports _ _

theorem assignment_compatible (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed)
    (inward : drawing.Orientation) (valid : drawing.IsOrientation inward) :
    IsPortCompatible .I drawing (assignment drawing inward) := by
  constructor <;> intro cell
  · change (selectedPortConfiguration .I drawing (assignment drawing inward) cell).east =
      (selectedPortConfiguration .I drawing (assignment drawing inward)
        (PeriodicOrthogonalDrawing.latticeNeighbor cell .east)).west
    rw [assignment_ports,assignment_ports]
    exact PreferredISelection.assignment_ports drawing wf inward valid cell .east
  · change (selectedPortConfiguration .I drawing (assignment drawing inward) cell).south =
      (selectedPortConfiguration .I drawing (assignment drawing inward)
        (PeriodicOrthogonalDrawing.latticeNeighbor cell .south)).north
    rw [assignment_ports,assignment_ports]
    exact PreferredISelection.assignment_ports drawing wf inward valid cell .south

def placements (drawing : PeriodicOrthogonalDrawing) (inward : drawing.Orientation) : Set (Placement Unit) :=
  {p | ∃ cell, p ∈ translatePlacements (latticeBlockOrigin cell) (assignment drawing inward cell)}

theorem placements_canonical (drawing : PeriodicOrthogonalDrawing) (inward : drawing.Orientation)
    {p : Placement Unit} (member : p ∈ placements drawing inward) : CanonicalI.Canonical p := by
  obtain ⟨cell,member⟩ := member
  obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp member
  exact CanonicalI.translate_canonical _ (pattern_canonical _ _ hq)

private theorem footprint_mem_iff (drawing : PeriodicOrthogonalDrawing) (inward : drawing.Orientation)
    (footprint : Finset Cell) :
    (∃ cell, footprint ∈ drawingBlockFootprints .I drawing (assignment drawing inward) cell) ↔
      ∃ p ∈ placements drawing inward, p.cells (fun _ => Tromino.I.cells) = footprint := by
  constructor
  · rintro ⟨cell,member⟩
    obtain ⟨localFootprint,localMember,rfl⟩ := Finset.mem_image.mp member
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp localMember
    exact ⟨translatePlacement (latticeBlockOrigin cell) p,
      ⟨cell,Finset.mem_image.mpr ⟨p,hp,rfl⟩⟩,translatePlacement_cells _ _ _⟩
  · rintro ⟨p,⟨cell,member⟩,rfl⟩
    obtain ⟨q,hq,rfl⟩ := Finset.mem_image.mp member
    refine ⟨cell,?_⟩
    rw [translatePlacement_cells]
    exact Finset.mem_image.mpr ⟨_,Finset.mem_image.mpr ⟨q,hq,rfl⟩,rfl⟩

theorem placements_tiling (drawing : PeriodicOrthogonalDrawing) (wf : drawing.IsWellFormed)
    (inward : drawing.Orientation) (valid : drawing.IsOrientation inward) :
    IsTiling (fun _ => Tromino.I.cells) (drawing.periodicRegion .I).carrier (placements drawing inward) := by
  let atlas := footprintAtlasOfAssignment .I drawing (assignment drawing inward)
    (assignment_locallyTiled drawing inward valid)
    (isGeometricallyCoherent_of_portCompatible .I drawing _
      (assignment_locallyTiled drawing inward valid) (assignment_compatible drawing wf inward valid))
  have carrier : atlas.carrier = (drawing.periodicRegion .I).carrier := by
    change liftedGadgetCarrier .I drawing = _
    rw [liftedGadgetCarrier_eq_expandedCarrier,PeriodicOrthogonalDrawing.periodicRegion_carrier_eq]
  have tiling := atlas.isFootprintTiling
  rw [carrier] at tiling
  have member (p : Placement Unit) (hp : p ∈ placements drawing inward) :
      p.cells (fun _ => Tromino.I.cells) ∈ atlas.selected :=
    (footprint_mem_iff drawing inward _).2 ⟨p,hp,rfl⟩
  constructor
  · intro p hp c hc
    exact (tiling.tilesInside _ (member p hp)).2 c hc
  · intro c hc
    obtain ⟨footprint,⟨hf,hfc⟩,unique⟩ := tiling.uniqueCover c hc
    obtain ⟨p,hp,equal⟩ := (footprint_mem_iff drawing inward footprint).1 hf
    refine ⟨p,⟨hp,by rwa [equal]⟩,?_⟩
    rintro q ⟨hq,hqc⟩
    apply CanonicalI.canonical_cells_injective (placements_canonical drawing inward hq)
      (placements_canonical drawing inward hp)
    exact (unique _ ⟨member q hq,hqc⟩).trans equal.symm

end LeanTrominoes.Gadget.CanonicalISelection
