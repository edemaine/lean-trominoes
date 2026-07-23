import LeanTrominoes.FootprintTiling
import LeanTrominoes.GadgetPorts

/-!
# Geometric assembly interface for tromino gadgets

The executable gadget search returns finite sets of `Placement`s, while
neighboring ports retain only their occupied-cell footprints.  This file
connects those representations: every verified open-window tiling induces an
exact local footprint cover, and all four ports are functions of that cover.
-/

namespace LeanTrominoes
namespace Gadget

/-- Forget representation-level placement data in one local tiling. -/
def windowFootprints (tromino : Tromino)
    (placements : Finset (Placement Unit)) : Finset (Finset Cell) :=
  placements.image fun placement =>
    placement.cells (fun _ : Unit => tromino.cells)

/-- The geometric content of a valid open-window tiling. Every selected
footprint is a tromino meeting the window, its visible cells are allowed, and
the target region is covered exactly once. -/
structure IsWindowFootprintTiling (tromino : Tromino)
    (window region : Finset Cell) (footprints : Finset (Finset Cell)) : Prop where
  isFootprint :
    ∀ footprint ∈ footprints, tromino.IsFootprint footprint
  meetsWindow :
    ∀ footprint ∈ footprints, ∃ cell ∈ window, cell ∈ footprint
  visibleInside :
    ∀ footprint ∈ footprints, footprint ∩ window ⊆ region
  uniqueCover :
    ∀ cell ∈ region,
      ∃! footprint : Finset Cell, footprint ∈ footprints ∧ cell ∈ footprint

/-- The card-one clause in an open-window tiling provides its usual unique
cover formulation. -/
theorem IsWindowTiling.uniqueCover {tromino : Tromino}
    {window region : Finset Cell} {placements : Finset (Placement Unit)}
    (tiling : IsWindowTiling tromino window region placements)
    {cell : Cell} (cellMember : cell ∈ region) :
    ∃! placement : Placement Unit,
      placement ∈ placements ∧
        cell ∈ placement.cells (fun _ : Unit => tromino.cells) := by
  obtain ⟨placement, filteredEquality⟩ :=
    Finset.card_eq_one.mp (tiling.2 cell cellMember)
  have placementFiltered :
      placement ∈ placements.filter fun candidate =>
        cell ∈ candidate.cells (fun _ : Unit => tromino.cells) := by
    rw [filteredEquality]
    simp
  refine ⟨placement, Finset.mem_filter.mp placementFiltered, ?_⟩
  intro other otherCovers
  have otherFiltered :
      other ∈ placements.filter fun candidate =>
        cell ∈ candidate.cells (fun _ : Unit => tromino.cells) :=
    Finset.mem_filter.mpr otherCovers
  rw [filteredEquality] at otherFiltered
  simpa using otherFiltered

/-- Quotienting a verified local placement tiling by geometric footprint
preserves exact coverage and every admissibility condition. -/
theorem IsWindowTiling.isWindowFootprintTiling {tromino : Tromino}
    {window region : Finset Cell} {placements : Finset (Placement Unit)}
    (tiling : IsWindowTiling tromino window region placements) :
    IsWindowFootprintTiling tromino window region
      (windowFootprints tromino placements) := by
  constructor
  · intro footprint footprintMember
    obtain ⟨placement, placementMember, rfl⟩ :=
      Finset.mem_image.mp footprintMember
    exact ⟨placement, rfl⟩
  · intro footprint footprintMember
    obtain ⟨placement, placementMember, rfl⟩ :=
      Finset.mem_image.mp footprintMember
    exact ((mem_admissibleCandidates_iff tromino window region placement).mp
      (tiling.1 placementMember)).1
  · intro footprint footprintMember
    obtain ⟨placement, placementMember, rfl⟩ :=
      Finset.mem_image.mp footprintMember
    exact ((mem_admissibleCandidates_iff tromino window region placement).mp
      (tiling.1 placementMember)).2
  · intro cell cellMember
    obtain ⟨placement, placementCovers, unique⟩ :=
      tiling.uniqueCover cellMember
    let footprint := placement.cells (fun _ : Unit => tromino.cells)
    refine ⟨footprint, ⟨Finset.mem_image.mpr ⟨placement,
      placementCovers.1, rfl⟩, placementCovers.2⟩, ?_⟩
    intro otherFootprint otherCovers
    obtain ⟨otherPlacement, otherPlacementMember, otherEquality⟩ :=
      Finset.mem_image.mp otherCovers.1
    have otherPlacementCovers :
        cell ∈ otherPlacement.cells (fun _ : Unit => tromino.cells) := by
      rw [otherEquality]
      exact otherCovers.2
    have placementEquality := unique otherPlacement
      ⟨otherPlacementMember, otherPlacementCovers⟩
    simpa only [footprint, placementEquality] using otherEquality.symm

/-- The footprints that geometrically cross the boundary of a window. -/
def footprintBoundary (window : Finset Cell)
    (footprints : Finset (Finset Cell)) : PortState :=
  footprints.filter fun footprint => ¬ footprint ⊆ window

/-- The boundary signature computed from placements is exactly the boundary
filter of their geometric footprints. -/
theorem boundarySignature_eq_footprintBoundary (tromino : Tromino)
    (window : Finset Cell) (placements : Finset (Placement Unit)) :
    boundarySignature tromino window placements =
      footprintBoundary window (windowFootprints tromino placements) := by
  ext footprint
  simp only [boundarySignature, boundaryPlacements, footprintBoundary,
    windowFootprints, Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨placement, ⟨placementMember, crossesBoundary⟩, rfl⟩
    exact ⟨⟨placement, placementMember, rfl⟩, crossesBoundary⟩
  · rintro ⟨⟨placement, placementMember, footprintEquality⟩,
      crossesBoundary⟩
    refine ⟨placement, ⟨placementMember, ?_⟩, footprintEquality⟩
    simpa only [footprintEquality] using crossesBoundary

/-- Compute all four ports directly from a local geometric footprint cover. -/
def footprintPortConfiguration (gadget : Gadget)
    (footprints : Finset (Finset Cell)) : PortConfiguration :=
  let boundary := footprintBoundary gadget.window footprints
  { north := northPortState boundary
    east := rightPortState gadget.width boundary
    south := southPortState gadget.height boundary
    west := leftPortState boundary }

/-- Port extraction factors through the geometric footprint quotient. -/
theorem portConfiguration_eq_footprintPortConfiguration (tromino : Tromino)
    (gadget : Gadget) (placements : Finset (Placement Unit)) :
    portConfiguration tromino gadget placements =
      footprintPortConfiguration gadget (windowFootprints tromino placements) := by
  rw [portConfiguration, footprintPortConfiguration,
    boundarySignature_eq_footprintBoundary]

/-! ## Translation invariance -/

/-- Translate a placement without changing its prototile kind or symmetry. -/
def translatePlacement (offset : Cell) (placement : Placement Unit) :
    Placement Unit :=
  { placement with offset := Cell.add offset placement.offset }

/-- Translating a placement translates exactly its geometric footprint. -/
theorem translatePlacement_cells (tromino : Tromino) (offset : Cell)
    (placement : Placement Unit) :
    (translatePlacement offset placement).cells
        (fun _ : Unit => tromino.cells) =
      translateFootprint offset
        (placement.cells (fun _ : Unit => tromino.cells)) := by
  ext cell
  simp only [Placement.cells, translatePlacement, translateFootprint,
    Finset.mem_image]
  constructor
  · rintro ⟨source, sourceMember, rfl⟩
    refine ⟨Cell.add placement.offset (placement.symmetry.act source),
      ⟨source, sourceMember, rfl⟩, ?_⟩
    simp only [Cell.add, Prod.mk.injEq]
    omega
  · rintro ⟨translatedSource, ⟨source, sourceMember, sourceEquality⟩,
      translatedEquality⟩
    refine ⟨source, sourceMember, ?_⟩
    subst translatedSource
    rw [← translatedEquality]
    simp only [Cell.add, Prod.mk.injEq]
    omega

/-- Membership in a translated footprint, evaluated at the corresponding
translated cell. -/
theorem add_mem_translateFootprint_iff (offset cell : Cell)
    (footprint : Finset Cell) :
    Cell.add offset cell ∈ translateFootprint offset footprint ↔
      cell ∈ footprint := by
  simp only [translateFootprint, Finset.mem_image]
  constructor
  · rintro ⟨source, sourceMember, equality⟩
    exact (Cell.add_left_injective offset equality) ▸ sourceMember
  · intro cellMember
    exact ⟨cell, cellMember, rfl⟩

/-- Translation acts injectively on finite geometric footprints. -/
theorem translateFootprint_injective (offset : Cell) :
    Function.Injective (translateFootprint offset) := by
  intro first second equality
  ext cell
  rw [← add_mem_translateFootprint_iff offset cell first,
    equality, add_mem_translateFootprint_iff]

/-- Successive footprint translations compose by adding their offsets. -/
theorem translateFootprint_translate (first second : Cell)
    (footprint : Finset Cell) :
    translateFootprint first (translateFootprint second footprint) =
      translateFootprint (Cell.add first second) footprint := by
  rw [translateFootprint, translateFootprint, translateFootprint,
    Finset.image_image]
  apply Finset.image_congr
  intro cell cellMember
  apply Prod.ext <;> simp only [Function.comp_apply, Cell.add] <;> omega

@[simp]
theorem translateFootprint_zero (footprint : Finset Cell) :
    translateFootprint (0, 0) footprint = footprint := by
  ext cell
  simp [translateFootprint, Cell.add]

/-- Translate every footprint in a finite local cover. -/
def translateFootprints (offset : Cell)
    (footprints : Finset (Finset Cell)) : Finset (Finset Cell) :=
  footprints.image (translateFootprint offset)

/-- Exact geometric window covers are invariant under a common translation
of the window, target region, and selected footprints. -/
theorem IsWindowFootprintTiling.translate {tromino : Tromino}
    {window region : Finset Cell} {footprints : Finset (Finset Cell)}
    (tiling : IsWindowFootprintTiling tromino window region footprints)
    (offset : Cell) :
    IsWindowFootprintTiling tromino
      (translateFootprint offset window)
      (translateFootprint offset region)
      (translateFootprints offset footprints) := by
  constructor
  · intro translated translatedMember
    obtain ⟨footprint, footprintMember, rfl⟩ :=
      Finset.mem_image.mp translatedMember
    obtain ⟨placement, placementEquality⟩ :=
      tiling.isFootprint footprint footprintMember
    refine ⟨translatePlacement offset placement, ?_⟩
    rw [translatePlacement_cells, placementEquality]
  · intro translated translatedMember
    obtain ⟨footprint, footprintMember, rfl⟩ :=
      Finset.mem_image.mp translatedMember
    obtain ⟨cell, cellInWindow, cellInFootprint⟩ :=
      tiling.meetsWindow footprint footprintMember
    exact ⟨Cell.add offset cell,
      (add_mem_translateFootprint_iff offset cell window).mpr cellInWindow,
      (add_mem_translateFootprint_iff offset cell footprint).mpr
        cellInFootprint⟩
  · intro translated translatedMember cell cellMember
    obtain ⟨footprint, footprintMember, rfl⟩ :=
      Finset.mem_image.mp translatedMember
    obtain ⟨cellInFootprint, cellInWindow⟩ :=
      Finset.mem_inter.mp cellMember
    obtain ⟨footprintCell, footprintCellMember, footprintCellEquality⟩ :=
      Finset.mem_image.mp cellInFootprint
    obtain ⟨windowCell, windowCellMember, windowCellEquality⟩ :=
      Finset.mem_image.mp cellInWindow
    have sourceEquality : footprintCell = windowCell :=
      Cell.add_left_injective offset
        (footprintCellEquality.trans windowCellEquality.symm)
    subst windowCell
    have regionMember := tiling.visibleInside footprint footprintMember
      (Finset.mem_inter.mpr ⟨footprintCellMember, windowCellMember⟩)
    exact Finset.mem_image.mpr
      ⟨footprintCell, regionMember, footprintCellEquality⟩
  · intro cell cellMember
    obtain ⟨sourceCell, sourceCellMember, sourceCellEquality⟩ :=
      Finset.mem_image.mp cellMember
    obtain ⟨footprint, footprintCovers, unique⟩ :=
      tiling.uniqueCover sourceCell sourceCellMember
    refine ⟨translateFootprint offset footprint,
      ⟨Finset.mem_image.mpr ⟨footprint, footprintCovers.1, rfl⟩, ?_⟩, ?_⟩
    · rw [← sourceCellEquality]
      exact (add_mem_translateFootprint_iff offset sourceCell footprint).mpr
        footprintCovers.2
    · intro otherTranslated otherCovers
      obtain ⟨otherFootprint, otherFootprintMember, otherEquality⟩ :=
        Finset.mem_image.mp otherCovers.1
      have sourceCovered : sourceCell ∈ otherFootprint := by
        apply (add_mem_translateFootprint_iff offset sourceCell
          otherFootprint).mp
        rw [sourceCellEquality, otherEquality]
        exact otherCovers.2
      have footprintEquality := unique otherFootprint
        ⟨otherFootprintMember, sourceCovered⟩
      simpa only [footprintEquality] using otherEquality.symm

/-! ## The `6 × 6` lattice-block atlas -/

/-- Origin of the gadget block indexed by an arbitrary cell of the infinite
normalized drawing. -/
def latticeBlockOrigin (location : Cell) : Cell :=
  (6 * location.1, 6 * location.2)

/-- The translated `6 × 6` window at one infinite drawing location. -/
def latticeBlockWindow (location : Cell) : Finset Cell :=
  translateFootprint (latticeBlockOrigin location) (rectangleCells 6 6)

/-- Translate a local paper-pixel mask into one infinite drawing block. -/
def latticeBlockRegion (location : Cell) (localRegion : Finset Cell) :
    Finset Cell :=
  translateFootprint (latticeBlockOrigin location) localRegion

/-- The integer plane is covered by the `6 × 6` windows indexed by the
Euclidean quotients of its coordinates. -/
theorem latticeBlockWindows_cover (cell : Cell) :
    ∃ location, cell ∈ latticeBlockWindow location := by
  let location : Cell := (cell.1 / 6, cell.2 / 6)
  let localCell : Cell := (cell.1 % 6, cell.2 % 6)
  refine ⟨location, Finset.mem_image.mpr ⟨localCell, ?_, ?_⟩⟩
  · rw [mem_rectangleCells_iff]
    constructor
    · exact Int.emod_nonneg cell.1 (by omega)
    constructor
    · exact Int.emod_lt_of_pos cell.1 (by omega)
    constructor
    · exact Int.emod_nonneg cell.2 (by omega)
    · exact Int.emod_lt_of_pos cell.2 (by omega)
  · have horizontal := Int.emod_add_mul_ediv cell.1 6
    have vertical := Int.emod_add_mul_ediv cell.2 6
    apply Prod.ext
    · simp only [latticeBlockOrigin, location, localCell, Cell.add]
      omega
    · simp only [latticeBlockOrigin, location, localCell, Cell.add]
      omega

/-- Translating a local region contained in the paper window preserves that
containment in its lattice block. -/
theorem latticeBlockRegion_subset (location : Cell)
    {localRegion : Finset Cell} (inside : localRegion ⊆ rectangleCells 6 6) :
    latticeBlockRegion location localRegion ⊆ latticeBlockWindow location := by
  intro cell cellMember
  obtain ⟨source, sourceMember, sourceEquality⟩ :=
    Finset.mem_image.mp cellMember
  exact Finset.mem_image.mpr ⟨source, inside sourceMember, sourceEquality⟩

/-! ## Abstract local-to-global gluing -/

/-- A plane-covering family of finite windows equipped with mutually
consistent exact local footprint covers. The coherence field says that a
selected footprint is recorded in every window that it meets. -/
structure FootprintAtlas (tromino : Tromino) {index : Type*}
    (windows regions : index → Finset Cell) where
  footprints : index → Finset (Finset Cell)
  regionInside : ∀ location, regions location ⊆ windows location
  windowsCover : ∀ cell, ∃ location, cell ∈ windows location
  localTiling : ∀ location,
    IsWindowFootprintTiling tromino (windows location) (regions location)
      (footprints location)
  coherent : ∀ first second footprint,
    footprint ∈ footprints first →
      (∃ cell ∈ windows second, cell ∈ footprint) →
        footprint ∈ footprints second

namespace FootprintAtlas

/-- The union of all target regions in an atlas. -/
def carrier {tromino : Tromino} {index : Type*}
    {windows regions : index → Finset Cell}
    (_atlas : FootprintAtlas tromino windows regions) : Set Cell :=
  { cell | ∃ location, cell ∈ regions location }

/-- The union of all selected geometric tromino footprints in an atlas. -/
def selected {tromino : Tromino} {index : Type*}
    {windows regions : index → Finset Cell}
    (atlas : FootprintAtlas tromino windows regions) : Set (Finset Cell) :=
  { footprint | ∃ location, footprint ∈ atlas.footprints location }

/-- Mutually coherent exact local covers glue to an exact global geometric
tromino tiling of the union of their target regions. -/
theorem isFootprintTiling {tromino : Tromino} {index : Type*}
    {windows regions : index → Finset Cell}
    (atlas : FootprintAtlas tromino windows regions) :
    Tromino.IsFootprintTiling tromino atlas.carrier atlas.selected := by
  constructor
  · intro footprint footprintMember
    obtain ⟨first, firstMember⟩ := footprintMember
    refine ⟨(atlas.localTiling first).isFootprint footprint firstMember, ?_⟩
    intro cell cellMember
    obtain ⟨second, cellInWindow⟩ := atlas.windowsCover cell
    have secondMember := atlas.coherent first second footprint firstMember
      ⟨cell, cellInWindow, cellMember⟩
    have visibleMember : cell ∈ footprint ∩ windows second :=
      Finset.mem_inter.mpr ⟨cellMember, cellInWindow⟩
    exact ⟨second,
      (atlas.localTiling second).visibleInside footprint secondMember
        visibleMember⟩
  · intro cell cellMember
    obtain ⟨location, cellInRegion⟩ := cellMember
    obtain ⟨footprint, footprintCovers, unique⟩ :=
      (atlas.localTiling location).uniqueCover cell cellInRegion
    refine ⟨footprint, ⟨⟨location, footprintCovers.1⟩,
      footprintCovers.2⟩, ?_⟩
    intro otherFootprint otherCovers
    obtain ⟨otherLocation, otherMember⟩ := otherCovers.1
    have cellInWindow := atlas.regionInside location cellInRegion
    have otherLocalMember := atlas.coherent otherLocation location
      otherFootprint otherMember ⟨cell, cellInWindow, otherCovers.2⟩
    exact unique otherFootprint ⟨otherLocalMember, otherCovers.2⟩

/-- The placement-based tileability consequence of the atlas gluing theorem. -/
theorem tileable {tromino : Tromino} {index : Type*}
    {windows regions : index → Finset Cell}
    (atlas : FootprintAtlas tromino windows regions) :
    tromino.Tileable atlas.carrier :=
  (tromino.tileable_iff_exists_footprintTiling atlas.carrier).mpr
    ⟨atlas.selected, atlas.isFootprintTiling⟩

end FootprintAtlas

end Gadget
end LeanTrominoes
