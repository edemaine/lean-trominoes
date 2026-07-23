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
