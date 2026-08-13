/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetAssembly
import LeanTrominoes.GadgetSubstitution

/-!
# Infinite compatible assignments of local gadget tilings

The substitution proof factors through a finite-state constraint system on
the infinite lifted drawing.  At every drawing cell we select one local tiling
certified by exact-cover search. Neighboring selections must have identical
normalized geometric port states along their shared side.
-/

namespace LeanTrominoes
namespace Gadget

/-- Verified exact-cover enumeration specialized to one cell of the complete
Figure 11/12 gadget alphabet. -/
def exactCellTilings (tromino : Tromino) (cellType : OrthogonalCellType) :
    List (Finset (Placement Unit)) :=
  exactWindowTilings tromino (orthogonalCellGadget tromino cellType)
    (orthogonalCellPixels tromino cellType)

/-- Membership in the executable local-state list is exactly the semantic
open-window tiling predicate. -/
theorem mem_exactCellTilings_iff (tromino : Tromino)
    (cellType : OrthogonalCellType) (placements : Finset (Placement Unit)) :
    placements ∈ exactCellTilings tromino cellType ↔
      IsWindowTiling tromino
        (orthogonalCellGadget tromino cellType).window
        (orthogonalCellGadget tromino cellType).region placements := by
  exact mem_exactWindowTilings_iff tromino
    (orthogonalCellGadget tromino cellType)
    (orthogonalCellGadget_wellFormed tromino cellType)
    (orthogonalCellPixels tromino cellType) rfl placements

/-- The four-port behavior of all verified local tilings of one drawing-cell
type. -/
def exactCellPortConfigurations (tromino : Tromino)
    (cellType : OrthogonalCellType) : Finset PortConfiguration :=
  exactPortConfigurations tromino (orthogonalCellGadget tromino cellType)
    (orthogonalCellPixels tromino cellType)

/-- The executable port behavior has the expected semantic interpretation. -/
theorem mem_exactCellPortConfigurations_iff (tromino : Tromino)
    (cellType : OrthogonalCellType) (configuration : PortConfiguration) :
    configuration ∈ exactCellPortConfigurations tromino cellType ↔
      ∃ placements,
        IsWindowTiling tromino
          (orthogonalCellGadget tromino cellType).window
          (orthogonalCellGadget tromino cellType).region placements ∧
        portConfiguration tromino
          (orthogonalCellGadget tromino cellType) placements = configuration := by
  exact mem_exactPortConfigurations_iff tromino
    (orthogonalCellGadget tromino cellType)
    (orthogonalCellGadget_wellFormed tromino cellType)
    (orthogonalCellPixels tromino cellType) rfl configuration

/-- One local placement selection at every cell of the infinite lifted
drawing. Placements use coordinates relative to their own `6 × 6` block. -/
abbrev LocalTilingAssignment (_tromino : Tromino)
    (_drawing : PeriodicOrthogonalDrawing) :=
  Cell → Finset (Placement Unit)

/-- Every selected local state is one of the states returned by verified
exact-cover search. -/
def IsLocallyTiled (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing) : Prop :=
  ∀ location,
    assignment location ∈ exactCellTilings tromino (drawing.getAt location)

/-- Neighboring local tilings retain exactly the same geometric tromino
footprints at every shared block boundary. -/
def IsPortCompatible (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing) : Prop :=
  (∀ location,
    HorizontallyCompatible
      (portConfiguration tromino
        (orthogonalCellGadget tromino (drawing.getAt location))
        (assignment location))
      (portConfiguration tromino
        (orthogonalCellGadget tromino
          (drawing.getAt
            (PeriodicOrthogonalDrawing.latticeNeighbor location .east)))
        (assignment
          (PeriodicOrthogonalDrawing.latticeNeighbor location .east)))) ∧
  ∀ location,
    VerticallyCompatible
      (portConfiguration tromino
        (orthogonalCellGadget tromino (drawing.getAt location))
        (assignment location))
      (portConfiguration tromino
        (orthogonalCellGadget tromino
          (drawing.getAt
            (PeriodicOrthogonalDrawing.latticeNeighbor location .south)))
        (assignment
          (PeriodicOrthogonalDrawing.latticeNeighbor location .south))
      )

/-- The intermediate infinite finite-state system implemented by the tromino
gadget library. -/
def HasCompatibleGadgetTiling (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : Prop :=
  ∃ assignment : LocalTilingAssignment tromino drawing,
    IsLocallyTiled tromino drawing assignment ∧
      IsPortCompatible tromino drawing assignment

/-- The local selected footprints translated to their global lattice
coordinates. -/
def drawingBlockFootprints (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (location : Cell) : Finset (Finset Cell) :=
  translateFootprints (latticeBlockOrigin location)
    (windowFootprints tromino (assignment location))

/-- Every selected tromino footprint occurs in every lattice block that it
meets. -/
def IsGeometricallyCoherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing) : Prop :=
  ∀ first second footprint,
    footprint ∈ drawingBlockFootprints tromino drawing assignment first →
      (∃ cell ∈ latticeBlockWindow second, cell ∈ footprint) →
        footprint ∈ drawingBlockFootprints tromino drawing assignment second

/-- Any block footprint family characterized by a common selected placement
set and intersection with the block windows is geometrically coherent. -/
theorem isGeometricallyCoherent_of_mem_iff (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (placements : Set (Placement Unit))
    (membership : ∀ location footprint,
      footprint ∈ drawingBlockFootprints tromino drawing assignment location ↔
        ∃ placement ∈ placements,
          placement.cells (fun _ : Unit => tromino.cells) = footprint ∧
            ∃ cell ∈ latticeBlockWindow location, cell ∈ footprint) :
    IsGeometricallyCoherent tromino drawing assignment := by
  intro first second footprint footprintMember meetsSecond
  obtain ⟨placement, placementSelected, placementEquality, meetsFirst⟩ :=
    (membership first footprint).mp footprintMember
  exact (membership second footprint).mpr
      ⟨placement, placementSelected, placementEquality, meetsSecond⟩

/-- Every selected global-coordinate block footprint is a genuine tromino and
meets the block in which it was selected. -/
theorem drawingBlockFootprint_shape_and_meets (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (location : Cell) (footprint : Finset Cell)
    (footprintMember :
      footprint ∈ drawingBlockFootprints tromino drawing assignment location) :
    tromino.IsFootprint footprint ∧
      ∃ cell ∈ latticeBlockWindow location, cell ∈ footprint := by
  have localPlacementTiling :=
    (mem_exactCellTilings_iff tromino (drawing.getAt location)
      (assignment location)).mp (locallyTiled location)
  have translatedTiling :=
    localPlacementTiling.isWindowFootprintTiling.translate
      (latticeBlockOrigin location)
  have translatedMember :
      footprint ∈ translateFootprints (latticeBlockOrigin location)
        (windowFootprints tromino (assignment location)) := by
    exact footprintMember
  refine ⟨translatedTiling.isFootprint footprint translatedMember, ?_⟩
  simpa only [orthogonalCellGadget, paperGadget, Gadget.window,
    latticeBlockWindow] using
      translatedTiling.meetsWindow footprint translatedMember

/-- A selected local footprint is a tromino meeting the paper window and it
cannot occupy any window corner, because every Figure 11/12 mask omits them. -/
theorem localFootprint_geometry (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (location : Cell) (footprint : Finset Cell)
    (footprintMember : footprint ∈
      windowFootprints tromino (assignment location)) :
    tromino.IsFootprint footprint ∧
      (∃ cell ∈ rectangleCells 6 6, cell ∈ footprint) ∧
      (0, 0) ∉ footprint ∧ (5, 0) ∉ footprint ∧
      (0, 5) ∉ footprint ∧ (5, 5) ∉ footprint := by
  have placementTiling :=
    (mem_exactCellTilings_iff tromino (drawing.getAt location)
      (assignment location)).mp (locallyTiled location)
  have footprintTiling := placementTiling.isWindowFootprintTiling
  have cornerMask :=
    orthogonalCellPixels_corners_absent tromino (drawing.getAt location)
  have cornerAbsent (corner : Cell)
      (cornerInWindow : corner ∈
        (orthogonalCellGadget tromino (drawing.getAt location)).window)
      (cornerNotInRegion : corner ∉
        (orthogonalCellGadget tromino (drawing.getAt location)).region) :
      corner ∉ footprint := by
    intro cornerMember
    apply cornerNotInRegion
    exact footprintTiling.visibleInside footprint footprintMember
      (Finset.mem_inter.mpr ⟨cornerMember, cornerInWindow⟩)
  have topLeftWindow : (0, 0) ∈
      (orthogonalCellGadget tromino (drawing.getAt location)).window := by
    simp [orthogonalCellGadget, paperGadget, Gadget.window,
      mem_rectangleCells_iff]
  have topRightWindow : (5, 0) ∈
      (orthogonalCellGadget tromino (drawing.getAt location)).window := by
    simp [orthogonalCellGadget, paperGadget, Gadget.window,
      mem_rectangleCells_iff]
  have bottomLeftWindow : (0, 5) ∈
      (orthogonalCellGadget tromino (drawing.getAt location)).window := by
    simp [orthogonalCellGadget, paperGadget, Gadget.window,
      mem_rectangleCells_iff]
  have bottomRightWindow : (5, 5) ∈
      (orthogonalCellGadget tromino (drawing.getAt location)).window := by
    simp [orthogonalCellGadget, paperGadget, Gadget.window,
      mem_rectangleCells_iff]
  refine ⟨footprintTiling.isFootprint footprint footprintMember,
    ?_, ?_, ?_, ?_, ?_⟩
  · simpa only [orthogonalCellGadget, paperGadget, Gadget.window] using
      footprintTiling.meetsWindow footprint footprintMember
  · apply cornerAbsent (0, 0) topLeftWindow
    simpa only [orthogonalCellGadget, paperGadget, Gadget.region] using
      cornerMask.1
  · apply cornerAbsent (5, 0) topRightWindow
    simpa only [orthogonalCellGadget, paperGadget, Gadget.region] using
      cornerMask.2.1
  · apply cornerAbsent (0, 5) bottomLeftWindow
    simpa only [orthogonalCellGadget, paperGadget, Gadget.region] using
      cornerMask.2.2.1
  · apply cornerAbsent (5, 5) bottomRightWindow
    simpa only [orthogonalCellGadget, paperGadget, Gadget.region] using
      cornerMask.2.2.2

@[simp]
theorem translate_east_neighbor_window (location : Cell) :
    translateFootprint (latticeBlockOrigin location)
        (translateFootprint (6, 0) (rectangleCells 6 6)) =
      latticeBlockWindow
        (PeriodicOrthogonalDrawing.latticeNeighbor location .east) := by
  rw [translateFootprint_translate, latticeBlockWindow]
  congr 1
  apply Prod.ext <;>
    simp [latticeBlockOrigin, PeriodicOrthogonalDrawing.latticeNeighbor,
      Cell.add] ;
    ring

@[simp]
theorem translate_west_neighbor_window (location : Cell) :
    translateFootprint (latticeBlockOrigin location)
        (translateFootprint (-6, 0) (rectangleCells 6 6)) =
      latticeBlockWindow
        (PeriodicOrthogonalDrawing.latticeNeighbor location .west) := by
  rw [translateFootprint_translate, latticeBlockWindow]
  congr 1
  apply Prod.ext <;>
    simp [latticeBlockOrigin, PeriodicOrthogonalDrawing.latticeNeighbor,
      Cell.add] ;
    ring

@[simp]
theorem translate_south_neighbor_window (location : Cell) :
    translateFootprint (latticeBlockOrigin location)
        (translateFootprint (0, 6) (rectangleCells 6 6)) =
      latticeBlockWindow
        (PeriodicOrthogonalDrawing.latticeNeighbor location .south) := by
  rw [translateFootprint_translate, latticeBlockWindow]
  congr 1
  apply Prod.ext <;>
    simp [latticeBlockOrigin, PeriodicOrthogonalDrawing.latticeNeighbor,
      Cell.add] ;
    ring

@[simp]
theorem translate_north_neighbor_window (location : Cell) :
    translateFootprint (latticeBlockOrigin location)
        (translateFootprint (0, -6) (rectangleCells 6 6)) =
      latticeBlockWindow
        (PeriodicOrthogonalDrawing.latticeNeighbor location .north) := by
  rw [translateFootprint_translate, latticeBlockWindow]
  congr 1
  apply Prod.ext <;>
    simp [latticeBlockOrigin, PeriodicOrthogonalDrawing.latticeNeighbor,
      Cell.add] ;
    ring

/-! ## Adjacent footprint propagation from geometric coherence -/

/-- Coherence propagates an east-crossing local footprint to the eastern
neighbor's local coordinates. -/
theorem east_footprint_mem_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment)
    (location : Cell) (footprint : Finset Cell)
    (footprintMember : footprint ∈
      windowFootprints tromino (assignment location))
    (crosses : crossesRight 6 footprint) :
    translateFootprint (-6, 0) footprint ∈ windowFootprints tromino
      (assignment
        (PeriodicOrthogonalDrawing.latticeNeighbor location .east)) := by
  have geometry := localFootprint_geometry tromino drawing assignment
    locallyTiled location footprint footprintMember
  have meetsLocalEast :=
    Tromino.IsFootprint.meets_east_neighbor_of_corners_absent geometry.1
      geometry.2.1 geometry.2.2.2.1 geometry.2.2.2.2.2 crosses
  let globalFootprint :=
    translateFootprint (latticeBlockOrigin location) footprint
  have globalMember : globalFootprint ∈
      drawingBlockFootprints tromino drawing assignment location := by
    exact Finset.mem_image.mpr ⟨footprint, footprintMember, rfl⟩
  have meetsGlobalEast : ∃ cell ∈ latticeBlockWindow
      (PeriodicOrthogonalDrawing.latticeNeighbor location .east),
      cell ∈ globalFootprint := by
    obtain ⟨cell, cellInEastWindow, cellInFootprint⟩ := meetsLocalEast
    refine ⟨Cell.add (latticeBlockOrigin location) cell, ?_, ?_⟩
    · rw [← translate_east_neighbor_window location]
      exact (add_mem_translateFootprint_iff (latticeBlockOrigin location) cell
        (translateFootprint (6, 0) (rectangleCells 6 6))).mpr
          cellInEastWindow
    · exact (add_mem_translateFootprint_iff (latticeBlockOrigin location)
        cell footprint).mpr cellInFootprint
  have globalEast := coherent location
    (PeriodicOrthogonalDrawing.latticeNeighbor location .east)
    globalFootprint globalMember meetsGlobalEast
  obtain ⟨eastFootprint, eastMember, eastEquality⟩ :=
    Finset.mem_image.mp globalEast
  have expectedEquality :
      translateFootprint
          (latticeBlockOrigin
            (PeriodicOrthogonalDrawing.latticeNeighbor location .east))
          (translateFootprint (-6, 0) footprint) = globalFootprint := by
    rw [translateFootprint_translate]
    have offsetEquality :
        Cell.add
          (latticeBlockOrigin
            (PeriodicOrthogonalDrawing.latticeNeighbor location .east))
          (-6, 0) = latticeBlockOrigin location := by
      apply Prod.ext <;>
        simp [latticeBlockOrigin,
          PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add] ;
        ring
    rw [offsetEquality]
  have eastFootprintEquality :
      eastFootprint = translateFootprint (-6, 0) footprint := by
    apply translateFootprint_injective
      (latticeBlockOrigin
        (PeriodicOrthogonalDrawing.latticeNeighbor location .east))
    exact eastEquality.trans expectedEquality.symm
  exact eastFootprintEquality ▸ eastMember

/-- Coherence propagates a west-crossing local footprint to the western
neighbor's local coordinates. -/
theorem west_footprint_mem_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment)
    (location : Cell) (footprint : Finset Cell)
    (footprintMember : footprint ∈
      windowFootprints tromino (assignment location))
    (crosses : crossesLeft footprint) :
    translateFootprint (6, 0) footprint ∈ windowFootprints tromino
      (assignment
        (PeriodicOrthogonalDrawing.latticeNeighbor location .west)) := by
  have geometry := localFootprint_geometry tromino drawing assignment
    locallyTiled location footprint footprintMember
  have meetsLocalWest :=
    Tromino.IsFootprint.meets_west_neighbor_of_corners_absent geometry.1
      geometry.2.1 geometry.2.2.1 geometry.2.2.2.2.1 crosses
  let globalFootprint :=
    translateFootprint (latticeBlockOrigin location) footprint
  have globalMember : globalFootprint ∈
      drawingBlockFootprints tromino drawing assignment location := by
    exact Finset.mem_image.mpr ⟨footprint, footprintMember, rfl⟩
  have meetsGlobalWest : ∃ cell ∈ latticeBlockWindow
      (PeriodicOrthogonalDrawing.latticeNeighbor location .west),
      cell ∈ globalFootprint := by
    obtain ⟨cell, cellInWestWindow, cellInFootprint⟩ := meetsLocalWest
    refine ⟨Cell.add (latticeBlockOrigin location) cell, ?_, ?_⟩
    · rw [← translate_west_neighbor_window location]
      exact (add_mem_translateFootprint_iff (latticeBlockOrigin location) cell
        (translateFootprint (-6, 0) (rectangleCells 6 6))).mpr
          cellInWestWindow
    · exact (add_mem_translateFootprint_iff (latticeBlockOrigin location)
        cell footprint).mpr cellInFootprint
  have globalWest := coherent location
    (PeriodicOrthogonalDrawing.latticeNeighbor location .west)
    globalFootprint globalMember meetsGlobalWest
  obtain ⟨westFootprint, westMember, westEquality⟩ :=
    Finset.mem_image.mp globalWest
  have expectedEquality :
      translateFootprint
          (latticeBlockOrigin
            (PeriodicOrthogonalDrawing.latticeNeighbor location .west))
          (translateFootprint (6, 0) footprint) = globalFootprint := by
    rw [translateFootprint_translate]
    have offsetEquality :
        Cell.add
          (latticeBlockOrigin
            (PeriodicOrthogonalDrawing.latticeNeighbor location .west))
          (6, 0) = latticeBlockOrigin location := by
      apply Prod.ext <;>
        simp [latticeBlockOrigin,
          PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add] ;
        ring
    rw [offsetEquality]
  have westFootprintEquality :
      westFootprint = translateFootprint (6, 0) footprint := by
    apply translateFootprint_injective
      (latticeBlockOrigin
        (PeriodicOrthogonalDrawing.latticeNeighbor location .west))
    exact westEquality.trans expectedEquality.symm
  exact westFootprintEquality ▸ westMember

/-- Coherence propagates a south-crossing local footprint to the southern
neighbor's local coordinates. -/
theorem south_footprint_mem_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment)
    (location : Cell) (footprint : Finset Cell)
    (footprintMember : footprint ∈
      windowFootprints tromino (assignment location))
    (crosses : crossesSouth 6 footprint) :
    translateFootprint (0, -6) footprint ∈ windowFootprints tromino
      (assignment
        (PeriodicOrthogonalDrawing.latticeNeighbor location .south)) := by
  have geometry := localFootprint_geometry tromino drawing assignment
    locallyTiled location footprint footprintMember
  have meetsLocalSouth :=
    Tromino.IsFootprint.meets_south_neighbor_of_corners_absent geometry.1
      geometry.2.1 geometry.2.2.2.2.1 geometry.2.2.2.2.2 crosses
  let globalFootprint :=
    translateFootprint (latticeBlockOrigin location) footprint
  have globalMember : globalFootprint ∈
      drawingBlockFootprints tromino drawing assignment location := by
    exact Finset.mem_image.mpr ⟨footprint, footprintMember, rfl⟩
  have meetsGlobalSouth : ∃ cell ∈ latticeBlockWindow
      (PeriodicOrthogonalDrawing.latticeNeighbor location .south),
      cell ∈ globalFootprint := by
    obtain ⟨cell, cellInSouthWindow, cellInFootprint⟩ := meetsLocalSouth
    refine ⟨Cell.add (latticeBlockOrigin location) cell, ?_, ?_⟩
    · rw [← translate_south_neighbor_window location]
      exact (add_mem_translateFootprint_iff (latticeBlockOrigin location) cell
        (translateFootprint (0, 6) (rectangleCells 6 6))).mpr
          cellInSouthWindow
    · exact (add_mem_translateFootprint_iff (latticeBlockOrigin location)
        cell footprint).mpr cellInFootprint
  have globalSouth := coherent location
    (PeriodicOrthogonalDrawing.latticeNeighbor location .south)
    globalFootprint globalMember meetsGlobalSouth
  obtain ⟨southFootprint, southMember, southEquality⟩ :=
    Finset.mem_image.mp globalSouth
  have expectedEquality :
      translateFootprint
          (latticeBlockOrigin
            (PeriodicOrthogonalDrawing.latticeNeighbor location .south))
          (translateFootprint (0, -6) footprint) = globalFootprint := by
    rw [translateFootprint_translate]
    have offsetEquality :
        Cell.add
          (latticeBlockOrigin
            (PeriodicOrthogonalDrawing.latticeNeighbor location .south))
          (0, -6) = latticeBlockOrigin location := by
      apply Prod.ext <;>
        simp [latticeBlockOrigin,
          PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add] ;
        ring
    rw [offsetEquality]
  have southFootprintEquality :
      southFootprint = translateFootprint (0, -6) footprint := by
    apply translateFootprint_injective
      (latticeBlockOrigin
        (PeriodicOrthogonalDrawing.latticeNeighbor location .south))
    exact southEquality.trans expectedEquality.symm
  exact southFootprintEquality ▸ southMember

/-- Coherence propagates a north-crossing local footprint to the northern
neighbor's local coordinates. -/
theorem north_footprint_mem_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment)
    (location : Cell) (footprint : Finset Cell)
    (footprintMember : footprint ∈
      windowFootprints tromino (assignment location))
    (crosses : crossesNorth footprint) :
    translateFootprint (0, 6) footprint ∈ windowFootprints tromino
      (assignment
        (PeriodicOrthogonalDrawing.latticeNeighbor location .north)) := by
  have geometry := localFootprint_geometry tromino drawing assignment
    locallyTiled location footprint footprintMember
  have meetsLocalNorth :=
    Tromino.IsFootprint.meets_north_neighbor_of_corners_absent geometry.1
      geometry.2.1 geometry.2.2.1 geometry.2.2.2.1 crosses
  let globalFootprint :=
    translateFootprint (latticeBlockOrigin location) footprint
  have globalMember : globalFootprint ∈
      drawingBlockFootprints tromino drawing assignment location := by
    exact Finset.mem_image.mpr ⟨footprint, footprintMember, rfl⟩
  have meetsGlobalNorth : ∃ cell ∈ latticeBlockWindow
      (PeriodicOrthogonalDrawing.latticeNeighbor location .north),
      cell ∈ globalFootprint := by
    obtain ⟨cell, cellInNorthWindow, cellInFootprint⟩ := meetsLocalNorth
    refine ⟨Cell.add (latticeBlockOrigin location) cell, ?_, ?_⟩
    · rw [← translate_north_neighbor_window location]
      exact (add_mem_translateFootprint_iff (latticeBlockOrigin location) cell
        (translateFootprint (0, -6) (rectangleCells 6 6))).mpr
          cellInNorthWindow
    · exact (add_mem_translateFootprint_iff (latticeBlockOrigin location)
        cell footprint).mpr cellInFootprint
  have globalNorth := coherent location
    (PeriodicOrthogonalDrawing.latticeNeighbor location .north)
    globalFootprint globalMember meetsGlobalNorth
  obtain ⟨northFootprint, northMember, northEquality⟩ :=
    Finset.mem_image.mp globalNorth
  have expectedEquality :
      translateFootprint
          (latticeBlockOrigin
            (PeriodicOrthogonalDrawing.latticeNeighbor location .north))
          (translateFootprint (0, 6) footprint) = globalFootprint := by
    rw [translateFootprint_translate]
    have offsetEquality :
        Cell.add
          (latticeBlockOrigin
            (PeriodicOrthogonalDrawing.latticeNeighbor location .north))
          (0, 6) = latticeBlockOrigin location := by
      apply Prod.ext <;>
        simp [latticeBlockOrigin,
          PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add] ;
        ring
    rw [offsetEquality]
  have northFootprintEquality :
      northFootprint = translateFootprint (0, 6) footprint := by
    apply translateFootprint_injective
      (latticeBlockOrigin
        (PeriodicOrthogonalDrawing.latticeNeighbor location .north))
    exact northEquality.trans expectedEquality.symm
  exact northFootprintEquality ▸ northMember

/-- Locally exact, geometrically coherent states have equal east/west ports. -/
theorem horizontallyCompatible_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment)
    (location : Cell) :
    HorizontallyCompatible
      (portConfiguration tromino
        (orthogonalCellGadget tromino (drawing.getAt location))
        (assignment location))
      (portConfiguration tromino
        (orthogonalCellGadget tromino
          (drawing.getAt
            (PeriodicOrthogonalDrawing.latticeNeighbor location .east)))
        (assignment
          (PeriodicOrthogonalDrawing.latticeNeighbor location .east))) := by
  unfold HorizontallyCompatible
  rw [portConfiguration_eq_footprintPortConfiguration,
    portConfiguration_eq_footprintPortConfiguration]
  change rightPortState 6
      (footprintBoundary (rectangleCells 6 6)
        (windowFootprints tromino (assignment location))) =
    leftPortState
      (footprintBoundary (rectangleCells 6 6)
        (windowFootprints tromino
          (assignment
            (PeriodicOrthogonalDrawing.latticeNeighbor location .east))))
  ext normalized
  simp only [rightPortState, leftPortState, footprintBoundary,
    Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨source, ⟨⟨sourceMember, sourceOutside⟩, sourceCrosses⟩,
      sourceEquality⟩
    have shiftedMember := east_footprint_mem_of_coherent tromino drawing
      assignment locallyTiled coherent location source sourceMember sourceCrosses
    have shiftedEquality :
        translateFootprint (-6, 0) source = normalized := by
      norm_num at sourceEquality ⊢
      exact sourceEquality
    rw [shiftedEquality] at shiftedMember
    have sourceGeometry := localFootprint_geometry tromino drawing assignment
      locallyTiled location source sourceMember
    obtain ⟨inside, insideInWindow, insideMember⟩ := sourceGeometry.2.1
    have insideBounds := (mem_rectangleCells_iff 6 6 inside).mp insideInWindow
    have shiftedInside : Cell.add (-6, 0) inside ∈ normalized := by
      rw [← sourceEquality]
      exact (add_mem_translateFootprint_iff (-6, 0) inside source).mpr
        insideMember
    have normalizedCrosses : crossesLeft normalized := by
      exact ⟨Cell.add (-6, 0) inside, shiftedInside, by
        simp only [Cell.add]
        omega⟩
    have normalizedOutside : ¬ normalized ⊆ rectangleCells 6 6 := by
      intro subset
      have insideShiftedWindow := subset shiftedInside
      have shiftedBounds :=
        (mem_rectangleCells_iff 6 6 (Cell.add (-6, 0) inside)).mp
          insideShiftedWindow
      simp only [Cell.add] at shiftedBounds
      omega
    exact ⟨⟨shiftedMember, normalizedOutside⟩, normalizedCrosses⟩
  · rintro ⟨⟨normalizedMember, normalizedOutside⟩, normalizedCrosses⟩
    let east := PeriodicOrthogonalDrawing.latticeNeighbor location .east
    have shiftedMember := west_footprint_mem_of_coherent tromino drawing
      assignment locallyTiled coherent east normalized normalizedMember
        normalizedCrosses
    have shiftedMemberAtLocation : translateFootprint (6, 0) normalized ∈
        windowFootprints tromino (assignment location) := by
      have neighborEquality :
          PeriodicOrthogonalDrawing.latticeNeighbor east .west = location := by
        simpa only [east, Side.opposite] using
          PeriodicOrthogonalDrawing.latticeNeighbor_opposite location .east
      rw [neighborEquality] at shiftedMember
      exact shiftedMember
    have normalizedGeometry := localFootprint_geometry tromino drawing assignment
      locallyTiled east normalized normalizedMember
    obtain ⟨inside, insideInWindow, insideMember⟩ := normalizedGeometry.2.1
    have insideBounds := (mem_rectangleCells_iff 6 6 inside).mp insideInWindow
    have shiftedInside : Cell.add (6, 0) inside ∈
        translateFootprint (6, 0) normalized :=
      (add_mem_translateFootprint_iff (6, 0) inside normalized).mpr insideMember
    have shiftedCrosses :
        crossesRight 6 (translateFootprint (6, 0) normalized) := by
      exact ⟨Cell.add (6, 0) inside, shiftedInside, by
        simp only [Cell.add]
        omega⟩
    have shiftedOutside :
        ¬ translateFootprint (6, 0) normalized ⊆ rectangleCells 6 6 := by
      intro subset
      have shiftedInWindow := subset shiftedInside
      have shiftedBounds :=
        (mem_rectangleCells_iff 6 6 (Cell.add (6, 0) inside)).mp
          shiftedInWindow
      simp only [Cell.add] at shiftedBounds
      omega
    refine ⟨translateFootprint (6, 0) normalized,
      ⟨⟨shiftedMemberAtLocation, shiftedOutside⟩, shiftedCrosses⟩, ?_⟩
    rw [translateFootprint_translate]
    simp [Cell.add]

/-- Locally exact, geometrically coherent states have equal south/north ports. -/
theorem verticallyCompatible_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment)
    (location : Cell) :
    VerticallyCompatible
      (portConfiguration tromino
        (orthogonalCellGadget tromino (drawing.getAt location))
        (assignment location))
      (portConfiguration tromino
        (orthogonalCellGadget tromino
          (drawing.getAt
            (PeriodicOrthogonalDrawing.latticeNeighbor location .south)))
        (assignment
          (PeriodicOrthogonalDrawing.latticeNeighbor location .south))) := by
  unfold VerticallyCompatible
  rw [portConfiguration_eq_footprintPortConfiguration,
    portConfiguration_eq_footprintPortConfiguration]
  change southPortState 6
      (footprintBoundary (rectangleCells 6 6)
        (windowFootprints tromino (assignment location))) =
    northPortState
      (footprintBoundary (rectangleCells 6 6)
        (windowFootprints tromino
          (assignment
            (PeriodicOrthogonalDrawing.latticeNeighbor location .south))))
  ext normalized
  simp only [southPortState, northPortState, footprintBoundary,
    Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨source, ⟨⟨sourceMember, sourceOutside⟩, sourceCrosses⟩,
      sourceEquality⟩
    have shiftedMember := south_footprint_mem_of_coherent tromino drawing
      assignment locallyTiled coherent location source sourceMember sourceCrosses
    have shiftedEquality :
        translateFootprint (0, -6) source = normalized := by
      norm_num at sourceEquality ⊢
      exact sourceEquality
    rw [shiftedEquality] at shiftedMember
    have sourceGeometry := localFootprint_geometry tromino drawing assignment
      locallyTiled location source sourceMember
    obtain ⟨inside, insideInWindow, insideMember⟩ := sourceGeometry.2.1
    have insideBounds := (mem_rectangleCells_iff 6 6 inside).mp insideInWindow
    have shiftedInside : Cell.add (0, -6) inside ∈ normalized := by
      rw [← shiftedEquality]
      exact (add_mem_translateFootprint_iff (0, -6) inside source).mpr
        insideMember
    have normalizedCrosses : crossesNorth normalized := by
      exact ⟨Cell.add (0, -6) inside, shiftedInside, by
        simp only [Cell.add]
        omega⟩
    have normalizedOutside : ¬ normalized ⊆ rectangleCells 6 6 := by
      intro subset
      have shiftedInWindow := subset shiftedInside
      have shiftedBounds :=
        (mem_rectangleCells_iff 6 6 (Cell.add (0, -6) inside)).mp
          shiftedInWindow
      simp only [Cell.add] at shiftedBounds
      omega
    exact ⟨⟨shiftedMember, normalizedOutside⟩, normalizedCrosses⟩
  · rintro ⟨⟨normalizedMember, normalizedOutside⟩, normalizedCrosses⟩
    let south := PeriodicOrthogonalDrawing.latticeNeighbor location .south
    have shiftedMember := north_footprint_mem_of_coherent tromino drawing
      assignment locallyTiled coherent south normalized normalizedMember
        normalizedCrosses
    have shiftedMemberAtLocation : translateFootprint (0, 6) normalized ∈
        windowFootprints tromino (assignment location) := by
      have neighborEquality :
          PeriodicOrthogonalDrawing.latticeNeighbor south .north = location := by
        simpa only [south, Side.opposite] using
          PeriodicOrthogonalDrawing.latticeNeighbor_opposite location .south
      rw [neighborEquality] at shiftedMember
      exact shiftedMember
    have normalizedGeometry := localFootprint_geometry tromino drawing assignment
      locallyTiled south normalized normalizedMember
    obtain ⟨inside, insideInWindow, insideMember⟩ := normalizedGeometry.2.1
    have insideBounds := (mem_rectangleCells_iff 6 6 inside).mp insideInWindow
    have shiftedInside : Cell.add (0, 6) inside ∈
        translateFootprint (0, 6) normalized :=
      (add_mem_translateFootprint_iff (0, 6) inside normalized).mpr insideMember
    have shiftedCrosses :
        crossesSouth 6 (translateFootprint (0, 6) normalized) := by
      exact ⟨Cell.add (0, 6) inside, shiftedInside, by
        simp only [Cell.add]
        omega⟩
    have shiftedOutside :
        ¬ translateFootprint (0, 6) normalized ⊆ rectangleCells 6 6 := by
      intro subset
      have shiftedInWindow := subset shiftedInside
      have shiftedBounds :=
        (mem_rectangleCells_iff 6 6 (Cell.add (0, 6) inside)).mp
          shiftedInWindow
      simp only [Cell.add] at shiftedBounds
      omega
    refine ⟨translateFootprint (0, 6) normalized,
      ⟨⟨shiftedMemberAtLocation, shiftedOutside⟩, shiftedCrosses⟩, ?_⟩
    rw [translateFootprint_translate]
    simp [Cell.add]

/-- Geometric coherence and exact local covers are equivalent to the port
matching condition in the direction needed to restrict global tilings. -/
theorem isPortCompatible_of_geometricallyCoherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment) :
    IsPortCompatible tromino drawing assignment :=
  ⟨horizontallyCompatible_of_coherent tromino drawing assignment
      locallyTiled coherent,
    verticallyCompatible_of_coherent tromino drawing assignment
      locallyTiled coherent⟩

/-- A common selected-placement characterization is a convenient sufficient
condition for port compatibility. -/
theorem isPortCompatible_of_mem_iff (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (placements : Set (Placement Unit))
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (membership : ∀ location footprint,
      footprint ∈ drawingBlockFootprints tromino drawing assignment location ↔
        ∃ placement ∈ placements,
          placement.cells (fun _ : Unit => tromino.cells) = footprint ∧
            ∃ cell ∈ latticeBlockWindow location, cell ∈ footprint) :
    IsPortCompatible tromino drawing assignment :=
  isPortCompatible_of_geometricallyCoherent tromino drawing assignment
    locallyTiled
    (isGeometricallyCoherent_of_mem_iff tromino drawing assignment placements
      membership)

/-! ## Adjacent footprint propagation from port equality -/

/-- Equality of east/west ports propagates every right-crossing geometric
footprint into the neighboring local cover. -/
theorem east_footprint_mem_of_compatible (tromino : Tromino)
    (leftType rightType : OrthogonalCellType)
    (leftPlacements rightPlacements : Finset (Placement Unit))
    (compatible : HorizontallyCompatible
      (portConfiguration tromino
        (orthogonalCellGadget tromino leftType) leftPlacements)
      (portConfiguration tromino
        (orthogonalCellGadget tromino rightType) rightPlacements))
    (footprint : Finset Cell)
    (footprintMember : footprint ∈ windowFootprints tromino leftPlacements)
    (crosses : crossesRight 6 footprint) :
    translateFootprint (-6, 0) footprint ∈
      windowFootprints tromino rightPlacements := by
  have outside :
      ¬ footprint ⊆ (orthogonalCellGadget tromino leftType).window := by
    intro subset
    obtain ⟨cell, cellMember, beyond⟩ := crosses
    have cellInWindow := subset cellMember
    have bounds : cell.1 < (6 : Int) := by
      exact ((mem_rectangleCells_iff 6 6 cell).mp cellInWindow).2.1
    omega
  have boundaryMember :
      footprint ∈ footprintBoundary
        (orthogonalCellGadget tromino leftType).window
        (windowFootprints tromino leftPlacements) :=
    Finset.mem_filter.mpr ⟨footprintMember, outside⟩
  have eastMember :
      translateFootprint (-6, 0) footprint ∈
        (footprintPortConfiguration
          (orthogonalCellGadget tromino leftType)
          (windowFootprints tromino leftPlacements)).east := by
    change translateFootprint (-6, 0) footprint ∈
      rightPortState 6
        (footprintBoundary
          (orthogonalCellGadget tromino leftType).window
          (windowFootprints tromino leftPlacements))
    exact Finset.mem_image.mpr
      ⟨footprint, Finset.mem_filter.mpr ⟨boundaryMember, crosses⟩, rfl⟩
  have footprintCompatibility :
      (footprintPortConfiguration
        (orthogonalCellGadget tromino leftType)
        (windowFootprints tromino leftPlacements)).east =
      (footprintPortConfiguration
        (orthogonalCellGadget tromino rightType)
        (windowFootprints tromino rightPlacements)).west := by
    rw [← portConfiguration_eq_footprintPortConfiguration,
      ← portConfiguration_eq_footprintPortConfiguration]
    exact compatible
  have westMember :
      translateFootprint (-6, 0) footprint ∈
        (footprintPortConfiguration
          (orthogonalCellGadget tromino rightType)
          (windowFootprints tromino rightPlacements)).west := by
    rw [← footprintCompatibility]
    exact eastMember
  change translateFootprint (-6, 0) footprint ∈
    leftPortState
      (footprintBoundary
        (orthogonalCellGadget tromino rightType).window
        (windowFootprints tromino rightPlacements)) at westMember
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp westMember).1).1

/-- Equality of south/north ports propagates every bottom-crossing geometric
footprint into the neighboring local cover. -/
theorem south_footprint_mem_of_compatible (tromino : Tromino)
    (topType bottomType : OrthogonalCellType)
    (topPlacements bottomPlacements : Finset (Placement Unit))
    (compatible : VerticallyCompatible
      (portConfiguration tromino
        (orthogonalCellGadget tromino topType) topPlacements)
      (portConfiguration tromino
        (orthogonalCellGadget tromino bottomType) bottomPlacements))
    (footprint : Finset Cell)
    (footprintMember : footprint ∈ windowFootprints tromino topPlacements)
    (crosses : crossesSouth 6 footprint) :
    translateFootprint (0, -6) footprint ∈
      windowFootprints tromino bottomPlacements := by
  have outside :
      ¬ footprint ⊆ (orthogonalCellGadget tromino topType).window := by
    intro subset
    obtain ⟨cell, cellMember, beyond⟩ := crosses
    have cellInWindow := subset cellMember
    have bounds : cell.2 < (6 : Int) := by
      exact ((mem_rectangleCells_iff 6 6 cell).mp cellInWindow).2.2.2
    omega
  have boundaryMember :
      footprint ∈ footprintBoundary
        (orthogonalCellGadget tromino topType).window
        (windowFootprints tromino topPlacements) :=
    Finset.mem_filter.mpr ⟨footprintMember, outside⟩
  have southMember :
      translateFootprint (0, -6) footprint ∈
        (footprintPortConfiguration
          (orthogonalCellGadget tromino topType)
          (windowFootprints tromino topPlacements)).south := by
    change translateFootprint (0, -6) footprint ∈
      southPortState 6
        (footprintBoundary
          (orthogonalCellGadget tromino topType).window
          (windowFootprints tromino topPlacements))
    exact Finset.mem_image.mpr
      ⟨footprint, Finset.mem_filter.mpr ⟨boundaryMember, crosses⟩, rfl⟩
  have footprintCompatibility :
      (footprintPortConfiguration
        (orthogonalCellGadget tromino topType)
        (windowFootprints tromino topPlacements)).south =
      (footprintPortConfiguration
        (orthogonalCellGadget tromino bottomType)
        (windowFootprints tromino bottomPlacements)).north := by
    rw [← portConfiguration_eq_footprintPortConfiguration,
      ← portConfiguration_eq_footprintPortConfiguration]
    exact compatible
  have northMember :
      translateFootprint (0, -6) footprint ∈
        (footprintPortConfiguration
          (orthogonalCellGadget tromino bottomType)
          (windowFootprints tromino bottomPlacements)).north := by
    rw [← footprintCompatibility]
    exact southMember
  change translateFootprint (0, -6) footprint ∈
    northPortState
      (footprintBoundary
        (orthogonalCellGadget tromino bottomType).window
        (windowFootprints tromino bottomPlacements)) at northMember
  exact (Finset.mem_filter.mp (Finset.mem_filter.mp northMember).1).1

/-- The reverse horizontal propagation furnished by the same east/west port
equality. -/
theorem west_footprint_mem_of_compatible (tromino : Tromino)
    (leftType rightType : OrthogonalCellType)
    (leftPlacements rightPlacements : Finset (Placement Unit))
    (compatible : HorizontallyCompatible
      (portConfiguration tromino
        (orthogonalCellGadget tromino leftType) leftPlacements)
      (portConfiguration tromino
        (orthogonalCellGadget tromino rightType) rightPlacements))
    (footprint : Finset Cell)
    (footprintMember : footprint ∈ windowFootprints tromino rightPlacements)
    (crosses : crossesLeft footprint) :
    translateFootprint (6, 0) footprint ∈
      windowFootprints tromino leftPlacements := by
  have outside :
      ¬ footprint ⊆ (orthogonalCellGadget tromino rightType).window := by
    intro subset
    obtain ⟨cell, cellMember, beyond⟩ := crosses
    have cellInWindow := subset cellMember
    have bounds : (0 : Int) ≤ cell.1 :=
      ((mem_rectangleCells_iff 6 6 cell).mp cellInWindow).1
    omega
  have boundaryMember :
      footprint ∈ footprintBoundary
        (orthogonalCellGadget tromino rightType).window
        (windowFootprints tromino rightPlacements) :=
    Finset.mem_filter.mpr ⟨footprintMember, outside⟩
  have westMember :
      footprint ∈
        (footprintPortConfiguration
          (orthogonalCellGadget tromino rightType)
          (windowFootprints tromino rightPlacements)).west := by
    change footprint ∈ leftPortState
      (footprintBoundary
        (orthogonalCellGadget tromino rightType).window
        (windowFootprints tromino rightPlacements))
    exact Finset.mem_filter.mpr ⟨boundaryMember, crosses⟩
  have footprintCompatibility :
      (footprintPortConfiguration
        (orthogonalCellGadget tromino leftType)
        (windowFootprints tromino leftPlacements)).east =
      (footprintPortConfiguration
        (orthogonalCellGadget tromino rightType)
        (windowFootprints tromino rightPlacements)).west := by
    rw [← portConfiguration_eq_footprintPortConfiguration,
      ← portConfiguration_eq_footprintPortConfiguration]
    exact compatible
  have eastMember :
      footprint ∈
        (footprintPortConfiguration
          (orthogonalCellGadget tromino leftType)
          (windowFootprints tromino leftPlacements)).east := by
    rw [footprintCompatibility]
    exact westMember
  change footprint ∈ rightPortState 6
    (footprintBoundary
      (orthogonalCellGadget tromino leftType).window
      (windowFootprints tromino leftPlacements)) at eastMember
  obtain ⟨leftFootprint, leftFiltered, shiftedEquality⟩ :=
    Finset.mem_image.mp eastMember
  have leftMember :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp leftFiltered).1).1
  have recoveredEquality :
      leftFootprint = translateFootprint (6, 0) footprint := by
    have translatedEquality :=
      congrArg (translateFootprint (6, 0)) shiftedEquality
    simpa [translateFootprint_translate, Cell.add] using translatedEquality
  rwa [← recoveredEquality]

/-- The reverse vertical propagation furnished by the same south/north port
equality. -/
theorem north_footprint_mem_of_compatible (tromino : Tromino)
    (topType bottomType : OrthogonalCellType)
    (topPlacements bottomPlacements : Finset (Placement Unit))
    (compatible : VerticallyCompatible
      (portConfiguration tromino
        (orthogonalCellGadget tromino topType) topPlacements)
      (portConfiguration tromino
        (orthogonalCellGadget tromino bottomType) bottomPlacements))
    (footprint : Finset Cell)
    (footprintMember : footprint ∈ windowFootprints tromino bottomPlacements)
    (crosses : crossesNorth footprint) :
    translateFootprint (0, 6) footprint ∈
      windowFootprints tromino topPlacements := by
  have outside :
      ¬ footprint ⊆ (orthogonalCellGadget tromino bottomType).window := by
    intro subset
    obtain ⟨cell, cellMember, beyond⟩ := crosses
    have cellInWindow := subset cellMember
    have bounds : (0 : Int) ≤ cell.2 :=
      ((mem_rectangleCells_iff 6 6 cell).mp cellInWindow).2.2.1
    omega
  have boundaryMember :
      footprint ∈ footprintBoundary
        (orthogonalCellGadget tromino bottomType).window
        (windowFootprints tromino bottomPlacements) :=
    Finset.mem_filter.mpr ⟨footprintMember, outside⟩
  have northMember :
      footprint ∈
        (footprintPortConfiguration
          (orthogonalCellGadget tromino bottomType)
          (windowFootprints tromino bottomPlacements)).north := by
    change footprint ∈ northPortState
      (footprintBoundary
        (orthogonalCellGadget tromino bottomType).window
        (windowFootprints tromino bottomPlacements))
    exact Finset.mem_filter.mpr ⟨boundaryMember, crosses⟩
  have footprintCompatibility :
      (footprintPortConfiguration
        (orthogonalCellGadget tromino topType)
        (windowFootprints tromino topPlacements)).south =
      (footprintPortConfiguration
        (orthogonalCellGadget tromino bottomType)
        (windowFootprints tromino bottomPlacements)).north := by
    rw [← portConfiguration_eq_footprintPortConfiguration,
      ← portConfiguration_eq_footprintPortConfiguration]
    exact compatible
  have southMember :
      footprint ∈
        (footprintPortConfiguration
          (orthogonalCellGadget tromino topType)
          (windowFootprints tromino topPlacements)).south := by
    rw [footprintCompatibility]
    exact northMember
  change footprint ∈ southPortState 6
    (footprintBoundary
      (orthogonalCellGadget tromino topType).window
      (windowFootprints tromino topPlacements)) at southMember
  obtain ⟨topFootprint, topFiltered, shiftedEquality⟩ :=
    Finset.mem_image.mp southMember
  have topMember :=
    (Finset.mem_filter.mp (Finset.mem_filter.mp topFiltered).1).1
  have recoveredEquality :
      topFootprint = translateFootprint (0, 6) footprint := by
    have translatedEquality :=
      congrArg (translateFootprint (0, 6)) shiftedEquality
    simpa [translateFootprint_translate, Cell.add] using translatedEquality
  rwa [← recoveredEquality]

/-- East/west port compatibility propagates a global-coordinate footprint
from one lattice block to its eastern neighbor whenever it meets that window. -/
theorem drawingBlockFootprint_mem_east (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (compatible : IsPortCompatible tromino drawing assignment)
    (location : Cell) (footprint : Finset Cell)
    (footprintMember :
      footprint ∈ drawingBlockFootprints tromino drawing assignment location)
    (meetsEast : ∃ cell ∈ latticeBlockWindow
        (PeriodicOrthogonalDrawing.latticeNeighbor location .east),
      cell ∈ footprint) :
    footprint ∈ drawingBlockFootprints tromino drawing assignment
      (PeriodicOrthogonalDrawing.latticeNeighbor location .east) := by
  obtain ⟨localFootprint, localMember, globalEquality⟩ :=
    Finset.mem_image.mp footprintMember
  obtain ⟨cell, cellInEastWindow, cellInFootprint⟩ := meetsEast
  have cellInTranslated :
      cell ∈ translateFootprint (latticeBlockOrigin location) localFootprint := by
    rw [globalEquality]
    exact cellInFootprint
  obtain ⟨localCell, localCellMember, localCellEquality⟩ :=
    Finset.mem_image.mp cellInTranslated
  obtain ⟨eastCell, eastCellMember, eastCellEquality⟩ :=
    Finset.mem_image.mp cellInEastWindow
  have eastCellNonnegative : (0 : Int) ≤ eastCell.1 :=
    ((mem_rectangleCells_iff 6 6 eastCell).mp eastCellMember).1
  have localHorizontal := congrArg Prod.fst localCellEquality
  have eastHorizontal := congrArg Prod.fst eastCellEquality
  have crosses : crossesRight 6 localFootprint := by
    refine ⟨localCell, localCellMember, ?_⟩
    simp only [latticeBlockOrigin,
      PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add] at localHorizontal eastHorizontal
    omega
  have shiftedMember := east_footprint_mem_of_compatible tromino
    (drawing.getAt location)
    (drawing.getAt
      (PeriodicOrthogonalDrawing.latticeNeighbor location .east))
    (assignment location)
    (assignment (PeriodicOrthogonalDrawing.latticeNeighbor location .east))
    (compatible.1 location) localFootprint localMember crosses
  refine Finset.mem_image.mpr
    ⟨translateFootprint (-6, 0) localFootprint, shiftedMember, ?_⟩
  rw [translateFootprint_translate]
  have offsetEquality :
      Cell.add
        (latticeBlockOrigin
          (PeriodicOrthogonalDrawing.latticeNeighbor location .east))
        (-6, 0) = latticeBlockOrigin location := by
    apply Prod.ext
    · simp [latticeBlockOrigin,
        PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add]
      ring
    · simp [latticeBlockOrigin,
        PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add]
  rw [offsetEquality, globalEquality]

/-- South/north port compatibility propagates a global-coordinate footprint
from one lattice block to its southern neighbor whenever it meets that window. -/
theorem drawingBlockFootprint_mem_south (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (compatible : IsPortCompatible tromino drawing assignment)
    (location : Cell) (footprint : Finset Cell)
    (footprintMember :
      footprint ∈ drawingBlockFootprints tromino drawing assignment location)
    (meetsSouth : ∃ cell ∈ latticeBlockWindow
        (PeriodicOrthogonalDrawing.latticeNeighbor location .south),
      cell ∈ footprint) :
    footprint ∈ drawingBlockFootprints tromino drawing assignment
      (PeriodicOrthogonalDrawing.latticeNeighbor location .south) := by
  obtain ⟨localFootprint, localMember, globalEquality⟩ :=
    Finset.mem_image.mp footprintMember
  obtain ⟨cell, cellInSouthWindow, cellInFootprint⟩ := meetsSouth
  have cellInTranslated :
      cell ∈ translateFootprint (latticeBlockOrigin location) localFootprint := by
    rw [globalEquality]
    exact cellInFootprint
  obtain ⟨localCell, localCellMember, localCellEquality⟩ :=
    Finset.mem_image.mp cellInTranslated
  obtain ⟨southCell, southCellMember, southCellEquality⟩ :=
    Finset.mem_image.mp cellInSouthWindow
  have southCellNonnegative : (0 : Int) ≤ southCell.2 :=
    ((mem_rectangleCells_iff 6 6 southCell).mp southCellMember).2.2.1
  have localVertical := congrArg Prod.snd localCellEquality
  have southVertical := congrArg Prod.snd southCellEquality
  have crosses : crossesSouth 6 localFootprint := by
    refine ⟨localCell, localCellMember, ?_⟩
    simp only [latticeBlockOrigin,
      PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add] at localVertical southVertical
    omega
  have shiftedMember := south_footprint_mem_of_compatible tromino
    (drawing.getAt location)
    (drawing.getAt
      (PeriodicOrthogonalDrawing.latticeNeighbor location .south))
    (assignment location)
    (assignment (PeriodicOrthogonalDrawing.latticeNeighbor location .south))
    (compatible.2 location) localFootprint localMember crosses
  refine Finset.mem_image.mpr
    ⟨translateFootprint (0, -6) localFootprint, shiftedMember, ?_⟩
  rw [translateFootprint_translate]
  have offsetEquality :
      Cell.add
        (latticeBlockOrigin
          (PeriodicOrthogonalDrawing.latticeNeighbor location .south))
        (0, -6) = latticeBlockOrigin location := by
    apply Prod.ext
    · simp [latticeBlockOrigin,
        PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add]
    · simp [latticeBlockOrigin,
        PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add]
      ring
  rw [offsetEquality, globalEquality]

/-- East/west port compatibility also propagates a footprint to its western
neighbor. -/
theorem drawingBlockFootprint_mem_west (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (compatible : IsPortCompatible tromino drawing assignment)
    (location : Cell) (footprint : Finset Cell)
    (footprintMember :
      footprint ∈ drawingBlockFootprints tromino drawing assignment location)
    (meetsWest : ∃ cell ∈ latticeBlockWindow
        (PeriodicOrthogonalDrawing.latticeNeighbor location .west),
      cell ∈ footprint) :
    footprint ∈ drawingBlockFootprints tromino drawing assignment
      (PeriodicOrthogonalDrawing.latticeNeighbor location .west) := by
  obtain ⟨localFootprint, localMember, globalEquality⟩ :=
    Finset.mem_image.mp footprintMember
  obtain ⟨cell, cellInWestWindow, cellInFootprint⟩ := meetsWest
  have cellInTranslated :
      cell ∈ translateFootprint (latticeBlockOrigin location) localFootprint := by
    rw [globalEquality]
    exact cellInFootprint
  obtain ⟨localCell, localCellMember, localCellEquality⟩ :=
    Finset.mem_image.mp cellInTranslated
  obtain ⟨westCell, westCellMember, westCellEquality⟩ :=
    Finset.mem_image.mp cellInWestWindow
  have westCellBelow : westCell.1 < (6 : Int) :=
    ((mem_rectangleCells_iff 6 6 westCell).mp westCellMember).2.1
  have localHorizontal := congrArg Prod.fst localCellEquality
  have westHorizontal := congrArg Prod.fst westCellEquality
  have crosses : crossesLeft localFootprint := by
    refine ⟨localCell, localCellMember, ?_⟩
    simp only [latticeBlockOrigin,
      PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add] at localHorizontal westHorizontal
    omega
  have adjacentCompatibility : HorizontallyCompatible
      (portConfiguration tromino
        (orthogonalCellGadget tromino
          (drawing.getAt
            (PeriodicOrthogonalDrawing.latticeNeighbor location .west)))
        (assignment
          (PeriodicOrthogonalDrawing.latticeNeighbor location .west)))
      (portConfiguration tromino
        (orthogonalCellGadget tromino (drawing.getAt location))
        (assignment location)) := by
    simpa [PeriodicOrthogonalDrawing.latticeNeighbor] using
      compatible.1
        (PeriodicOrthogonalDrawing.latticeNeighbor location .west)
  have shiftedMember := west_footprint_mem_of_compatible tromino
    (drawing.getAt
      (PeriodicOrthogonalDrawing.latticeNeighbor location .west))
    (drawing.getAt location)
    (assignment (PeriodicOrthogonalDrawing.latticeNeighbor location .west))
    (assignment location) adjacentCompatibility localFootprint localMember crosses
  refine Finset.mem_image.mpr
    ⟨translateFootprint (6, 0) localFootprint, shiftedMember, ?_⟩
  rw [translateFootprint_translate]
  have offsetEquality :
      Cell.add
        (latticeBlockOrigin
          (PeriodicOrthogonalDrawing.latticeNeighbor location .west))
        (6, 0) = latticeBlockOrigin location := by
    apply Prod.ext
    · simp [latticeBlockOrigin,
        PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add]
      ring
    · simp [latticeBlockOrigin,
        PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add]
  rw [offsetEquality, globalEquality]

/-- South/north port compatibility also propagates a footprint to its northern
neighbor. -/
theorem drawingBlockFootprint_mem_north (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (compatible : IsPortCompatible tromino drawing assignment)
    (location : Cell) (footprint : Finset Cell)
    (footprintMember :
      footprint ∈ drawingBlockFootprints tromino drawing assignment location)
    (meetsNorth : ∃ cell ∈ latticeBlockWindow
        (PeriodicOrthogonalDrawing.latticeNeighbor location .north),
      cell ∈ footprint) :
    footprint ∈ drawingBlockFootprints tromino drawing assignment
      (PeriodicOrthogonalDrawing.latticeNeighbor location .north) := by
  obtain ⟨localFootprint, localMember, globalEquality⟩ :=
    Finset.mem_image.mp footprintMember
  obtain ⟨cell, cellInNorthWindow, cellInFootprint⟩ := meetsNorth
  have cellInTranslated :
      cell ∈ translateFootprint (latticeBlockOrigin location) localFootprint := by
    rw [globalEquality]
    exact cellInFootprint
  obtain ⟨localCell, localCellMember, localCellEquality⟩ :=
    Finset.mem_image.mp cellInTranslated
  obtain ⟨northCell, northCellMember, northCellEquality⟩ :=
    Finset.mem_image.mp cellInNorthWindow
  have northCellBelow : northCell.2 < (6 : Int) :=
    ((mem_rectangleCells_iff 6 6 northCell).mp northCellMember).2.2.2
  have localVertical := congrArg Prod.snd localCellEquality
  have northVertical := congrArg Prod.snd northCellEquality
  have crosses : crossesNorth localFootprint := by
    refine ⟨localCell, localCellMember, ?_⟩
    simp only [latticeBlockOrigin,
      PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add] at localVertical northVertical
    omega
  have adjacentCompatibility : VerticallyCompatible
      (portConfiguration tromino
        (orthogonalCellGadget tromino
          (drawing.getAt
            (PeriodicOrthogonalDrawing.latticeNeighbor location .north)))
        (assignment
          (PeriodicOrthogonalDrawing.latticeNeighbor location .north)))
      (portConfiguration tromino
        (orthogonalCellGadget tromino (drawing.getAt location))
        (assignment location)) := by
    simpa [PeriodicOrthogonalDrawing.latticeNeighbor] using
      compatible.2
        (PeriodicOrthogonalDrawing.latticeNeighbor location .north)
  have shiftedMember := north_footprint_mem_of_compatible tromino
    (drawing.getAt
      (PeriodicOrthogonalDrawing.latticeNeighbor location .north))
    (drawing.getAt location)
    (assignment (PeriodicOrthogonalDrawing.latticeNeighbor location .north))
    (assignment location) adjacentCompatibility localFootprint localMember crosses
  refine Finset.mem_image.mpr
    ⟨translateFootprint (0, 6) localFootprint, shiftedMember, ?_⟩
  rw [translateFootprint_translate]
  have offsetEquality :
      Cell.add
        (latticeBlockOrigin
          (PeriodicOrthogonalDrawing.latticeNeighbor location .north))
        (0, 6) = latticeBlockOrigin location := by
    apply Prod.ext
    · simp [latticeBlockOrigin,
        PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add]
    · simp [latticeBlockOrigin,
        PeriodicOrthogonalDrawing.latticeNeighbor, Cell.add]
      ring
  rw [offsetEquality, globalEquality]

/-- The four directional propagation lemmas packaged for a block that is
equal to or edge-neighboring the current block. -/
theorem drawingBlockFootprint_mem_neighborOrEqual (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (compatible : IsPortCompatible tromino drawing assignment)
    (first second : Cell) (footprint : Finset Cell)
    (footprintMember :
      footprint ∈ drawingBlockFootprints tromino drawing assignment first)
    (near : Cell.NeighborOrEqual first second)
    (meetsSecond : ∃ cell ∈ latticeBlockWindow second, cell ∈ footprint) :
    footprint ∈ drawingBlockFootprints tromino drawing assignment second := by
  rcases near with (same | east | west | south | north)
  · subst second
    exact footprintMember
  · subst second
    simpa [PeriodicOrthogonalDrawing.latticeNeighbor] using
      drawingBlockFootprint_mem_east tromino drawing assignment compatible
        first footprint footprintMember meetsSecond
  · subst second
    simpa [PeriodicOrthogonalDrawing.latticeNeighbor] using
      drawingBlockFootprint_mem_west tromino drawing assignment compatible
        first footprint footprintMember meetsSecond
  · subst second
    simpa [PeriodicOrthogonalDrawing.latticeNeighbor] using
      drawingBlockFootprint_mem_south tromino drawing assignment compatible
        first footprint footprintMember meetsSecond
  · subst second
    simpa [PeriodicOrthogonalDrawing.latticeNeighbor] using
      drawingBlockFootprint_mem_north tromino drawing assignment compatible
        first footprint footprintMember meetsSecond

/-- Pairwise port compatibility implies the full geometric footprint
coherence required by the atlas gluing theorem. -/
theorem isGeometricallyCoherent_of_portCompatible (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (compatible : IsPortCompatible tromino drawing assignment) :
    IsGeometricallyCoherent tromino drawing assignment := by
  intro first second footprint footprintMember meetsSecond
  obtain ⟨shape, meetsFirst⟩ :=
    drawingBlockFootprint_shape_and_meets tromino drawing assignment
      locallyTiled first footprint footprintMember
  obtain ⟨firstCell, firstCellInWindow, firstCellMember⟩ := meetsFirst
  obtain ⟨secondCell, secondCellInWindow, secondCellMember⟩ := meetsSecond
  obtain ⟨middle, middleMember, firstNearMiddle, middleNearSecond⟩ :=
    Tromino.IsFootprint.exists_middle shape firstCellMember secondCellMember
  obtain ⟨middleBlock, middleCellInWindow⟩ :=
    latticeBlockWindows_cover middle
  have firstBlockNearMiddle : Cell.NeighborOrEqual first middleBlock :=
    latticeBlocks_neighborOrEqual firstCellInWindow middleCellInWindow
      firstNearMiddle
  have middleMemberSelected :
      footprint ∈ drawingBlockFootprints tromino drawing assignment
        middleBlock :=
    drawingBlockFootprint_mem_neighborOrEqual tromino drawing assignment
      compatible first middleBlock footprint footprintMember
      firstBlockNearMiddle ⟨middle, middleCellInWindow, middleMember⟩
  have middleBlockNearSecond : Cell.NeighborOrEqual middleBlock second :=
    latticeBlocks_neighborOrEqual middleCellInWindow secondCellInWindow
      middleNearSecond
  exact drawingBlockFootprint_mem_neighborOrEqual tromino drawing assignment
    compatible middleBlock second footprint middleMemberSelected
    middleBlockNearSecond ⟨secondCell, secondCellInWindow, secondCellMember⟩

/-! ## Geometric realization on the lattice-block atlas -/

/-- The paper mask translated into the `6 × 6` block at one cell of the
infinite lifted drawing. -/
def drawingBlockRegion (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) (location : Cell) : Finset Cell :=
  latticeBlockRegion location
    (orthogonalCellPixels tromino (drawing.getAt location)).toFinset

/-- The infinite union of all translated Figure 11/12 pixel masks. -/
def liftedGadgetCarrier (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : Set Cell :=
  { cell | ∃ location, cell ∈ drawingBlockRegion tromino drawing location }

/-- Every translated paper mask stays inside its own lattice-block window. -/
theorem drawingBlockRegion_subset_window (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) (location : Cell) :
    drawingBlockRegion tromino drawing location ⊆ latticeBlockWindow location := by
  apply latticeBlockRegion_subset
  simpa only [Gadget.IsWellFormed, orthogonalCellGadget, paperGadget,
    Gadget.window] using
      orthogonalCellGadget_wellFormed tromino (drawing.getAt location)

/-- Inside one lattice-block window, the infinite lifted carrier is exactly
that block's translated paper mask. -/
theorem mem_liftedGadgetCarrier_iff_of_mem_window (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) (location cell : Cell)
    (cellInWindow : cell ∈ latticeBlockWindow location) :
    cell ∈ liftedGadgetCarrier tromino drawing ↔
      cell ∈ drawingBlockRegion tromino drawing location := by
  constructor
  · rintro ⟨other, cellInOtherRegion⟩
    have cellInOtherWindow := drawingBlockRegion_subset_window tromino drawing
      other cellInOtherRegion
    have locationEquality := latticeBlockWindow_unique cellInOtherWindow
      cellInWindow
    subst other
    exact cellInOtherRegion
  · intro cellInRegion
    exact ⟨location, cellInRegion⟩

/-- The block-atlas carrier is exactly the infinite carrier specified by the
finite periodic-region compilation. -/
theorem liftedGadgetCarrier_eq_expandedCarrier (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) :
    liftedGadgetCarrier tromino drawing = drawing.expandedCarrier tromino := by
  ext cell
  constructor
  · rintro ⟨location, cellMember⟩
    obtain ⟨pixel, pixelMember, pixelEquality⟩ :=
      Finset.mem_image.mp cellMember
    let position := drawing.positionAt location
    refine ⟨position, pixel, ?_,
      location.1 / (drawing.horizontalPeriod : Int),
      location.2 / (drawing.verticalPeriod : Int), ?_⟩
    · simpa only [drawingBlockRegion, latticeBlockRegion, List.mem_toFinset,
        PeriodicOrthogonalDrawing.getAt, position] using pixelMember
    · have horizontalDecomposition := Int.emod_add_mul_ediv location.1
        (drawing.horizontalPeriod : Int)
      have verticalDecomposition := Int.emod_add_mul_ediv location.2
        (drawing.verticalPeriod : Int)
      have horizontalResidue :=
        PeriodicOrthogonalDrawing.residue_val_int location.1
          drawing.horizontalPeriodPred
      have verticalResidue :=
        PeriodicOrthogonalDrawing.residue_val_int location.2
          drawing.verticalPeriodPred
      have pixelHorizontal := congrArg Prod.fst pixelEquality
      have pixelVertical := congrArg Prod.snd pixelEquality
      apply Prod.ext
      · simp only [Cell.add, Cell.scale, latticeBlockOrigin,
          PeriodicOrthogonalDrawing.blockOrigin,
          PeriodicOrthogonalDrawing.positionAt,
          PeriodicOrthogonalDrawing.horizontalPeriod,
          PeriodicOrthogonalDrawing.verticalPeriod, position] at pixelHorizontal horizontalDecomposition horizontalResidue ⊢
        rw [horizontalResidue]
        simp only [Nat.cast_add, Nat.cast_one] at horizontalDecomposition ⊢
        ring_nf at horizontalDecomposition pixelHorizontal ⊢
        linarith
      · simp only [Cell.add, Cell.scale, latticeBlockOrigin,
          PeriodicOrthogonalDrawing.blockOrigin,
          PeriodicOrthogonalDrawing.positionAt,
          PeriodicOrthogonalDrawing.horizontalPeriod,
          PeriodicOrthogonalDrawing.verticalPeriod, position] at pixelVertical verticalDecomposition verticalResidue ⊢
        rw [verticalResidue]
        simp only [Nat.cast_add, Nat.cast_one] at verticalDecomposition ⊢
        ring_nf at verticalDecomposition pixelVertical ⊢
        linarith
  · rintro ⟨position, pixel, pixelMember, horizontal, vertical, equality⟩
    let location : Cell :=
      ((position.1.val : Int) +
          horizontal * (drawing.horizontalPeriod : Int),
        (position.2.val : Int) +
          vertical * (drawing.verticalPeriod : Int))
    refine ⟨location, Finset.mem_image.mpr ⟨pixel, ?_, ?_⟩⟩
    · have positionEquality : drawing.positionAt location = position := by
        simpa only [location,
          PeriodicOrthogonalDrawing.horizontalPeriod,
          PeriodicOrthogonalDrawing.verticalPeriod, Nat.cast_add,
          Nat.cast_one] using
            drawing.positionAt_add_periods position horizontal vertical
      simpa only [drawingBlockRegion, latticeBlockRegion, List.mem_toFinset,
        PeriodicOrthogonalDrawing.getAt, positionEquality] using pixelMember
    · have horizontalEquality := congrArg Prod.fst equality
      have verticalEquality := congrArg Prod.snd equality
      apply Prod.ext
      · simp only [Cell.add, Cell.scale, latticeBlockOrigin,
          PeriodicOrthogonalDrawing.blockOrigin, location] at horizontalEquality ⊢
        nlinarith

      · simp only [Cell.add, Cell.scale, latticeBlockOrigin,
          PeriodicOrthogonalDrawing.blockOrigin, location] at verticalEquality ⊢
        nlinarith

/-- The same block-locality characterization for the carrier of the compiled
finite periodic presentation. -/
theorem mem_periodicRegion_carrier_iff_of_mem_blockWindow
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (location cell : Cell) (cellInWindow : cell ∈ latticeBlockWindow location) :
    cell ∈ (drawing.periodicRegion tromino).carrier ↔
      cell ∈ drawingBlockRegion tromino drawing location := by
  rw [PeriodicOrthogonalDrawing.periodicRegion_carrier_eq,
    ← liftedGadgetCarrier_eq_expandedCarrier]
  exact mem_liftedGadgetCarrier_iff_of_mem_window tromino drawing location cell
    cellInWindow

/-! ## Restricting a global tiling back to local gadget states -/

/-- Translation taking one global lattice block back to paper-local
coordinates. -/
def inverseLatticeBlockOrigin (location : Cell) : Cell :=
  (-6 * location.1, -6 * location.2)

@[simp]
theorem inverseLatticeBlockOrigin_add_latticeBlockOrigin (location : Cell) :
    Cell.add (inverseLatticeBlockOrigin location)
      (latticeBlockOrigin location) = (0, 0) := by
  rcases location with ⟨horizontal, vertical⟩
  apply Prod.ext <;>
    simp only [inverseLatticeBlockOrigin, latticeBlockOrigin, Cell.add] <;>
    ring

@[simp]
theorem latticeBlockOrigin_add_inverseLatticeBlockOrigin (location : Cell) :
    Cell.add (latticeBlockOrigin location)
      (inverseLatticeBlockOrigin location) = (0, 0) := by
  rcases location with ⟨horizontal, vertical⟩
  apply Prod.ext <;>
    simp only [inverseLatticeBlockOrigin, latticeBlockOrigin, Cell.add] <;>
    ring

@[simp]
theorem translate_inverse_latticeBlockWindow (location : Cell) :
    translateFootprint (inverseLatticeBlockOrigin location)
      (latticeBlockWindow location) = rectangleCells 6 6 := by
  rw [latticeBlockWindow, translateFootprint_translate,
    inverseLatticeBlockOrigin_add_latticeBlockOrigin,
    translateFootprint_zero]

@[simp]
theorem translate_inverse_latticeBlockRegion (location : Cell)
    (region : Finset Cell) :
    translateFootprint (inverseLatticeBlockOrigin location)
      (latticeBlockRegion location region) = region := by
  rw [latticeBlockRegion, translateFootprint_translate,
    inverseLatticeBlockOrigin_add_latticeBlockOrigin,
    translateFootprint_zero]

/-- Restrict a global placement set to one block, then translate those
placements back to local `6 × 6` coordinates. -/
noncomputable def localPlacementsFromGlobal (tromino : Tromino)
    (placements : Set (Placement Unit)) (location : Cell) :
    Finset (Placement Unit) :=
  translatePlacements (inverseLatticeBlockOrigin location)
    (globalWindowPlacements tromino (latticeBlockWindow location) placements)

/-- A global tiling of the compiled carrier restricts to a semantic local
tiling of every Figure 11/12 gadget. -/
theorem localPlacementsFromGlobal_isWindowTiling (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (placements : Set (Placement Unit))
    (tiling : LeanTrominoes.IsTiling (fun _ : Unit => tromino.cells)
      (drawing.periodicRegion tromino).carrier placements)
    (location : Cell) :
    IsWindowTiling tromino
      (orthogonalCellGadget tromino (drawing.getAt location)).window
      (orthogonalCellGadget tromino (drawing.getAt location)).region
      (localPlacementsFromGlobal tromino placements location) := by
  have restricted := LeanTrominoes.Gadget.IsTiling.isWindowTiling tiling
    (latticeBlockWindow location)
    (drawingBlockRegion tromino drawing location)
    (drawingBlockRegion_subset_window tromino drawing location)
    (fun cell cellInWindow =>
      mem_periodicRegion_carrier_iff_of_mem_blockWindow tromino drawing
        location cell cellInWindow)
  have translated := restricted.translate (inverseLatticeBlockOrigin location)
  change IsWindowTiling tromino (rectangleCells 6 6)
    (orthogonalCellPixels tromino (drawing.getAt location)).toFinset
    (translatePlacements (inverseLatticeBlockOrigin location)
      (globalWindowPlacements tromino (latticeBlockWindow location)
        placements))
  simpa only [drawingBlockRegion, translate_inverse_latticeBlockWindow,
    translate_inverse_latticeBlockRegion] using translated

/-- The local-state assignment obtained by restricting one global placement
set to every lattice block. -/
noncomputable def localAssignmentFromGlobal (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (placements : Set (Placement Unit)) :
    LocalTilingAssignment tromino drawing :=
  localPlacementsFromGlobal tromino placements

/-- Translating an extracted local footprint back to its block coordinates
recovers exactly the globally selected footprints meeting that block. -/
theorem drawingBlockFootprints_localAssignmentFromGlobal (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (placements : Set (Placement Unit)) (location : Cell) :
    drawingBlockFootprints tromino drawing
        (localAssignmentFromGlobal tromino drawing placements) location =
      windowFootprints tromino
        (globalWindowPlacements tromino (latticeBlockWindow location)
          placements) := by
  rw [drawingBlockFootprints, localAssignmentFromGlobal,
    localPlacementsFromGlobal, windowFootprints_translatePlacements,
    translateFootprints_translate,
    latticeBlockOrigin_add_inverseLatticeBlockOrigin,
    translateFootprints_zero]

/-- Membership in the extracted global-coordinate footprint set has the
expected representation-free characterization. -/
theorem mem_drawingBlockFootprints_localAssignmentFromGlobal_iff
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (placements : Set (Placement Unit)) (location : Cell)
    (footprint : Finset Cell) :
    footprint ∈ drawingBlockFootprints tromino drawing
        (localAssignmentFromGlobal tromino drawing placements) location ↔
      ∃ placement ∈ placements,
        placement.cells (fun _ : Unit => tromino.cells) = footprint ∧
          ∃ cell ∈ latticeBlockWindow location, cell ∈ footprint := by
  rw [drawingBlockFootprints_localAssignmentFromGlobal]
  exact mem_globalWindowFootprints_iff tromino (latticeBlockWindow location)
    placements footprint

/-- A global tiling makes all of its extracted local states members of the
verified exact-cover tables. -/
theorem localAssignmentFromGlobal_isLocallyTiled (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (placements : Set (Placement Unit))
    (tiling : LeanTrominoes.IsTiling (fun _ : Unit => tromino.cells)
      (drawing.periodicRegion tromino).carrier placements) :
    IsLocallyTiled tromino drawing
      (localAssignmentFromGlobal tromino drawing placements) := by
  intro location
  apply (mem_exactCellTilings_iff tromino (drawing.getAt location)
    (localAssignmentFromGlobal tromino drawing placements location)).mpr
  exact localPlacementsFromGlobal_isWindowTiling tromino drawing placements
    tiling location

/-- The states extracted from one global tiling have matching adjacent ports. -/
theorem localAssignmentFromGlobal_isPortCompatible (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (placements : Set (Placement Unit))
    (tiling : LeanTrominoes.IsTiling (fun _ : Unit => tromino.cells)
      (drawing.periodicRegion tromino).carrier placements) :
    IsPortCompatible tromino drawing
      (localAssignmentFromGlobal tromino drawing placements) := by
  exact isPortCompatible_of_mem_iff tromino drawing
    (localAssignmentFromGlobal tromino drawing placements) placements
    (localAssignmentFromGlobal_isLocallyTiled tromino drawing placements tiling)
    (mem_drawingBlockFootprints_localAssignmentFromGlobal_iff tromino drawing
      placements)

/-- A locally exact and geometrically coherent assignment instantiates the
abstract footprint atlas. -/
def footprintAtlasOfAssignment (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment) :
    FootprintAtlas tromino latticeBlockWindow
      (drawingBlockRegion tromino drawing) where
  footprints := drawingBlockFootprints tromino drawing assignment
  regionInside := by
    intro location
    apply latticeBlockRegion_subset
    simpa only [Gadget.IsWellFormed, orthogonalCellGadget, paperGadget,
      Gadget.window] using
      orthogonalCellGadget_wellFormed tromino (drawing.getAt location)
  windowsCover := latticeBlockWindows_cover
  localTiling := by
    intro location
    have localPlacementTiling :=
      (mem_exactCellTilings_iff tromino (drawing.getAt location)
        (assignment location)).mp (locallyTiled location)
    have localFootprintTiling :=
      localPlacementTiling.isWindowFootprintTiling
    simpa only [drawingBlockRegion, drawingBlockFootprints,
      latticeBlockWindow, latticeBlockRegion, orthogonalCellGadget,
      paperGadget, Gadget.window] using
      localFootprintTiling.translate (latticeBlockOrigin location)
  coherent := coherent

/-- Coherent local exact-cover states glue to a tiling of the complete lifted
gadget carrier. -/
theorem tileable_liftedGadgetCarrier_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment) :
    tromino.Tileable (liftedGadgetCarrier tromino drawing) := by
  let atlas := footprintAtlasOfAssignment tromino drawing assignment
    locallyTiled coherent
  simpa only [liftedGadgetCarrier, FootprintAtlas.carrier] using atlas.tileable

/-- The same gluing result stated for the actual finite `PeriodicRegion`
presentation emitted by gadget substitution. -/
theorem periodicRegion_tileable_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (coherent : IsGeometricallyCoherent tromino drawing assignment) :
    tromino.Tileable (drawing.periodicRegion tromino).carrier := by
  have tiling := tileable_liftedGadgetCarrier_of_coherent tromino drawing
    assignment locallyTiled coherent
  rw [liftedGadgetCarrier_eq_expandedCarrier,
    ← PeriodicOrthogonalDrawing.periodicRegion_carrier_eq] at tiling
  exact tiling

/-- Locally exact states with matching adjacent ports tile the compiled
periodic region. -/
theorem periodicRegion_tileable_of_portCompatible (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (locallyTiled : IsLocallyTiled tromino drawing assignment)
    (compatible : IsPortCompatible tromino drawing assignment) :
    tromino.Tileable (drawing.periodicRegion tromino).carrier :=
  periodicRegion_tileable_of_coherent tromino drawing assignment locallyTiled
    (isGeometricallyCoherent_of_portCompatible tromino drawing assignment
      locallyTiled compatible)

/-- Forward geometric correctness of the infinite compatible gadget system. -/
theorem periodicRegion_tileable_of_hasCompatibleGadgetTiling
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (compatibleTiling : HasCompatibleGadgetTiling tromino drawing) :
    tromino.Tileable (drawing.periodicRegion tromino).carrier := by
  obtain ⟨assignment, locallyTiled, compatible⟩ := compatibleTiling
  exact periodicRegion_tileable_of_portCompatible tromino drawing assignment
    locallyTiled compatible

/-- Conversely, a tiling of the compiled region restricts to a compatible
verified local state at every drawing cell. -/
theorem hasCompatibleGadgetTiling_of_periodicRegion_tileable
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (tileable : tromino.Tileable (drawing.periodicRegion tromino).carrier) :
    HasCompatibleGadgetTiling tromino drawing := by
  change ∃ placements : Set (Placement Unit),
    LeanTrominoes.IsTiling (fun _ : Unit => tromino.cells)
      (drawing.periodicRegion tromino).carrier placements at tileable
  obtain ⟨placements, tiling⟩ := tileable
  exact ⟨localAssignmentFromGlobal tromino drawing placements,
    localAssignmentFromGlobal_isLocallyTiled tromino drawing placements tiling,
    localAssignmentFromGlobal_isPortCompatible tromino drawing placements
      tiling⟩

/-- Exact geometric correctness of the Figure 11/12 block substitution. -/
theorem hasCompatibleGadgetTiling_iff_periodicRegion_tileable
    (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing) :
    HasCompatibleGadgetTiling tromino drawing ↔
      tromino.Tileable (drawing.periodicRegion tromino).carrier :=
  ⟨periodicRegion_tileable_of_hasCompatibleGadgetTiling tromino drawing,
    hasCompatibleGadgetTiling_of_periodicRegion_tileable tromino drawing⟩

/-- The finite-state correctness goal for Figures 11 and 12 on the
vertex-separated orthogonal drawings produced by normalization.
Well-formedness is repeated on the gadget side because malformed drawing
cells can have matching empty geometric ports despite disagreeing edge
colors. -/
def OrientationBehaviorCorrect (tromino : Tromino) : Prop :=
  ∀ drawing : PeriodicOrthogonalDrawing,
    drawing.VerticesSeparated →
      (drawing.HasOrientation ↔
        drawing.IsWellFormed ∧ HasCompatibleGadgetTiling tromino drawing)

/-- The geometric assembly correctness goal for the `6 × 6` substitution. -/
def SubstitutionAssemblyCorrect (tromino : Tromino) : Prop :=
  ∀ drawing : PeriodicOrthogonalDrawing,
    HasCompatibleGadgetTiling tromino drawing ↔
      tromino.Tileable (drawing.periodicRegion tromino).carrier

/-- The geometric assembly correctness goal is fully discharged for both
trominoes. -/
theorem substitutionAssemblyCorrect (tromino : Tromino) :
    SubstitutionAssemblyCorrect tromino :=
  hasCompatibleGadgetTiling_iff_periodicRegion_tileable tromino

end Gadget
end LeanTrominoes
