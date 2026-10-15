/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import LeanTrominoes.Tiling.Tromino.Gadgets.GadgetOrientationBehavior

/-! # Port compatibility requires only the two incident gadget windows

The geometry proofs are localized versions of the global assembly lemmas.
A common placement set supplies geometric coherence even outside the region
where its windows are exactly tiled.
-/
namespace LeanTrominoes.Gadget.PartialPortCompatibility
theorem localFootprint_geometry (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (location : Cell)
    (locallyTiled : assignment location ∈ exactCellTilings tromino (drawing.getAt location))
    (footprint : Finset Cell)
    (footprintMember : footprint ∈
      windowFootprints tromino (assignment location)) :
    tromino.IsFootprint footprint ∧
      (∃ cell ∈ rectangleCells 6 6, cell ∈ footprint) ∧
      (0, 0) ∉ footprint ∧ (5, 0) ∉ footprint ∧
      (0, 5) ∉ footprint ∧ (5, 5) ∉ footprint := by
  have placementTiling :=
    (mem_exactCellTilings_iff tromino (drawing.getAt location)
      (assignment location)).mp locallyTiled
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

theorem east_footprint_mem_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (location : Cell)
    (locallyTiled : assignment location ∈ exactCellTilings tromino (drawing.getAt location))
    (coherent : IsGeometricallyCoherent tromino drawing assignment)
    (footprint : Finset Cell)
    (footprintMember : footprint ∈
      windowFootprints tromino (assignment location))
    (crosses : crossesRight 6 footprint) :
    translateFootprint (-6, 0) footprint ∈ windowFootprints tromino
      (assignment
        (PeriodicOrthogonalDrawing.latticeNeighbor location .east)) := by
  have geometry := localFootprint_geometry tromino drawing assignment
    location locallyTiled footprint footprintMember
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

theorem west_footprint_mem_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (location : Cell)
    (locallyTiled : assignment location ∈ exactCellTilings tromino (drawing.getAt location))
    (coherent : IsGeometricallyCoherent tromino drawing assignment)
    (footprint : Finset Cell)
    (footprintMember : footprint ∈
      windowFootprints tromino (assignment location))
    (crosses : crossesLeft footprint) :
    translateFootprint (6, 0) footprint ∈ windowFootprints tromino
      (assignment
        (PeriodicOrthogonalDrawing.latticeNeighbor location .west)) := by
  have geometry := localFootprint_geometry tromino drawing assignment
    location locallyTiled footprint footprintMember
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

theorem south_footprint_mem_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (location : Cell)
    (locallyTiled : assignment location ∈ exactCellTilings tromino (drawing.getAt location))
    (coherent : IsGeometricallyCoherent tromino drawing assignment)
    (footprint : Finset Cell)
    (footprintMember : footprint ∈
      windowFootprints tromino (assignment location))
    (crosses : crossesSouth 6 footprint) :
    translateFootprint (0, -6) footprint ∈ windowFootprints tromino
      (assignment
        (PeriodicOrthogonalDrawing.latticeNeighbor location .south)) := by
  have geometry := localFootprint_geometry tromino drawing assignment
    location locallyTiled footprint footprintMember
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

theorem north_footprint_mem_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (location : Cell)
    (locallyTiled : assignment location ∈ exactCellTilings tromino (drawing.getAt location))
    (coherent : IsGeometricallyCoherent tromino drawing assignment)
    (footprint : Finset Cell)
    (footprintMember : footprint ∈
      windowFootprints tromino (assignment location))
    (crosses : crossesNorth footprint) :
    translateFootprint (0, 6) footprint ∈ windowFootprints tromino
      (assignment
        (PeriodicOrthogonalDrawing.latticeNeighbor location .north)) := by
  have geometry := localFootprint_geometry tromino drawing assignment
    location locallyTiled footprint footprintMember
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

theorem horizontallyCompatible_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (location : Cell)
    (locallyTiled : assignment location ∈ exactCellTilings tromino (drawing.getAt location) ∧
      assignment (PeriodicOrthogonalDrawing.latticeNeighbor location .east) ∈
        exactCellTilings tromino (drawing.getAt (PeriodicOrthogonalDrawing.latticeNeighbor location .east)))
    (coherent : IsGeometricallyCoherent tromino drawing assignment) :
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
      assignment location locallyTiled.1 coherent source sourceMember sourceCrosses
    have shiftedEquality :
        translateFootprint (-6, 0) source = normalized := by
      norm_num at sourceEquality ⊢
      exact sourceEquality
    rw [shiftedEquality] at shiftedMember
    have sourceGeometry := localFootprint_geometry tromino drawing assignment
      location locallyTiled.1 source sourceMember
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
      assignment east locallyTiled.2 coherent normalized normalizedMember
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
      east locallyTiled.2 normalized normalizedMember
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

theorem verticallyCompatible_of_coherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing)
    (location : Cell)
    (locallyTiled : assignment location ∈ exactCellTilings tromino (drawing.getAt location) ∧
      assignment (PeriodicOrthogonalDrawing.latticeNeighbor location .south) ∈
        exactCellTilings tromino (drawing.getAt (PeriodicOrthogonalDrawing.latticeNeighbor location .south)))
    (coherent : IsGeometricallyCoherent tromino drawing assignment) :
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
      assignment location locallyTiled.1 coherent source sourceMember sourceCrosses
    have shiftedEquality :
        translateFootprint (0, -6) source = normalized := by
      norm_num at sourceEquality ⊢
      exact sourceEquality
    rw [shiftedEquality] at shiftedMember
    have sourceGeometry := localFootprint_geometry tromino drawing assignment
      location locallyTiled.1 source sourceMember
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
      assignment south locallyTiled.2 coherent normalized normalizedMember
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
      south locallyTiled.2 normalized normalizedMember
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

theorem ports_agree (tromino : Tromino) (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing) (location : Cell)
    (state : assignment location ∈ exactCellTilings tromino (drawing.getAt location))
    (neighbors : ∀ side,
      assignment (PeriodicOrthogonalDrawing.latticeNeighbor location side) ∈
        exactCellTilings tromino (drawing.getAt (PeriodicOrthogonalDrawing.latticeNeighbor location side)))
    (coherent : IsGeometricallyCoherent tromino drawing assignment) (side : Side) :
    (selectedPortConfiguration tromino drawing assignment location).get side =
      (selectedPortConfiguration tromino drawing assignment
        (PeriodicOrthogonalDrawing.latticeNeighbor location side)).get side.opposite := by
  cases side with
  | east =>
      exact horizontallyCompatible_of_coherent tromino drawing assignment location
        ⟨state,neighbors .east⟩ coherent
  | south =>
      exact verticallyCompatible_of_coherent tromino drawing assignment location
        ⟨state,neighbors .south⟩ coherent
  | west =>
      let west := PeriodicOrthogonalDrawing.latticeNeighbor location .west
      have back : PeriodicOrthogonalDrawing.latticeNeighbor west .east = location := by
        simpa only [west,Side.opposite] using
          PeriodicOrthogonalDrawing.latticeNeighbor_opposite location .west
      have h := horizontallyCompatible_of_coherent tromino drawing assignment west
        ⟨neighbors .west,by simpa only [back] using state⟩ coherent
      simpa only [back,selectedPortConfiguration,HorizontallyCompatible,
        PortConfiguration.get,Side.opposite] using h.symm
  | north =>
      let north := PeriodicOrthogonalDrawing.latticeNeighbor location .north
      have back : PeriodicOrthogonalDrawing.latticeNeighbor north .south = location := by
        simpa only [north,Side.opposite] using
          PeriodicOrthogonalDrawing.latticeNeighbor_opposite location .north
      have h := verticallyCompatible_of_coherent tromino drawing assignment north
        ⟨neighbors .north,by simpa only [back] using state⟩ coherent
      simpa only [back,selectedPortConfiguration,VerticallyCompatible,
        PortConfiguration.get,Side.opposite] using h.symm

end LeanTrominoes.Gadget.PartialPortCompatibility
