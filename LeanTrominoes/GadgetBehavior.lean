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

/-! ## Geometric realization on the lattice-block atlas -/

/-- The paper mask translated into the `6 × 6` block at one cell of the
infinite lifted drawing. -/
def drawingBlockRegion (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) (location : Cell) : Finset Cell :=
  latticeBlockRegion location
    (orthogonalCellPixels tromino (drawing.getAt location)).toFinset

/-- Port agreement must ultimately imply this geometric condition: every
selected tromino footprint occurs in every lattice block that it meets. -/
def IsGeometricallyCoherent (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing)
    (assignment : LocalTilingAssignment tromino drawing) : Prop :=
  ∀ first second footprint,
    footprint ∈ drawingBlockFootprints tromino drawing assignment first →
      (∃ cell ∈ latticeBlockWindow second, cell ∈ footprint) →
        footprint ∈ drawingBlockFootprints tromino drawing assignment second

/-- The infinite union of all translated Figure 11/12 pixel masks. -/
def liftedGadgetCarrier (tromino : Tromino)
    (drawing : PeriodicOrthogonalDrawing) : Set Cell :=
  { cell | ∃ location, cell ∈ drawingBlockRegion tromino drawing location }

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

/-- The finite-state correctness goal for Figures 11 and 12. -/
def OrientationBehaviorCorrect (tromino : Tromino) : Prop :=
  ∀ drawing : PeriodicOrthogonalDrawing,
    drawing.HasOrientation ↔ HasCompatibleGadgetTiling tromino drawing

/-- The geometric assembly correctness goal for the `6 × 6` substitution. -/
def SubstitutionAssemblyCorrect (tromino : Tromino) : Prop :=
  ∀ drawing : PeriodicOrthogonalDrawing,
    HasCompatibleGadgetTiling tromino drawing ↔
      tromino.Tileable (drawing.periodicRegion tromino).carrier

end Gadget
end LeanTrominoes
