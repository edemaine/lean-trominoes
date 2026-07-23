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

theorem mem_windowFootprints_iff (tromino : Tromino)
    (placements : Finset (Placement Unit)) (footprint : Finset Cell) :
    footprint ∈ windowFootprints tromino placements ↔
      ∃ placement ∈ placements,
        placement.cells (fun _ : Unit => tromino.cells) = footprint := by
  exact Finset.mem_image

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

/-- Restrict a possibly infinite global placement set to the finite candidates
that meet one window. -/
noncomputable def globalWindowPlacements (tromino : Tromino)
    (window : Finset Cell) (placements : Set (Placement Unit)) :
    Finset (Placement Unit) := by
  classical
  exact (windowCandidates tromino window).filter fun placement =>
    placement ∈ placements

/-- A placement occurs in a finite global restriction exactly when it is
globally selected and its footprint meets the window. -/
theorem mem_globalWindowPlacements_iff (tromino : Tromino)
    (window : Finset Cell) (placements : Set (Placement Unit))
    (placement : Placement Unit) :
    placement ∈ globalWindowPlacements tromino window placements ↔
      placement ∈ placements ∧
        ∃ cell ∈ window,
          cell ∈ placement.cells (fun _ : Unit => tromino.cells) := by
  classical
  rw [globalWindowPlacements, Finset.mem_filter,
    mem_windowCandidates_iff]
  tauto

/-- The footprints in a finite global restriction are exactly the globally
selected placement footprints that meet the window. -/
theorem mem_globalWindowFootprints_iff (tromino : Tromino)
    (window : Finset Cell) (placements : Set (Placement Unit))
    (footprint : Finset Cell) :
    footprint ∈
        windowFootprints tromino
          (globalWindowPlacements tromino window placements) ↔
      ∃ placement ∈ placements,
        placement.cells (fun _ : Unit => tromino.cells) = footprint ∧
          ∃ cell ∈ window, cell ∈ footprint := by
  constructor
  · intro footprintMember
    obtain ⟨placement, placementMember, placementEquality⟩ :=
      (mem_windowFootprints_iff tromino
        (globalWindowPlacements tromino window placements) footprint).mp
          footprintMember
    have globalData := (mem_globalWindowPlacements_iff tromino window
      placements placement).mp placementMember
    refine ⟨placement, globalData.1, placementEquality, ?_⟩
    obtain ⟨cell, cellInWindow, cellInPlacement⟩ := globalData.2
    exact ⟨cell, cellInWindow, placementEquality ▸ cellInPlacement⟩
  · rintro ⟨placement, placementSelected, placementEquality,
      cell, cellInWindow, cellInFootprint⟩
    apply (mem_windowFootprints_iff tromino
      (globalWindowPlacements tromino window placements) footprint).mpr
    refine ⟨placement, ?_, placementEquality⟩
    apply (mem_globalWindowPlacements_iff tromino window placements
      placement).mpr
    exact ⟨placementSelected, cell, cellInWindow,
      placementEquality.symm ▸ cellInFootprint⟩

/-- Restricting a global tiling to a finite window gives an exact open-window
tiling, provided the local target is exactly the global region inside that
window. -/
theorem IsTiling.isWindowTiling {tromino : Tromino} {region : Set Cell}
    {placements : Set (Placement Unit)}
    (tiling : LeanTrominoes.IsTiling
      (fun _ : Unit => tromino.cells) region placements)
    (window localRegion : Finset Cell)
    (localInside : localRegion ⊆ window)
    (regionInWindow : ∀ cell ∈ window,
      cell ∈ region ↔ cell ∈ localRegion) :
    IsWindowTiling tromino window localRegion
      (globalWindowPlacements tromino window placements) := by
  classical
  constructor
  · intro placement placementMember
    change placement ∈ (windowCandidates tromino window).filter
      (fun candidate => candidate ∈ placements) at placementMember
    have memberData := Finset.mem_filter.mp placementMember
    apply (mem_admissibleCandidates_iff tromino window localRegion placement).mpr
    refine ⟨(mem_windowCandidates_iff tromino window placement).mp memberData.1,
      ?_⟩
    intro cell cellMember
    obtain ⟨cellInPlacement, cellInWindow⟩ := Finset.mem_inter.mp cellMember
    have cellInRegion := tiling.tilesInside placement memberData.2 cell
      cellInPlacement
    exact (regionInWindow cell cellInWindow).mp cellInRegion
  · intro cell cellInLocalRegion
    have cellInWindow := localInside cellInLocalRegion
    have cellInRegion := (regionInWindow cell cellInWindow).mpr cellInLocalRegion
    obtain ⟨placement, ⟨placementMember, placementCovers⟩, unique⟩ :=
      tiling.uniqueCover cell cellInRegion
    apply Finset.card_eq_one.mpr
    refine ⟨placement, Finset.ext ?_⟩
    intro other
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨otherMember, otherCovers⟩
      change other ∈ (windowCandidates tromino window).filter
        (fun candidate => candidate ∈ placements) at otherMember
      have otherSelected := (Finset.mem_filter.mp otherMember).2
      exact unique other ⟨otherSelected, otherCovers⟩
    · intro otherEquality
      subst other
      refine ⟨?_, placementCovers⟩
      change placement ∈ (windowCandidates tromino window).filter
        (fun candidate => candidate ∈ placements)
      apply Finset.mem_filter.mpr
      refine ⟨?_, placementMember⟩
      exact (mem_windowCandidates_iff tromino window placement).mpr
        ⟨cell, cellInWindow, placementCovers⟩

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

/-! ## Elementary tromino-footprint geometry -/

/-- Two cells coincide or share one grid edge. -/
def Cell.NeighborOrEqual (first second : Cell) : Prop :=
  first = second ∨
    second = (first.1 + 1, first.2) ∨
    second = (first.1 - 1, first.2) ∨
    second = (first.1, first.2 + 1) ∨
    second = (first.1, first.2 - 1)

/-- Every tromino has a distinguished middle cell within one grid step of
each of its cells: the middle segment of I, or the elbow of L. -/
theorem Tromino.IsFootprint.exists_middle {tromino : Tromino}
    {footprint : Finset Cell} (shape : tromino.IsFootprint footprint)
    {first second : Cell} (firstMember : first ∈ footprint)
    (secondMember : second ∈ footprint) :
    ∃ middle ∈ footprint,
      Cell.NeighborOrEqual first middle ∧
        Cell.NeighborOrEqual middle second := by
  obtain ⟨placement, rfl⟩ := shape
  rcases placement with ⟨kind, symmetry, offset⟩
  rcases kind with ⟨⟩
  rw [Placement.mem_cells_iff] at firstMember secondMember
  obtain ⟨firstSource, firstSourceMember, firstEquality⟩ := firstMember
  obtain ⟨secondSource, secondSourceMember, secondEquality⟩ := secondMember
  cases tromino with
  | I =>
      let middle := Cell.add offset (symmetry.act (1, 0))
      have middleMember : middle ∈
          (Placement.mk () symmetry offset).cells
            (fun _ : Unit => Tromino.I.cells) := by
        rw [Placement.mem_cells_iff]
        exact ⟨(1, 0), by simp [Tromino.cells], rfl⟩
      refine ⟨middle, middleMember, ?_, ?_⟩
      · rw [← firstEquality]
        simp [Tromino.cells] at firstSourceMember
        rcases firstSourceMember with (rfl | rfl | rfl) <;>
          cases symmetry <;>
          simp [middle, Cell.NeighborOrEqual, SquareSymmetry.act, Cell.add] <;>
          omega
      · rw [← secondEquality]
        simp [Tromino.cells] at secondSourceMember
        rcases secondSourceMember with (rfl | rfl | rfl) <;>
          cases symmetry <;>
          simp [middle, Cell.NeighborOrEqual, SquareSymmetry.act, Cell.add] <;>
          omega
  | L =>
      let middle := Cell.add offset (symmetry.act (0, 0))
      have middleMember : middle ∈
          (Placement.mk () symmetry offset).cells
            (fun _ : Unit => Tromino.L.cells) := by
        rw [Placement.mem_cells_iff]
        exact ⟨(0, 0), by simp [Tromino.cells], rfl⟩
      refine ⟨middle, middleMember, ?_, ?_⟩
      · rw [← firstEquality]
        simp [Tromino.cells] at firstSourceMember
        rcases firstSourceMember with (rfl | rfl | rfl) <;>
          cases symmetry <;>
          simp [middle, Cell.NeighborOrEqual, SquareSymmetry.act, Cell.add]
      · rw [← secondEquality]
        simp [Tromino.cells] at secondSourceMember
        rcases secondSourceMember with (rfl | rfl | rfl) <;>
          cases symmetry <;>
          simp [middle, Cell.NeighborOrEqual, SquareSymmetry.act, Cell.add] <;>
          omega

/-- Any two cells of one I- or L-tromino footprint differ by at most two in
each coordinate. -/
theorem Tromino.IsFootprint.coordinate_bounds {tromino : Tromino}
    {footprint : Finset Cell} (shape : tromino.IsFootprint footprint)
    {first second : Cell} (firstMember : first ∈ footprint)
    (secondMember : second ∈ footprint) :
    -2 ≤ first.1 - second.1 ∧ first.1 - second.1 ≤ 2 ∧
      -2 ≤ first.2 - second.2 ∧ first.2 - second.2 ≤ 2 := by
  obtain ⟨placement, rfl⟩ := shape
  rcases placement with ⟨kind, symmetry, offset⟩
  rcases kind with ⟨⟩
  rw [Placement.mem_cells_iff] at firstMember secondMember
  obtain ⟨firstSource, firstSourceMember, firstEquality⟩ := firstMember
  obtain ⟨secondSource, secondSourceMember, secondEquality⟩ := secondMember
  have firstHorizontal := congrArg Prod.fst firstEquality
  have firstVertical := congrArg Prod.snd firstEquality
  have secondHorizontal := congrArg Prod.fst secondEquality
  have secondVertical := congrArg Prod.snd secondEquality
  cases tromino with
  | I =>
      simp [Tromino.cells] at firstSourceMember secondSourceMember
      rcases firstSourceMember with (rfl | rfl | rfl) <;>
        rcases secondSourceMember with (rfl | rfl | rfl) <;>
        cases symmetry <;>
        simp [SquareSymmetry.act, Cell.add] at firstHorizontal firstVertical secondHorizontal secondVertical <;>
        omega

  | L =>
      simp [Tromino.cells] at firstSourceMember secondSourceMember
      rcases firstSourceMember with (rfl | rfl | rfl) <;>
        rcases secondSourceMember with (rfl | rfl | rfl) <;>
        cases symmetry <;>
        simp [SquareSymmetry.act, Cell.add] at firstHorizontal firstVertical secondHorizontal secondVertical <;>
        omega

/-- A footprint crossing the east side of the paper window meets the east
neighbor unless it occupies one of the two intervening corners. -/
theorem Tromino.IsFootprint.meets_east_neighbor_of_corners_absent
    {tromino : Tromino} {footprint : Finset Cell}
    (shape : tromino.IsFootprint footprint)
    (meetsWindow : ∃ cell ∈ rectangleCells 6 6, cell ∈ footprint)
    (topCornerAbsent : (5, 0) ∉ footprint)
    (bottomCornerAbsent : (5, 5) ∉ footprint)
    (crosses : crossesRight 6 footprint) :
    ∃ cell ∈ translateFootprint (6, 0) (rectangleCells 6 6),
      cell ∈ footprint := by
  obtain ⟨inside, insideInWindow, insideMember⟩ := meetsWindow
  obtain ⟨beyond, beyondMember, beyondHorizontal⟩ := crosses
  have insideBounds := (mem_rectangleCells_iff 6 6 inside).mp insideInWindow
  have footprintBounds := Tromino.IsFootprint.coordinate_bounds shape
    beyondMember insideMember
  have eastWindowMember (cell : Cell) (horizontalLower : 6 ≤ cell.1)
      (horizontalUpper : cell.1 < 12) (verticalLower : 0 ≤ cell.2)
      (verticalUpper : cell.2 < 6) :
      cell ∈ translateFootprint (6, 0) (rectangleCells 6 6) := by
    apply Finset.mem_image.mpr
    refine ⟨(cell.1 - 6, cell.2), ?_, ?_⟩
    · rw [mem_rectangleCells_iff]
      simp only
      omega
    · apply Prod.ext <;> simp only [Cell.add] <;> omega
  by_cases beyondVertical : 0 ≤ beyond.2 ∧ beyond.2 < 6
  · exact ⟨beyond,
      eastWindowMember beyond beyondHorizontal (by omega)
        beyondVertical.1 beyondVertical.2,
      beyondMember⟩
  obtain ⟨middle, middleMember, insideNearMiddle, middleNearBeyond⟩ :=
    Tromino.IsFootprint.exists_middle shape insideMember beyondMember
  by_cases middleInEast : 6 ≤ middle.1 ∧ 0 ≤ middle.2 ∧ middle.2 < 6
  · exact ⟨middle,
      eastWindowMember middle middleInEast.1 (by
        have middleBounds := Tromino.IsFootprint.coordinate_bounds shape
          middleMember insideMember
        omega) middleInEast.2.1 middleInEast.2.2,
      middleMember⟩
  have beyondVerticalOutside : beyond.2 < 0 ∨ 6 ≤ beyond.2 := by omega
  have middleOutside : middle.1 < 6 ∨ middle.2 < 0 ∨ 6 ≤ middle.2 := by
    by_cases horizontal : middle.1 < 6
    · exact Or.inl horizontal
    by_cases vertical : middle.2 < 0
    · exact Or.inr (Or.inl vertical)
    exact Or.inr (Or.inr (by omega))
  rcases insideNearMiddle with (firstEquality | firstEquality |
      firstEquality | firstEquality | firstEquality) <;>
    rcases middleNearBeyond with (secondEquality | secondEquality |
      secondEquality | secondEquality | secondEquality) <;>
    rcases middleOutside with (middleLeft | middleAbove | middleBelow) <;>
    rcases beyondVerticalOutside with (beyondAbove | beyondBelow) <;>
    exfalso
  all_goals
    have firstHorizontal := congrArg Prod.fst firstEquality
    have firstVertical := congrArg Prod.snd firstEquality
    have secondHorizontal := congrArg Prod.fst secondEquality
    have secondVertical := congrArg Prod.snd secondEquality
  all_goals
    first
    | omega
    | apply topCornerAbsent
      have cornerEquality : inside = (5, 0) := by
        apply Prod.ext <;> omega
      exact cornerEquality ▸ insideMember
    | apply bottomCornerAbsent
      have cornerEquality : inside = (5, 5) := by
        apply Prod.ext <;> omega
      exact cornerEquality ▸ insideMember

/-- The corresponding west-side boundary fact. -/
theorem Tromino.IsFootprint.meets_west_neighbor_of_corners_absent
    {tromino : Tromino} {footprint : Finset Cell}
    (shape : tromino.IsFootprint footprint)
    (meetsWindow : ∃ cell ∈ rectangleCells 6 6, cell ∈ footprint)
    (topCornerAbsent : (0, 0) ∉ footprint)
    (bottomCornerAbsent : (0, 5) ∉ footprint)
    (crosses : crossesLeft footprint) :
    ∃ cell ∈ translateFootprint (-6, 0) (rectangleCells 6 6),
      cell ∈ footprint := by
  obtain ⟨inside, insideInWindow, insideMember⟩ := meetsWindow
  obtain ⟨beyond, beyondMember, beyondHorizontal⟩ := crosses
  have insideBounds := (mem_rectangleCells_iff 6 6 inside).mp insideInWindow
  have footprintBounds := Tromino.IsFootprint.coordinate_bounds shape
    beyondMember insideMember
  have westWindowMember (cell : Cell) (horizontalLower : -6 ≤ cell.1)
      (horizontalUpper : cell.1 < 0) (verticalLower : 0 ≤ cell.2)
      (verticalUpper : cell.2 < 6) :
      cell ∈ translateFootprint (-6, 0) (rectangleCells 6 6) := by
    apply Finset.mem_image.mpr
    refine ⟨(cell.1 + 6, cell.2), ?_, ?_⟩
    · rw [mem_rectangleCells_iff]
      simp only
      omega
    · apply Prod.ext <;> simp only [Cell.add] <;> omega
  by_cases beyondVertical : 0 ≤ beyond.2 ∧ beyond.2 < 6
  · exact ⟨beyond,
      westWindowMember beyond (by omega) beyondHorizontal
        beyondVertical.1 beyondVertical.2,
      beyondMember⟩
  obtain ⟨middle, middleMember, insideNearMiddle, middleNearBeyond⟩ :=
    Tromino.IsFootprint.exists_middle shape insideMember beyondMember
  by_cases middleInWest : middle.1 < 0 ∧ 0 ≤ middle.2 ∧ middle.2 < 6
  · exact ⟨middle,
      westWindowMember middle (by
        have middleBounds := Tromino.IsFootprint.coordinate_bounds shape
          middleMember insideMember
        omega) middleInWest.1 middleInWest.2.1 middleInWest.2.2,
      middleMember⟩
  have beyondVerticalOutside : beyond.2 < 0 ∨ 6 ≤ beyond.2 := by omega
  have middleOutside : 0 ≤ middle.1 ∨ middle.2 < 0 ∨ 6 ≤ middle.2 := by
    by_cases horizontal : 0 ≤ middle.1
    · exact Or.inl horizontal
    by_cases vertical : middle.2 < 0
    · exact Or.inr (Or.inl vertical)
    exact Or.inr (Or.inr (by omega))
  rcases insideNearMiddle with (firstEquality | firstEquality |
      firstEquality | firstEquality | firstEquality) <;>
    rcases middleNearBeyond with (secondEquality | secondEquality |
      secondEquality | secondEquality | secondEquality) <;>
    rcases middleOutside with (middleRight | middleAbove | middleBelow) <;>
    rcases beyondVerticalOutside with (beyondAbove | beyondBelow) <;>
    exfalso
  all_goals
    have firstHorizontal := congrArg Prod.fst firstEquality
    have firstVertical := congrArg Prod.snd firstEquality
    have secondHorizontal := congrArg Prod.fst secondEquality
    have secondVertical := congrArg Prod.snd secondEquality
  all_goals
    first
    | omega
    | apply topCornerAbsent
      have cornerEquality : inside = (0, 0) := by
        apply Prod.ext <;> omega
      exact cornerEquality ▸ insideMember
    | apply bottomCornerAbsent
      have cornerEquality : inside = (0, 5) := by
        apply Prod.ext <;> omega
      exact cornerEquality ▸ insideMember

/-- The corresponding south-side boundary fact. -/
theorem Tromino.IsFootprint.meets_south_neighbor_of_corners_absent
    {tromino : Tromino} {footprint : Finset Cell}
    (shape : tromino.IsFootprint footprint)
    (meetsWindow : ∃ cell ∈ rectangleCells 6 6, cell ∈ footprint)
    (leftCornerAbsent : (0, 5) ∉ footprint)
    (rightCornerAbsent : (5, 5) ∉ footprint)
    (crosses : crossesSouth 6 footprint) :
    ∃ cell ∈ translateFootprint (0, 6) (rectangleCells 6 6),
      cell ∈ footprint := by
  obtain ⟨inside, insideInWindow, insideMember⟩ := meetsWindow
  obtain ⟨beyond, beyondMember, beyondVertical⟩ := crosses
  have insideBounds := (mem_rectangleCells_iff 6 6 inside).mp insideInWindow
  have footprintBounds := Tromino.IsFootprint.coordinate_bounds shape
    beyondMember insideMember
  have southWindowMember (cell : Cell) (horizontalLower : 0 ≤ cell.1)
      (horizontalUpper : cell.1 < 6) (verticalLower : 6 ≤ cell.2)
      (verticalUpper : cell.2 < 12) :
      cell ∈ translateFootprint (0, 6) (rectangleCells 6 6) := by
    apply Finset.mem_image.mpr
    refine ⟨(cell.1, cell.2 - 6), ?_, ?_⟩
    · rw [mem_rectangleCells_iff]
      simp only
      omega
    · apply Prod.ext <;> simp only [Cell.add] <;> omega
  by_cases beyondHorizontal : 0 ≤ beyond.1 ∧ beyond.1 < 6
  · exact ⟨beyond,
      southWindowMember beyond beyondHorizontal.1 beyondHorizontal.2
        beyondVertical (by omega),
      beyondMember⟩
  obtain ⟨middle, middleMember, insideNearMiddle, middleNearBeyond⟩ :=
    Tromino.IsFootprint.exists_middle shape insideMember beyondMember
  by_cases middleInSouth :
      0 ≤ middle.1 ∧ middle.1 < 6 ∧ 6 ≤ middle.2
  · exact ⟨middle,
      southWindowMember middle middleInSouth.1 middleInSouth.2.1
        middleInSouth.2.2 (by
          have middleBounds := Tromino.IsFootprint.coordinate_bounds shape
            middleMember insideMember
          omega),
      middleMember⟩
  have beyondHorizontalOutside : beyond.1 < 0 ∨ 6 ≤ beyond.1 := by omega
  have middleOutside : middle.1 < 0 ∨ 6 ≤ middle.1 ∨ middle.2 < 6 := by
    by_cases left : middle.1 < 0
    · exact Or.inl left
    by_cases right : 6 ≤ middle.1
    · exact Or.inr (Or.inl right)
    exact Or.inr (Or.inr (by omega))
  rcases insideNearMiddle with (firstEquality | firstEquality |
      firstEquality | firstEquality | firstEquality) <;>
    rcases middleNearBeyond with (secondEquality | secondEquality |
      secondEquality | secondEquality | secondEquality) <;>
    rcases middleOutside with (middleLeft | middleRight | middleAbove) <;>
    rcases beyondHorizontalOutside with (beyondLeft | beyondRight) <;>
    exfalso
  all_goals
    have firstHorizontal := congrArg Prod.fst firstEquality
    have firstVertical := congrArg Prod.snd firstEquality
    have secondHorizontal := congrArg Prod.fst secondEquality
    have secondVertical := congrArg Prod.snd secondEquality
  all_goals
    first
    | omega
    | apply leftCornerAbsent
      have cornerEquality : inside = (0, 5) := by
        apply Prod.ext <;> omega
      exact cornerEquality ▸ insideMember
    | apply rightCornerAbsent
      have cornerEquality : inside = (5, 5) := by
        apply Prod.ext <;> omega
      exact cornerEquality ▸ insideMember

/-- The corresponding north-side boundary fact. -/
theorem Tromino.IsFootprint.meets_north_neighbor_of_corners_absent
    {tromino : Tromino} {footprint : Finset Cell}
    (shape : tromino.IsFootprint footprint)
    (meetsWindow : ∃ cell ∈ rectangleCells 6 6, cell ∈ footprint)
    (leftCornerAbsent : (0, 0) ∉ footprint)
    (rightCornerAbsent : (5, 0) ∉ footprint)
    (crosses : crossesNorth footprint) :
    ∃ cell ∈ translateFootprint (0, -6) (rectangleCells 6 6),
      cell ∈ footprint := by
  obtain ⟨inside, insideInWindow, insideMember⟩ := meetsWindow
  obtain ⟨beyond, beyondMember, beyondVertical⟩ := crosses
  have insideBounds := (mem_rectangleCells_iff 6 6 inside).mp insideInWindow
  have footprintBounds := Tromino.IsFootprint.coordinate_bounds shape
    beyondMember insideMember
  have northWindowMember (cell : Cell) (horizontalLower : 0 ≤ cell.1)
      (horizontalUpper : cell.1 < 6) (verticalLower : -6 ≤ cell.2)
      (verticalUpper : cell.2 < 0) :
      cell ∈ translateFootprint (0, -6) (rectangleCells 6 6) := by
    apply Finset.mem_image.mpr
    refine ⟨(cell.1, cell.2 + 6), ?_, ?_⟩
    · rw [mem_rectangleCells_iff]
      simp only
      omega
    · apply Prod.ext <;> simp only [Cell.add] <;> omega
  by_cases beyondHorizontal : 0 ≤ beyond.1 ∧ beyond.1 < 6
  · exact ⟨beyond,
      northWindowMember beyond beyondHorizontal.1 beyondHorizontal.2
        (by omega) beyondVertical,
      beyondMember⟩
  obtain ⟨middle, middleMember, insideNearMiddle, middleNearBeyond⟩ :=
    Tromino.IsFootprint.exists_middle shape insideMember beyondMember
  by_cases middleInNorth :
      0 ≤ middle.1 ∧ middle.1 < 6 ∧ middle.2 < 0
  · exact ⟨middle,
      northWindowMember middle middleInNorth.1 middleInNorth.2.1 (by
        have middleBounds := Tromino.IsFootprint.coordinate_bounds shape
          middleMember insideMember
        omega) middleInNorth.2.2,
      middleMember⟩
  have beyondHorizontalOutside : beyond.1 < 0 ∨ 6 ≤ beyond.1 := by omega
  have middleOutside : middle.1 < 0 ∨ 6 ≤ middle.1 ∨ 0 ≤ middle.2 := by
    by_cases left : middle.1 < 0
    · exact Or.inl left
    by_cases right : 6 ≤ middle.1
    · exact Or.inr (Or.inl right)
    exact Or.inr (Or.inr (by omega))
  rcases insideNearMiddle with (firstEquality | firstEquality |
      firstEquality | firstEquality | firstEquality) <;>
    rcases middleNearBeyond with (secondEquality | secondEquality |
      secondEquality | secondEquality | secondEquality) <;>
    rcases middleOutside with (middleLeft | middleRight | middleBelow) <;>
    rcases beyondHorizontalOutside with (beyondLeft | beyondRight) <;>
    exfalso
  all_goals
    have firstHorizontal := congrArg Prod.fst firstEquality
    have firstVertical := congrArg Prod.snd firstEquality
    have secondHorizontal := congrArg Prod.fst secondEquality
    have secondVertical := congrArg Prod.snd secondEquality
  all_goals
    first
    | omega
    | apply leftCornerAbsent
      have cornerEquality : inside = (0, 0) := by
        apply Prod.ext <;> omega
      exact cornerEquality ▸ insideMember
    | apply rightCornerAbsent
      have cornerEquality : inside = (5, 0) := by
        apply Prod.ext <;> omega
      exact cornerEquality ▸ insideMember

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

/-- Translate every placement in a finite local selection. -/
def translatePlacements (offset : Cell)
    (placements : Finset (Placement Unit)) : Finset (Placement Unit) :=
  placements.image (translatePlacement offset)

/-- Translating placements by a fixed offset is injective. -/
theorem translatePlacement_injective (offset : Cell) :
    Function.Injective (translatePlacement offset) := by
  intro first second equality
  refine Placement.ext ?_ ?_ ?_
  · exact congrArg (fun placement => placement.kind) equality
  · exact congrArg (fun placement => placement.symmetry) equality
  · have offsetEquality := congrArg Placement.offset equality
    apply Cell.add_left_injective offset
    simpa only [translatePlacement] using offsetEquality

/-- Exact open-window placement tilings are invariant under a common
translation of the window, region, and placement selection. -/
theorem IsWindowTiling.translate {tromino : Tromino}
    {window region : Finset Cell} {placements : Finset (Placement Unit)}
    (tiling : IsWindowTiling tromino window region placements)
    (offset : Cell) :
    IsWindowTiling tromino
      (translateFootprint offset window)
      (translateFootprint offset region)
      (translatePlacements offset placements) := by
  constructor
  · intro translatedPlacement translatedMember
    obtain ⟨placement, placementMember, rfl⟩ :=
      Finset.mem_image.mp translatedMember
    have admissible := (mem_admissibleCandidates_iff tromino window region
      placement).mp (tiling.1 placementMember)
    apply (mem_admissibleCandidates_iff tromino
      (translateFootprint offset window) (translateFootprint offset region)
      (translatePlacement offset placement)).mpr
    constructor
    · obtain ⟨cell, cellInWindow, cellInPlacement⟩ := admissible.1
      refine ⟨Cell.add offset cell,
        (add_mem_translateFootprint_iff offset cell window).mpr cellInWindow,
        ?_⟩
      rw [translatePlacement_cells]
      exact (add_mem_translateFootprint_iff offset cell
        (placement.cells fun _ : Unit => tromino.cells)).mpr cellInPlacement
    · intro cell cellMember
      obtain ⟨cellInPlacement, cellInWindow⟩ := Finset.mem_inter.mp cellMember
      rw [translatePlacement_cells] at cellInPlacement
      obtain ⟨placementCell, placementCellMember, placementCellEquality⟩ :=
        Finset.mem_image.mp cellInPlacement
      obtain ⟨windowCell, windowCellMember, windowCellEquality⟩ :=
        Finset.mem_image.mp cellInWindow
      have sourceEquality : placementCell = windowCell :=
        Cell.add_left_injective offset
          (placementCellEquality.trans windowCellEquality.symm)
      subst windowCell
      have sourceRegionMember := admissible.2
        (Finset.mem_inter.mpr ⟨placementCellMember, windowCellMember⟩)
      exact Finset.mem_image.mpr
        ⟨placementCell, sourceRegionMember, placementCellEquality⟩
  · intro cell cellMember
    obtain ⟨sourceCell, sourceCellMember, sourceCellEquality⟩ :=
      Finset.mem_image.mp cellMember
    obtain ⟨placement, placementCovers, unique⟩ :=
      tiling.uniqueCover sourceCellMember
    apply Finset.card_eq_one.mpr
    refine ⟨translatePlacement offset placement, Finset.ext ?_⟩
    intro other
    simp only [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨otherMember, otherCovers⟩
      obtain ⟨sourcePlacement, sourcePlacementMember,
        sourcePlacementEquality⟩ := Finset.mem_image.mp otherMember
      have sourceCovers :
          sourceCell ∈ sourcePlacement.cells (fun _ : Unit => tromino.cells) := by
        have translatedCovers :
            Cell.add offset sourceCell ∈
              (translatePlacement offset sourcePlacement).cells
                (fun _ : Unit => tromino.cells) := by
          rw [sourceCellEquality, sourcePlacementEquality]
          exact otherCovers
        rw [translatePlacement_cells] at translatedCovers
        exact (add_mem_translateFootprint_iff offset sourceCell
          (sourcePlacement.cells fun _ : Unit => tromino.cells)).mp
            translatedCovers
      have placementEquality := unique sourcePlacement
        ⟨sourcePlacementMember, sourceCovers⟩
      simpa only [placementEquality] using sourcePlacementEquality.symm
    · intro otherEquality
      subst other
      constructor
      · exact Finset.mem_image.mpr ⟨placement, placementCovers.1, rfl⟩
      · rw [← sourceCellEquality, translatePlacement_cells]
        exact (add_mem_translateFootprint_iff offset sourceCell
          (placement.cells fun _ : Unit => tromino.cells)).mpr
            placementCovers.2
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

/-- Forgetting placement representation commutes with translation. -/
theorem windowFootprints_translatePlacements (tromino : Tromino)
    (offset : Cell) (placements : Finset (Placement Unit)) :
    windowFootprints tromino (translatePlacements offset placements) =
      translateFootprints offset (windowFootprints tromino placements) := by
  rw [windowFootprints, translatePlacements, Finset.image_image,
    translateFootprints, windowFootprints, Finset.image_image]
  apply Finset.image_congr
  intro placement placementMember
  simp only [Function.comp_apply, translatePlacement_cells]

/-- Successive translations of a finite footprint family compose. -/
theorem translateFootprints_translate (first second : Cell)
    (footprints : Finset (Finset Cell)) :
    translateFootprints first (translateFootprints second footprints) =
      translateFootprints (Cell.add first second) footprints := by
  rw [translateFootprints, translateFootprints, translateFootprints,
    Finset.image_image]
  apply Finset.image_congr
  intro footprint footprintMember
  exact translateFootprint_translate first second footprint

@[simp]
theorem translateFootprints_zero (footprints : Finset (Finset Cell)) :
    translateFootprints (0, 0) footprints = footprints := by
  ext footprint
  simp only [translateFootprints, Finset.mem_image]
  constructor
  · rintro ⟨source, sourceMember, equality⟩
    have sourceEquality : source = footprint := by
      simpa only [translateFootprint_zero] using equality
    exact sourceEquality ▸ sourceMember
  · intro footprintMember
    exact ⟨footprint, footprintMember, translateFootprint_zero footprint⟩

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

/-- Distinct lattice-block windows are disjoint; equivalently, every integer
cell belongs to exactly one block. -/
theorem latticeBlockWindow_unique {cell first second : Cell}
    (firstMember : cell ∈ latticeBlockWindow first)
    (secondMember : cell ∈ latticeBlockWindow second) :
    first = second := by
  rcases first with ⟨firstHorizontal, firstVertical⟩
  rcases second with ⟨secondHorizontal, secondVertical⟩
  obtain ⟨firstLocal, firstLocalMember, firstEquality⟩ :=
    Finset.mem_image.mp firstMember
  obtain ⟨secondLocal, secondLocalMember, secondEquality⟩ :=
    Finset.mem_image.mp secondMember
  have firstBounds := (mem_rectangleCells_iff 6 6 firstLocal).mp firstLocalMember
  have secondBounds := (mem_rectangleCells_iff 6 6 secondLocal).mp secondLocalMember
  have firstX := congrArg Prod.fst firstEquality
  have firstY := congrArg Prod.snd firstEquality
  have secondX := congrArg Prod.fst secondEquality
  have secondY := congrArg Prod.snd secondEquality
  apply Prod.ext
  · simp only [latticeBlockOrigin, Cell.add] at firstX secondX
    omega
  · simp only [latticeBlockOrigin, Cell.add] at firstY secondY
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

/-- A tromino footprint can meet only its current `6 × 6` block and the eight
immediately neighboring blocks. -/
theorem Tromino.IsFootprint.latticeBlock_bounds {tromino : Tromino}
    {footprint : Finset Cell} (shape : tromino.IsFootprint footprint)
    {first second : Cell}
    (meetsFirst : ∃ cell ∈ latticeBlockWindow first, cell ∈ footprint)
    (meetsSecond : ∃ cell ∈ latticeBlockWindow second, cell ∈ footprint) :
    -1 ≤ second.1 - first.1 ∧ second.1 - first.1 ≤ 1 ∧
      -1 ≤ second.2 - first.2 ∧ second.2 - first.2 ≤ 1 := by
  obtain ⟨firstCell, firstCellInWindow, firstCellMember⟩ := meetsFirst
  obtain ⟨secondCell, secondCellInWindow, secondCellMember⟩ := meetsSecond
  obtain ⟨firstLocal, firstLocalMember, firstEquality⟩ :=
    Finset.mem_image.mp firstCellInWindow
  obtain ⟨secondLocal, secondLocalMember, secondEquality⟩ :=
    Finset.mem_image.mp secondCellInWindow
  have firstBounds := (mem_rectangleCells_iff 6 6 firstLocal).mp firstLocalMember
  have secondBounds := (mem_rectangleCells_iff 6 6 secondLocal).mp secondLocalMember
  have footprintBounds := Tromino.IsFootprint.coordinate_bounds shape
    firstCellMember secondCellMember
  have firstHorizontal := congrArg Prod.fst firstEquality
  have firstVertical := congrArg Prod.snd firstEquality
  have secondHorizontal := congrArg Prod.fst secondEquality
  have secondVertical := congrArg Prod.snd secondEquality
  simp only [latticeBlockOrigin, Cell.add] at firstHorizontal firstVertical secondHorizontal secondVertical
  omega

/-- Equal or edge-neighboring cells lie in equal or edge-neighboring lattice
blocks. -/
theorem latticeBlocks_neighborOrEqual {firstBlock secondBlock : Cell}
    {firstCell secondCell : Cell}
    (firstCellInWindow : firstCell ∈ latticeBlockWindow firstBlock)
    (secondCellInWindow : secondCell ∈ latticeBlockWindow secondBlock)
    (near : Cell.NeighborOrEqual firstCell secondCell) :
    Cell.NeighborOrEqual firstBlock secondBlock := by
  rcases firstBlock with ⟨firstHorizontalIndex, firstVerticalIndex⟩
  rcases secondBlock with ⟨secondHorizontalIndex, secondVerticalIndex⟩
  obtain ⟨firstLocal, firstLocalMember, firstEquality⟩ :=
    Finset.mem_image.mp firstCellInWindow
  obtain ⟨secondLocal, secondLocalMember, secondEquality⟩ :=
    Finset.mem_image.mp secondCellInWindow
  have firstBounds := (mem_rectangleCells_iff 6 6 firstLocal).mp firstLocalMember
  have secondBounds := (mem_rectangleCells_iff 6 6 secondLocal).mp secondLocalMember
  have firstHorizontal := congrArg Prod.fst firstEquality
  have firstVertical := congrArg Prod.snd firstEquality
  have secondHorizontal := congrArg Prod.fst secondEquality
  have secondVertical := congrArg Prod.snd secondEquality
  simp only [latticeBlockOrigin, Cell.add] at firstHorizontal firstVertical secondHorizontal secondVertical
  rcases near with (equality | east | west | south | north)
  · have nearHorizontal := congrArg Prod.fst equality
    have nearVertical := congrArg Prod.snd equality
    unfold Cell.NeighborOrEqual
    simp only [Prod.mk.injEq]
    omega
  · have nearHorizontal := congrArg Prod.fst east
    have nearVertical := congrArg Prod.snd east
    simp only at nearHorizontal nearVertical
    unfold Cell.NeighborOrEqual
    simp only [Prod.mk.injEq]
    omega
  · have nearHorizontal := congrArg Prod.fst west
    have nearVertical := congrArg Prod.snd west
    simp only at nearHorizontal nearVertical
    unfold Cell.NeighborOrEqual
    simp only [Prod.mk.injEq]
    omega
  · have nearHorizontal := congrArg Prod.fst south
    have nearVertical := congrArg Prod.snd south
    simp only at nearHorizontal nearVertical
    unfold Cell.NeighborOrEqual
    simp only [Prod.mk.injEq]
    omega
  · have nearHorizontal := congrArg Prod.fst north
    have nearVertical := congrArg Prod.snd north
    simp only at nearHorizontal nearVertical
    unfold Cell.NeighborOrEqual
    simp only [Prod.mk.injEq]
    omega

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
