import LeanTrominoes.ComputableSearch
import LeanTrominoes.ExactCover
import Mathlib.Data.Finset.Interval
import Mathlib.Data.Finset.Max
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Int.Interval

/-!
# Finite tromino gadget windows

The hardness proof of Theorem 5.2 replaces every cell of an orthogonal graph
drawing by a `6 × 6` pattern. Tiles may cross from one pattern to the next,
so a gadget is not an isolated finite tiling problem. This file defines the
right local notion: exact coverage is required inside a finite window, while
placements crossing its boundary are retained as a finite boundary state.
-/

namespace LeanTrominoes

/-- The integer cells in `[0, width) × [0, height)`. -/
def rectangleCells (width height : Nat) : Finset Cell :=
  (Finset.Ico 0 (width : Int)).product (Finset.Ico 0 (height : Int))

theorem mem_rectangleCells_iff (width height : Nat) (cell : Cell) :
    cell ∈ rectangleCells width height ↔
      0 ≤ cell.1 ∧ cell.1 < (width : Int) ∧
        0 ≤ cell.2 ∧ cell.2 < (height : Int) := by
  simp [rectangleCells, and_assoc]

/-- A finite target pattern inside a rectangular window. -/
structure Gadget where
  width : Nat
  height : Nat
  region : Finset Cell
  deriving DecidableEq

namespace Gadget

/-- The complete rectangular window occupied by a gadget. -/
def window (gadget : Gadget) : Finset Cell :=
  rectangleCells gadget.width gadget.height

/-- Every target cell of a well-formed gadget lies in its window. -/
def IsWellFormed (gadget : Gadget) : Prop :=
  gadget.region ⊆ gadget.window

instance (gadget : Gadget) : Decidable gadget.IsWellFormed := by
  unfold IsWellFormed
  infer_instance

/-- The part of a placed tromino visible inside `window`. -/
def placementWindowCells (tromino : Tromino) (window : Finset Cell)
    (placement : Placement Unit) : Finset Cell :=
  placement.cells (fun _ : Unit => tromino.cells) ∩ window

/-- Every placement that meets at least one cell of `window`. -/
def windowCandidates (tromino : Tromino) (window : Finset Cell) :
    Finset (Placement Unit) :=
  window.biUnion fun cell =>
    TrominoAssignment.coveringPlacements tromino cell

theorem mem_windowCandidates_iff (tromino : Tromino)
    (window : Finset Cell) (placement : Placement Unit) :
    placement ∈ windowCandidates tromino window ↔
      ∃ cell ∈ window,
        cell ∈ placement.cells (fun _ : Unit => tromino.cells) := by
  simp only [windowCandidates, Finset.mem_biUnion]
  apply exists_congr
  intro cell
  apply and_congr_right
  intro _
  exact TrominoAssignment.mem_coveringPlacements_iff
    tromino cell placement

/-- Placements that meet `window` without covering a forbidden cell of that
window. Cells outside the window are deliberately ignored. -/
def admissibleCandidates (tromino : Tromino) (window region : Finset Cell) :
    Finset (Placement Unit) :=
  (windowCandidates tromino window).filter fun placement =>
    placementWindowCells tromino window placement ⊆ region

theorem mem_admissibleCandidates_iff (tromino : Tromino)
    (window region : Finset Cell) (placement : Placement Unit) :
    placement ∈ admissibleCandidates tromino window region ↔
      (∃ cell ∈ window,
        cell ∈ placement.cells (fun _ : Unit => tromino.cells)) ∧
      placementWindowCells tromino window placement ⊆ region := by
  simp [admissibleCandidates, mem_windowCandidates_iff]

/-- A finite placement collection tiles `region` exactly as seen through
`window`. A selected placement may extend outside the window, but its visible
cells must all belong to `region`. -/
def IsWindowTiling (tromino : Tromino) (window region : Finset Cell)
    (placements : Finset (Placement Unit)) : Prop :=
  placements ⊆ admissibleCandidates tromino window region ∧
    ∀ cell ∈ region,
      (placements.filter fun placement =>
        cell ∈ placement.cells (fun _ : Unit => tromino.cells)).card = 1

instance (tromino : Tromino) (window region : Finset Cell)
    (placements : Finset (Placement Unit)) :
    Decidable (IsWindowTiling tromino window region placements) := by
  unfold IsWindowTiling
  infer_instance

/-- The finite set of every local tiling of a window. This powerset
specification is primarily a proof interface; a later exact-cover search can
compute the same collection more efficiently. -/
def windowTilings (tromino : Tromino) (window region : Finset Cell) :
    Finset (Finset (Placement Unit)) :=
  (admissibleCandidates tromino window region).powerset.filter fun placements =>
    IsWindowTiling tromino window region placements

theorem mem_windowTilings_iff (tromino : Tromino)
    (window region : Finset Cell) (placements : Finset (Placement Unit)) :
    placements ∈ windowTilings tromino window region ↔
      IsWindowTiling tromino window region placements := by
  simp only [windowTilings, Finset.mem_filter, Finset.mem_powerset]
  constructor
  · exact fun member => member.2
  · intro tiling
    exact ⟨tiling.1, tiling⟩

/-- The selected placements that cross the geometric boundary of `window`. -/
def boundaryPlacements (tromino : Tromino) (window : Finset Cell)
    (placements : Finset (Placement Unit)) : Finset (Placement Unit) :=
  placements.filter fun placement =>
    ¬ placement.cells (fun _ : Unit => tromino.cells) ⊆ window

/-- Forget representation-level orientation and offset choices, retaining only
the occupied cells of each boundary-crossing tromino. -/
def boundarySignature (tromino : Tromino) (window : Finset Cell)
    (placements : Finset (Placement Unit)) : Finset (Finset Cell) :=
  (boundaryPlacements tromino window placements).image fun placement =>
    placement.cells (fun _ : Unit => tromino.cells)

/-- All realizable boundary states of a finite target pattern. -/
def boundarySignatures (tromino : Tromino) (window region : Finset Cell) :
    Finset (Finset (Finset Cell)) :=
  (windowTilings tromino window region).image fun placements =>
    boundarySignature tromino window placements

theorem mem_boundarySignatures_iff (tromino : Tromino)
    (window region : Finset Cell) (boundary : Finset (Finset Cell)) :
    boundary ∈ boundarySignatures tromino window region ↔
      ∃ placements, IsWindowTiling tromino window region placements ∧
        boundarySignature tromino window placements = boundary := by
  simp only [boundarySignatures, Finset.mem_image, mem_windowTilings_iff]

/-! ## Executable exact-cover enumeration -/

/-- A computable candidate list obtained by asking which placements cover a
listed target cell, then rejecting placements that hit a forbidden cell in the
window. -/
def admissibleCandidateList (tromino : Tromino) (window : Finset Cell)
    (regionCells : List Cell) : List (Placement Unit) :=
  ((regionCells.flatMap
    (TrominoAssignment.coveringPlacementList tromino)).dedup).filter
      fun placement =>
        placementWindowCells tromino window placement ⊆ regionCells.toFinset

theorem mem_admissibleCandidateList_iff (tromino : Tromino)
    (gadget : Gadget) (wellFormed : gadget.IsWellFormed)
    (regionCells : List Cell) (regionEquality : regionCells.toFinset = gadget.region)
    (placement : Placement Unit) :
    placement ∈ admissibleCandidateList tromino gadget.window regionCells ↔
      placement ∈ admissibleCandidates tromino gadget.window gadget.region := by
  simp only [admissibleCandidateList, List.mem_filter, List.mem_dedup,
    List.mem_flatMap]
  constructor
  · rintro ⟨⟨cell, cellInList, placementCovers⟩, visibleSubset⟩
    apply (mem_admissibleCandidates_iff tromino gadget.window
      gadget.region placement).mpr
    have cellInRegion : cell ∈ gadget.region := by
      rw [← regionEquality]
      simpa using cellInList
    refine ⟨⟨cell, wellFormed cellInRegion, ?_⟩, ?_⟩
    · exact (TrominoAssignment.mem_coveringPlacements_iff
        tromino cell placement).mp
          ((TrominoAssignment.mem_coveringPlacementList_iff
            tromino cell placement).mp placementCovers)
    · simpa only [decide_eq_true_eq, regionEquality] using visibleSubset
  · intro admissible
    obtain ⟨⟨cell, cellInWindow, placementCovers⟩, visibleSubset⟩ :=
      (mem_admissibleCandidates_iff tromino gadget.window
        gadget.region placement).mp admissible
    have cellVisible : cell ∈
        placementWindowCells tromino gadget.window placement := by
      exact Finset.mem_inter.mpr ⟨placementCovers, cellInWindow⟩
    have cellInRegion := visibleSubset cellVisible
    have cellInList : cell ∈ regionCells := by
      rw [← regionEquality] at cellInRegion
      simpa using cellInRegion
    refine ⟨⟨cell, cellInList, ?_⟩, ?_⟩
    · exact (TrominoAssignment.mem_coveringPlacementList_iff
        tromino cell placement).mpr
          ((TrominoAssignment.mem_coveringPlacements_iff
            tromino cell placement).mpr placementCovers)
    · simpa only [decide_eq_true_eq, regionEquality] using visibleSubset

theorem isWindowTiling_iff_exactCover (tromino : Tromino)
    (window region : Finset Cell) (regionSubset : region ⊆ window)
    (placements : Finset (Placement Unit)) :
    IsWindowTiling tromino window region placements ↔
      (∀ placement ∈ placements,
        placement ∈ admissibleCandidates tromino window region) ∧
      ExactCover.IsExactCover
        (placementWindowCells tromino window) region placements := by
  rw [ExactCover.isExactCover_iff_card_one]
  constructor
  · rintro ⟨admissible, covered⟩
    refine ⟨fun placement placementMember => admissible placementMember, ?_, ?_⟩
    · intro placement placementMember
      have candidate := (mem_admissibleCandidates_iff tromino window
        region placement).mp (admissible placementMember)
      obtain ⟨⟨cell, cellInWindow, placementCovers⟩, visibleSubset⟩ := candidate
      exact ⟨⟨cell, Finset.mem_inter.mpr ⟨placementCovers, cellInWindow⟩⟩,
        visibleSubset⟩
    · intro cell cellInRegion
      have cellInWindow := regionSubset cellInRegion
      simpa only [placementWindowCells, Finset.mem_inter, cellInWindow,
        and_true] using covered cell cellInRegion
  · rintro ⟨admissible, pieceData, covered⟩
    constructor
    · exact admissible
    · intro cell cellInRegion
      have cellInWindow := regionSubset cellInRegion
      simpa only [placementWindowCells, Finset.mem_inter, cellInWindow,
        and_true] using covered cell cellInRegion

/-- Efficiently enumerate the local tilings of a gadget from an explicit list
of its region cells. -/
def chooseCell (target : Finset Cell) (nonempty : target.Nonempty) : Cell :=
  let encoded := target.image Encodable.encode
  let code := encoded.min' (nonempty.image Encodable.encode)
  (Encodable.decode code).getD (0, 0)

theorem chooseCell_mem (target : Finset Cell) (nonempty : target.Nonempty) :
    chooseCell target nonempty ∈ target := by
  let encoded := target.image Encodable.encode
  let encodedNonempty : encoded.Nonempty := nonempty.image Encodable.encode
  have codeMember : encoded.min' encodedNonempty ∈ encoded :=
    Finset.min'_mem encoded encodedNonempty
  obtain ⟨cell, cellMember, codeEquality⟩ := Finset.mem_image.mp codeMember
  have decodeEquality :
      (Encodable.decode (encoded.min' encodedNonempty) : Option Cell) = some cell := by
    rw [← codeEquality]
    exact Encodable.encodek cell
  unfold chooseCell
  simpa only [encoded, encodedNonempty, decodeEquality, Option.getD_some]

def exactWindowTilings (tromino : Tromino) (gadget : Gadget)
    (regionCells : List Cell) : List (Finset (Placement Unit)) :=
  ExactCover.search chooseCell (placementWindowCells tromino gadget.window)
    (admissibleCandidateList tromino gadget.window regionCells) gadget.region

theorem mem_exactWindowTilings_iff (tromino : Tromino)
    (gadget : Gadget) (wellFormed : gadget.IsWellFormed)
    (regionCells : List Cell) (regionEquality : regionCells.toFinset = gadget.region)
    (placements : Finset (Placement Unit)) :
    placements ∈ exactWindowTilings tromino gadget regionCells ↔
      IsWindowTiling tromino gadget.window gadget.region placements := by
  rw [exactWindowTilings, ExactCover.mem_search_iff chooseCell chooseCell_mem,
    isWindowTiling_iff_exactCover tromino gadget.window gadget.region wellFormed]
  apply and_congr_left
  intro _
  apply forall_congr'
  intro placement
  apply forall_congr'
  intro _
  exact mem_admissibleCandidateList_iff tromino gadget wellFormed
    regionCells regionEquality placement

/-- Boundary signatures computed through verified backtracking. -/
def exactBoundarySignatures (tromino : Tromino) (gadget : Gadget)
    (regionCells : List Cell) : Finset (Finset (Finset Cell)) :=
  ((exactWindowTilings tromino gadget regionCells).map fun placements =>
    boundarySignature tromino gadget.window placements).toFinset

theorem exactBoundarySignatures_eq (tromino : Tromino)
    (gadget : Gadget) (wellFormed : gadget.IsWellFormed)
    (regionCells : List Cell) (regionEquality : regionCells.toFinset = gadget.region) :
    exactBoundarySignatures tromino gadget regionCells =
      boundarySignatures tromino gadget.window gadget.region := by
  ext boundary
  rw [mem_boundarySignatures_iff]
  simp only [exactBoundarySignatures, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨placements, placementsMember, equality⟩
    refine ⟨placements,
      (mem_exactWindowTilings_iff tromino gadget wellFormed
        regionCells regionEquality placements).mp placementsMember, equality⟩
  · rintro ⟨placements, tiling, equality⟩
    refine ⟨placements, ?_, equality⟩
    exact (mem_exactWindowTilings_iff tromino gadget wellFormed
      regionCells regionEquality placements).mpr tiling

/-! ## Figure 11 and 12 wire masks -/

/-- Region cells of the red horizontal L-tromino wire in Figure 11(b). -/
def figure11RedWireCells : List Cell :=
  [(0, 2), (1, 2), (2, 2), (3, 2), (4, 2), (5, 2),
    (1, 3), (3, 3), (5, 3)]

/-- The red horizontal L-tromino wire in Figure 11(b). Coordinates use the
top-left figure cell as `(0, 0)`; reflecting the vertical coordinate has no
effect on its local tiling behavior. -/
def figure11RedWire : Gadget where
  width := 6
  height := 6
  region := figure11RedWireCells.toFinset

theorem figure11RedWire_wellFormed : figure11RedWire.IsWellFormed := by
  native_decide

/-- Region cells of the red horizontal I-tromino wire in Figure 12(b). -/
def figure12RedWireCells : List Cell :=
  [(0, 1), (1, 1), (2, 1), (3, 1),
    (0, 2), (3, 2),
    (0, 3), (3, 3),
    (0, 4), (3, 4), (4, 4), (5, 4)]

/-- The red horizontal I-tromino wire in Figure 12(b). -/
def figure12RedWire : Gadget where
  width := 6
  height := 6
  region := figure12RedWireCells.toFinset

theorem figure12RedWire_wellFormed : figure12RedWire.IsWellFormed := by
  native_decide

/-- Before neighboring gadgets impose compatibility, the L-wire window has
thirteen geometric boundary signatures. -/
theorem figure11RedWire_boundarySignatureCount :
    (boundarySignatures .L figure11RedWire.window
      figure11RedWire.region).card = 13 := by
  rw [← exactBoundarySignatures_eq .L figure11RedWire
    figure11RedWire_wellFormed figure11RedWireCells rfl]
  native_decide

/-- Before neighboring gadgets impose compatibility, the I-wire window has
five geometric boundary signatures. -/
theorem figure12RedWire_boundarySignatureCount :
    (boundarySignatures .I figure12RedWire.window
      figure12RedWire.region).card = 5 := by
  rw [← exactBoundarySignatures_eq .I figure12RedWire
    figure12RedWire_wellFormed figure12RedWireCells rfl]
  native_decide

end Gadget
end LeanTrominoes
