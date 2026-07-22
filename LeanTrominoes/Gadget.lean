import LeanTrominoes.Assignment
import Mathlib.Data.Finset.Interval
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

/-- All realizable boundary states of a finite target pattern. -/
def boundarySignatures (tromino : Tromino) (window region : Finset Cell) :
    Finset (Finset (Placement Unit)) :=
  (windowTilings tromino window region).image fun placements =>
    boundaryPlacements tromino window placements

theorem mem_boundarySignatures_iff (tromino : Tromino)
    (window region : Finset Cell) (boundary : Finset (Placement Unit)) :
    boundary ∈ boundarySignatures tromino window region ↔
      ∃ placements, IsWindowTiling tromino window region placements ∧
        boundaryPlacements tromino window placements = boundary := by
  simp only [boundarySignatures, Finset.mem_image, mem_windowTilings_iff]

/-! ## Figure 11 and 12 wire masks -/

/-- The red horizontal L-tromino wire in Figure 11(b). Coordinates use the
top-left figure cell as `(0, 0)`; reflecting the vertical coordinate has no
effect on its local tiling behavior. -/
def figure11RedWire : Gadget where
  width := 6
  height := 6
  region :=
    {(0, 2), (1, 2), (2, 2), (3, 2), (4, 2), (5, 2),
      (1, 3), (3, 3), (5, 3)}

theorem figure11RedWire_wellFormed : figure11RedWire.IsWellFormed := by
  native_decide

/-- The red horizontal I-tromino wire in Figure 12(b). -/
def figure12RedWire : Gadget where
  width := 6
  height := 6
  region :=
    {(0, 1), (1, 1), (2, 1), (3, 1),
      (0, 2), (3, 2),
      (0, 3), (3, 3),
      (0, 4), (3, 4), (4, 4), (5, 4)}

theorem figure12RedWire_wellFormed : figure12RedWire.IsWellFormed := by
  native_decide

end Gadget
end LeanTrominoes
