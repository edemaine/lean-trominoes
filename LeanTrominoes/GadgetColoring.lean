/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.GadgetLibrary

/-!
# Periodic pixel colorings used by the tromino gadgets

Figures 11(a) and 12(a) use periodic red/green/blue marker pixels.  The
orientation carried by an edge is the vector from a placed tromino's center
to the pixel matching that edge's color.  This file records the two colorings
and that representation-independent geometric data.
-/

namespace LeanTrominoes
namespace Gadget

/-- The marker color of a lattice pixel in Figure 11(a).  The fourth parity
class is uncolored. -/
def lPixelColor (cell : Cell) : Option WireColor :=
  if cell.2 % 2 = 0 then
    if cell.1 % 2 = 0 then some .red else some .green
  else if cell.1 % 2 = 0 then some .blue else none

/-- The marker color of a lattice pixel in Figure 12(a).  Only rows congruent
to one modulo three are colored, in the repeating order red, blue, green. -/
def iPixelColor (cell : Cell) : Option WireColor :=
  if cell.2 % 3 = 1 then
    if cell.1 % 3 = 0 then some .red
    else if cell.1 % 3 = 1 then some .blue
    else some .green
  else none

/-- The periodic marker coloring associated with a tromino. -/
def paperPixelColor : Tromino → Cell → Option WireColor
  | .L => lPixelColor
  | .I => iPixelColor

/-- Both paper colorings are invariant under the `6 × 6` gadget lattice. -/
theorem paperPixelColor_add_six (tromino : Tromino) (cell : Cell)
    (horizontal vertical : Int) :
    paperPixelColor tromino
      (Cell.add (6 * horizontal, 6 * vertical) cell) =
        paperPixelColor tromino cell := by
  rcases cell with ⟨x, y⟩
  cases tromino <;>
    simp [paperPixelColor, lPixelColor, iPixelColor, Cell.add,
      Int.add_emod, Int.mul_emod]

/-- The distinguished center cell in each canonical tromino representative:
the middle cell of an I and the elbow cell of an L. -/
def trominoCenterCell : Tromino → Cell
  | .I => (1, 0)
  | .L => (0, 0)

theorem trominoCenterCell_mem (tromino : Tromino) :
    trominoCenterCell tromino ∈ tromino.cells := by
  cases tromino <;> simp [trominoCenterCell, Tromino.cells]

/-- The geometric center cell of a placed tromino. -/
def placementCenter (tromino : Tromino)
    (placement : Placement Unit) : Cell :=
  Cell.add placement.offset (placement.symmetry.act (trominoCenterCell tromino))

theorem placementCenter_mem_cells (tromino : Tromino)
    (placement : Placement Unit) :
    placementCenter tromino placement ∈
      placement.cells (fun _ : Unit => tromino.cells) := by
  rw [Placement.mem_cells_iff]
  exact ⟨trominoCenterCell tromino, trominoCenterCell_mem tromino, rfl⟩

/-- Cells of a placed tromino carrying a specified paper marker color. -/
def placementColorCells (tromino : Tromino) (color : WireColor)
    (placement : Placement Unit) : Finset Cell :=
  (placement.cells (fun _ : Unit => tromino.cells)).filter fun cell =>
    paperPixelColor tromino cell = some color

/-- Vectors from a placed tromino's center to all of its pixels carrying a
specified marker color.  Gadget correctness will show the relevant set is a
singleton nonzero unit vector. -/
def placementColorVectors (tromino : Tromino) (color : WireColor)
    (placement : Placement Unit) : Finset Cell :=
  (placementColorCells tromino color placement).image fun cell =>
    Cell.sub cell (placementCenter tromino placement)

theorem mem_placementColorCells_iff (tromino : Tromino)
    (color : WireColor) (placement : Placement Unit) (cell : Cell) :
    cell ∈ placementColorCells tromino color placement ↔
      cell ∈ placement.cells (fun _ : Unit => tromino.cells) ∧
        paperPixelColor tromino cell = some color := by
  simp [placementColorCells]

theorem mem_placementColorVectors_iff (tromino : Tromino)
    (color : WireColor) (placement : Placement Unit) (vector : Cell) :
    vector ∈ placementColorVectors tromino color placement ↔
      ∃ cell ∈ placement.cells (fun _ : Unit => tromino.cells),
        paperPixelColor tromino cell = some color ∧
          Cell.sub cell (placementCenter tromino placement) = vector := by
  simp only [placementColorVectors, Finset.mem_image,
    mem_placementColorCells_iff]
  constructor
  · rintro ⟨cell, ⟨member, colorMatch⟩, equality⟩
    exact ⟨cell, member, colorMatch, equality⟩
  · rintro ⟨cell, member, colorMatch, equality⟩
    exact ⟨cell, ⟨member, colorMatch⟩, equality⟩

set_option maxHeartbeats 1000000 in
/-- A placed tromino contains at most one pixel of each marker color.  This is
the coloring invariant that makes the center-to-colored-pixel vector
unambiguous. -/
theorem placementColorCells_card_le_one (tromino : Tromino)
    (color : WireColor) (placement : Placement Unit) :
    (placementColorCells tromino color placement).card ≤ 1 := by
  rw [Finset.card_le_one_iff]
  intro first second firstMember secondMember
  rw [mem_placementColorCells_iff] at firstMember secondMember
  rw [Placement.mem_cells_iff] at firstMember secondMember
  obtain ⟨⟨firstSource, firstSourceMember, firstEquality⟩, firstColor⟩ :=
    firstMember
  obtain ⟨⟨secondSource, secondSourceMember, secondEquality⟩, secondColor⟩ :=
    secondMember
  subst first
  subst second
  rcases placement with ⟨⟨⟩, symmetry, ⟨x, y⟩⟩
  cases tromino <;> cases symmetry <;>
    simp [Tromino.cells] at firstSourceMember secondSourceMember <;>
    rcases firstSourceMember with (rfl | rfl | rfl) <;>
    rcases secondSourceMember with (rfl | rfl | rfl) <;>
    simp [SquareSymmetry.act, Cell.add, paperPixelColor, lPixelColor,
      iPixelColor] at firstColor secondColor ⊢ <;>
    cases color <;>
    split_ifs at firstColor secondColor <;> simp_all <;> omega

theorem placementColorVectors_card_le_one (tromino : Tromino)
    (color : WireColor) (placement : Placement Unit) :
    (placementColorVectors tromino color placement).card ≤ 1 := by
  exact (Finset.card_image_le.trans
    (placementColorCells_card_le_one tromino color placement))

end Gadget
end LeanTrominoes
