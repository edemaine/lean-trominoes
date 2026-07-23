import LeanTrominoes.GadgetColoring

/-!
# Orientation data carried by local gadget tilings

The paper reads an edge orientation from the vector between a tromino center
and a marker pixel of the edge's color.  This file lifts those placement-level
vectors to exact local tilings, both at a designated target pixel and across
an entire gadget region.
-/

namespace LeanTrominoes
namespace Gadget

/-- Center-to-pixel vectors of the selected placements covering one cell. -/
def tilingVectorsAt (tromino : Tromino) (cell : Cell)
    (placements : Finset (Placement Unit)) : Finset Cell :=
  (placements.filter fun placement =>
    cell ∈ placement.cells (fun _ : Unit => tromino.cells)).image fun placement =>
      Cell.sub cell (placementCenter tromino placement)

/-- At every target cell, a local exact tiling determines exactly one
center-to-pixel vector. -/
theorem tilingVectorsAt_card (tromino : Tromino) (window region : Finset Cell)
    (placements : Finset (Placement Unit))
    (tiling : IsWindowTiling tromino window region placements)
    (cell : Cell) (cellMember : cell ∈ region) :
    (tilingVectorsAt tromino cell placements).card = 1 := by
  let coverers := placements.filter fun placement =>
    cell ∈ placement.cells (fun _ : Unit => tromino.cells)
  have coverersCard : coverers.card = 1 := tiling.2 cell cellMember
  have coverersSubsingleton : coverers.card ≤ 1 := by omega
  calc
    (tilingVectorsAt tromino cell placements).card =
        coverers.card := by
      apply Finset.card_image_of_injOn
      intro first firstMember second secondMember _
      exact (Finset.card_le_one.mp coverersSubsingleton)
        first firstMember second secondMember
    _ = 1 := coverersCard

/-- All vectors to pixels of one marker color that lie inside the gadget
region.  Marker pixels outside the current window are deliberately excluded. -/
def tilingRegionColorVectors (tromino : Tromino) (color : WireColor)
    (gadget : Gadget) (placements : Finset (Placement Unit)) : Finset Cell :=
  placements.biUnion fun placement =>
    ((placementColorCells tromino color placement ∩ gadget.region).image
      fun cell => Cell.sub cell (placementCenter tromino placement))

/-- The red, green, and blue orientation-vector data of one local tiling. -/
structure ColorVectorProfile where
  red : Finset Cell
  green : Finset Cell
  blue : Finset Cell
  deriving DecidableEq

/-- Collect every marker-color vector visible in a gadget region. -/
def colorVectorProfile (tromino : Tromino) (gadget : Gadget)
    (placements : Finset (Placement Unit)) : ColorVectorProfile where
  red := tilingRegionColorVectors tromino .red gadget placements
  green := tilingRegionColorVectors tromino .green gadget placements
  blue := tilingRegionColorVectors tromino .blue gadget placements

/-- Every color-vector profile produced by the verified exact-cover search. -/
def exactColorVectorProfiles (tromino : Tromino) (gadget : Gadget)
    (regionCells : List Cell) : Finset ColorVectorProfile :=
  ((exactWindowTilings tromino gadget regionCells).map
    (colorVectorProfile tromino gadget)).toFinset

theorem mem_exactColorVectorProfiles_iff (tromino : Tromino)
    (gadget : Gadget) (wellFormed : gadget.IsWellFormed)
    (regionCells : List Cell) (regionEquality : regionCells.toFinset = gadget.region)
    (profile : ColorVectorProfile) :
    profile ∈ exactColorVectorProfiles tromino gadget regionCells ↔
      ∃ placements, IsWindowTiling tromino gadget.window gadget.region placements ∧
        colorVectorProfile tromino gadget placements = profile := by
  simp only [exactColorVectorProfiles, List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨placements, member, equality⟩
    exact ⟨placements,
      (mem_exactWindowTilings_iff tromino gadget wellFormed
        regionCells regionEquality placements).mp member,
      equality⟩
  · rintro ⟨placements, tiling, equality⟩
    exact ⟨placements,
      (mem_exactWindowTilings_iff tromino gadget wellFormed
        regionCells regionEquality placements).mpr tiling,
      equality⟩

end Gadget
end LeanTrominoes
