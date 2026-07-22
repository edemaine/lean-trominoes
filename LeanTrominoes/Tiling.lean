import LeanTrominoes.Basic
import Mathlib.Data.Set.Basic

/-!
# Tilings of lattice subsets

The definitions mirror the two conditions in Section 5 of the paper: every
placed copy lies in the target region, and every target cell is covered by
exactly one placed copy.
-/

namespace LeanTrominoes

/-- A set of placements is an exact tiling of `region` by `prototiles`. -/
structure IsTiling {ι : Type*} (prototiles : ι → Polyomino)
    (region : Set Cell) (placements : Set (Placement ι)) : Prop where
  tilesInside :
    ∀ placement ∈ placements, ∀ cell ∈ placement.cells prototiles, cell ∈ region
  uniqueCover :
    ∀ cell ∈ region,
      ∃! placement : Placement ι,
        placement ∈ placements ∧ cell ∈ placement.cells prototiles

/-- A target region is tileable when some set of placements tiles it exactly. -/
def Tileable {ι : Type*} (prototiles : ι → Polyomino) (region : Set Cell) : Prop :=
  ∃ placements : Set (Placement ι), IsTiling prototiles region placements

/-- Specialization of `Tileable` to copies of one prototile. -/
def TileableBy (prototile : Polyomino) (region : Set Cell) : Prop :=
  Tileable (fun _ : Unit => prototile) region

/-- Tileability by copies of one of the two trominoes. -/
def Tromino.Tileable (tromino : Tromino) (region : Set Cell) : Prop :=
  TileableBy tromino.cells region

end LeanTrominoes
