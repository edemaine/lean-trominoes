/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

namespace IsTiling

/-- Every cell in a tiled region has a covering placement. -/
theorem exists_cover {kind : Type*} {prototiles : kind → Polyomino}
    {region : Set Cell} {placements : Set (Placement kind)}
    (tiling : IsTiling prototiles region placements) {cell : Cell}
    (cell_mem : cell ∈ region) :
    ∃ placement ∈ placements, cell ∈ placement.cells prototiles := by
  obtain ⟨placement, ⟨placement_mem, covers⟩, _⟩ := tiling.uniqueCover cell cell_mem
  exact ⟨placement, placement_mem, covers⟩

/-- Distinct placements in a tiling occupy disjoint sets of cells. -/
theorem disjoint_cells {kind : Type*} {prototiles : kind → Polyomino}
    {region : Set Cell} {placements : Set (Placement kind)}
    (tiling : IsTiling prototiles region placements)
    {first second : Placement kind} (first_mem : first ∈ placements)
    (second_mem : second ∈ placements) (distinct : first ≠ second) :
    Disjoint (first.cells prototiles) (second.cells prototiles) := by
  rw [Finset.disjoint_left]
  intro cell first_covers second_covers
  have cell_mem := tiling.tilesInside first first_mem cell first_covers
  obtain ⟨chosen, _, unique⟩ := tiling.uniqueCover cell cell_mem
  have first_eq : first = chosen := unique first ⟨first_mem, first_covers⟩
  have second_eq : second = chosen := unique second ⟨second_mem, second_covers⟩
  exact distinct (first_eq.trans second_eq.symm)

end IsTiling

/-- A decidable exact-tiling predicate for a finite region and a finite set of
placements. This is the form used to verify the constant-size reduction
gadgets. -/
def IsFiniteTiling {kind : Type*} (prototiles : kind → Polyomino)
    (region : Finset Cell) (placements : Finset (Placement kind)) : Prop :=
  (∀ placement ∈ placements, placement.cells prototiles ⊆ region) ∧
    ∀ cell ∈ region,
      (placements.filter fun placement =>
        cell ∈ placement.cells prototiles).card = 1

instance {kind : Type*} [DecidableEq kind] (prototiles : kind → Polyomino)
    (region : Finset Cell) (placements : Finset (Placement kind)) :
    Decidable (IsFiniteTiling prototiles region placements) := by
  unfold IsFiniteTiling
  infer_instance

/-- The finite checker agrees with `IsTiling` after coercing its finite region
and placement collection to sets. -/
theorem isFiniteTiling_iff_isTiling {kind : Type*} [DecidableEq kind]
    (prototiles : kind → Polyomino) (region : Finset Cell)
    (placements : Finset (Placement kind)) :
    IsFiniteTiling prototiles region placements ↔
      IsTiling prototiles (region : Set Cell) (placements : Set (Placement kind)) := by
  constructor
  · rintro ⟨inside, covered⟩
    constructor
    · intro placement placement_mem cell cell_mem
      exact inside placement (by simpa using placement_mem) cell_mem
    · intro cell cell_mem
      obtain ⟨placement, filtered_eq⟩ :=
        Finset.card_eq_one.mp (covered cell (by simpa using cell_mem))
      have placement_filtered :
          placement ∈ placements.filter fun candidate =>
            cell ∈ candidate.cells prototiles := by
        rw [filtered_eq]
        simp
      have placement_data := Finset.mem_filter.mp placement_filtered
      refine ⟨placement, ⟨by simpa using placement_data.1, placement_data.2⟩, ?_⟩
      intro other other_covers
      have other_filtered :
          other ∈ placements.filter fun candidate =>
            cell ∈ candidate.cells prototiles :=
        Finset.mem_filter.mpr ⟨by simpa using other_covers.1, other_covers.2⟩
      rw [filtered_eq] at other_filtered
      simpa using other_filtered
  · rintro ⟨inside, covered⟩
    constructor
    · intro placement placement_mem cell cell_mem
      exact inside placement (by simpa using placement_mem) cell cell_mem
    · intro cell cell_mem
      obtain ⟨placement, ⟨placement_mem, covers⟩, unique⟩ :=
        covered cell (by simpa using cell_mem)
      apply Finset.card_eq_one.mpr
      refine ⟨placement, Finset.ext ?_⟩
      intro other
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨other_mem, other_covers⟩
        exact unique other ⟨by simpa using other_mem, other_covers⟩
      · rintro rfl
        exact ⟨by simpa using placement_mem, covers⟩

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
