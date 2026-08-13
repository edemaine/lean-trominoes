/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
import LeanTrominoes.Tiling
import Mathlib.Data.Finset.Prod
import Mathlib.Tactic.Ring

/-!
# Local assignments of tromino placements

A tromino tiling can be represented by a finite-valued state at every lattice
cell: either no tile starts at that offset, or a tile starts there in one of
the eight square-grid orientations. This form is convenient for compactness
and finite-obstruction arguments.
-/

noncomputable section

namespace LeanTrominoes

/-- A finite-valued placement state at every possible offset. -/
abbrev TrominoAssignment := Cell → Option SquareSymmetry

namespace TrominoAssignment

/-- All placements of `tromino` that could cover `cell`. There are only
finitely many: choose an orientation and which prototile cell maps to `cell`. -/
def coveringPlacements (tromino : Tromino) (cell : Cell) :
    Finset (Placement Unit) :=
  (Finset.univ.product tromino.cells).image fun candidate =>
    { kind := ()
      symmetry := candidate.1
      offset := Cell.sub cell (candidate.1.act candidate.2) }

/-- The finite candidate enumeration contains exactly the placements that
cover the specified cell. -/
theorem mem_coveringPlacements_iff (tromino : Tromino) (cell : Cell)
    (placement : Placement Unit) :
    placement ∈ coveringPlacements tromino cell ↔
      cell ∈ placement.cells fun _ : Unit => tromino.cells := by
  constructor
  · rw [coveringPlacements, Finset.mem_image]
    rintro ⟨⟨symmetry, source⟩, candidate_mem, rfl⟩
    rw [Placement.mem_cells_iff]
    refine ⟨source, (Finset.mem_product.mp candidate_mem).2, ?_⟩
    simp only [Cell.add, Cell.sub]
    apply Prod.ext <;> simp
  · intro covers
    rw [coveringPlacements, Finset.mem_image]
    rw [Placement.mem_cells_iff] at covers
    obtain ⟨source, source_mem, equality⟩ := covers
    refine ⟨(placement.symmetry, source), by simp [source_mem], ?_⟩
    apply Placement.ext
    · exact Subsingleton.elim _ _
    · rfl
    · apply Prod.ext
      · have x_equality := congrArg Prod.fst equality
        simp only [Cell.add] at x_equality
        simp only [Cell.sub]
        rw [← x_equality]
        ring
      · have y_equality := congrArg Prod.snd equality
        simp only [Cell.add] at y_equality
        simp only [Cell.sub]
        rw [← y_equality]
        ring

/-- The set of placements selected by an assignment. -/
def placements (assignment : TrominoAssignment) : Set (Placement Unit) :=
  { placement | assignment placement.offset = some placement.symmetry }

/-- An assignment tiles a region when its selected placements do. -/
def IsTiling (tromino : Tromino) (region : Set Cell)
    (assignment : TrominoAssignment) : Prop :=
  LeanTrominoes.IsTiling (fun _ : Unit => tromino.cells) region assignment.placements

/-- The local constraint form of a tromino tiling. A selected tile stays
inside the region, and every region cell has exactly one active candidate
placement from its finite candidate list. -/
def IsLocallyValid (tromino : Tromino) (region : Set Cell)
    (assignment : TrominoAssignment) : Prop :=
  (∀ offset symmetry, assignment offset = some symmetry →
      ∀ cell ∈ (Placement.mk () symmetry offset).cells (fun _ : Unit => tromino.cells),
        cell ∈ region) ∧
    ∀ cell ∈ region,
      ((coveringPlacements tromino cell).filter fun placement =>
        assignment placement.offset = some placement.symmetry).card = 1

/-- Local assignment constraints are exactly the semantic tiling condition. -/
theorem isLocallyValid_iff_isTiling (tromino : Tromino) (region : Set Cell)
    (assignment : TrominoAssignment) :
    assignment.IsLocallyValid tromino region ↔ assignment.IsTiling tromino region := by
  constructor
  · rintro ⟨inside, covered⟩
    constructor
    · intro placement placement_mem cell cell_mem
      exact inside placement.offset placement.symmetry placement_mem cell cell_mem
    · intro cell cell_mem
      obtain ⟨placement, filtered_eq⟩ :=
        Finset.card_eq_one.mp (covered cell cell_mem)
      have placement_filtered :
          placement ∈ (coveringPlacements tromino cell).filter fun candidate =>
            assignment candidate.offset = some candidate.symmetry := by
        rw [filtered_eq]
        simp
      have placement_data := Finset.mem_filter.mp placement_filtered
      refine ⟨placement, ⟨placement_data.2,
        (mem_coveringPlacements_iff tromino cell placement).mp placement_data.1⟩, ?_⟩
      intro other other_data
      have other_filtered :
          other ∈ (coveringPlacements tromino cell).filter fun candidate =>
            assignment candidate.offset = some candidate.symmetry :=
        Finset.mem_filter.mpr ⟨
          (mem_coveringPlacements_iff tromino cell other).mpr other_data.2,
          other_data.1⟩
      rw [filtered_eq] at other_filtered
      simpa using other_filtered
  · intro tiling
    constructor
    · intro offset symmetry selected cell cell_mem
      exact tiling.tilesInside (Placement.mk () symmetry offset) selected cell cell_mem
    · intro cell cell_mem
      obtain ⟨placement, ⟨selected, covers⟩, unique⟩ :=
        tiling.uniqueCover cell cell_mem
      apply Finset.card_eq_one.mpr
      refine ⟨placement, Finset.ext ?_⟩
      intro other
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨candidate, active⟩
        exact unique other ⟨active,
          (mem_coveringPlacements_iff tromino cell other).mp candidate⟩
      · intro other_eq
        subst other
        exact ⟨(mem_coveringPlacements_iff tromino cell placement).mpr covers, selected⟩

/-- Two selected placements at the same offset are equal. The shared offset
cell would otherwise be covered twice. -/
theorem placement_eq_of_offset_eq (tromino : Tromino) {region : Set Cell}
    {selected : Set (Placement Unit)}
    (tiling : LeanTrominoes.IsTiling (fun _ : Unit => tromino.cells) region selected)
    {first second : Placement Unit} (first_mem : first ∈ selected)
    (second_mem : second ∈ selected) (offset_eq : first.offset = second.offset) :
    first = second := by
  have first_covers := tromino.offset_mem_placement_cells first
  have second_covers : first.offset ∈ second.cells fun _ : Unit => tromino.cells := by
    simpa only [offset_eq] using tromino.offset_mem_placement_cells second
  have offset_mem := tiling.tilesInside first first_mem first.offset first_covers
  obtain ⟨chosen, _, unique⟩ := tiling.uniqueCover first.offset offset_mem
  exact (unique first ⟨first_mem, first_covers⟩).trans
    (unique second ⟨second_mem, second_covers⟩).symm

/-- Every set-based tromino tiling has an equivalent finite-valued assignment
of placements. -/
theorem exists_assignment_iff_tileable (tromino : Tromino) (region : Set Cell) :
    (∃ assignment : TrominoAssignment, assignment.IsTiling tromino region) ↔
      tromino.Tileable region := by
  constructor
  · rintro ⟨assignment, tiling⟩
    exact ⟨assignment.placements, tiling⟩
  · rintro ⟨selected, tiling⟩
    classical
    let assignment : TrominoAssignment := fun offset =>
      if exists_placement : ∃ placement ∈ selected, placement.offset = offset then
        some exists_placement.choose.symmetry
      else
        none
    refine ⟨assignment, ?_⟩
    have placements_eq : assignment.placements = selected := by
      ext placement
      constructor
      · intro placement_mem
        change assignment placement.offset = some placement.symmetry at placement_mem
        have exists_placement :
            ∃ candidate ∈ selected, candidate.offset = placement.offset := by
          by_contra none_exists
          simp only [assignment, dif_neg none_exists] at placement_mem
          cases placement_mem
        simp only [assignment, dif_pos exists_placement] at placement_mem
        have symmetry_eq : exists_placement.choose.symmetry = placement.symmetry :=
          Option.some.inj placement_mem
        have chosen_mem := exists_placement.choose_spec.1
        have chosen_offset := exists_placement.choose_spec.2
        have placement_eq : placement = exists_placement.choose :=
          Placement.ext (Subsingleton.elim _ _) symmetry_eq.symm chosen_offset.symm
        rw [placement_eq]
        exact chosen_mem
      · intro placement_mem
        change assignment placement.offset = some placement.symmetry
        have exists_placement :
            ∃ candidate ∈ selected, candidate.offset = placement.offset :=
          ⟨placement, placement_mem, rfl⟩
        simp only [assignment, dif_pos exists_placement]
        have chosen_eq : exists_placement.choose = placement :=
          placement_eq_of_offset_eq tromino tiling
            exists_placement.choose_spec.1 placement_mem exists_placement.choose_spec.2
        rw [chosen_eq]
    simpa only [IsTiling, placements_eq] using tiling

end TrominoAssignment

end LeanTrominoes

end
