import LeanTrominoes.Tiling

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

/-- The set of placements selected by an assignment. -/
def placements (assignment : TrominoAssignment) : Set (Placement Unit) :=
  { placement | assignment placement.offset = some placement.symmetry }

/-- An assignment tiles a region when its selected placements do. -/
def IsTiling (tromino : Tromino) (region : Set Cell)
    (assignment : TrominoAssignment) : Prop :=
  LeanTrominoes.IsTiling (fun _ : Unit => tromino.cells) region assignment.placements

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
