import LeanTrominoes.Assignment
import LeanWang.Compactness

/-!
# Finite-box compactness for tromino tilings

Global local validity is approximated by constraints whose distinguished
offsets and target cells lie in a centered finite box. The constraints may
inspect the constant-radius neighborhood needed by a tromino placement.
-/

namespace LeanTrominoes
namespace TrominoAssignment

/-- Local tiling constraints whose tile offsets and covered target cells are
drawn from the centered box of radius `radius`. -/
def IsValidInBox (tromino : Tromino) (region : Set Cell) (radius : Nat)
    (assignment : TrominoAssignment) : Prop :=
  (∀ offset, LeanWang.InBox radius offset →
      ∀ symmetry, assignment offset = some symmetry →
        ∀ cell ∈ (Placement.mk () symmetry offset).cells
            (fun _ : Unit => tromino.cells),
          cell ∈ region) ∧
    ∀ cell, LeanWang.InBox radius cell → cell ∈ region →
      ((coveringPlacements tromino cell).filter fun placement =>
        assignment placement.offset = some placement.symmetry).card = 1

/-- Box validity is monotone under restricting to a smaller centered box. -/
theorem isValidInBox_mono (tromino : Tromino) (region : Set Cell)
    {small large : Nat} (radius_le : small ≤ large)
    {assignment : TrominoAssignment}
    (valid : assignment.IsValidInBox tromino region large) :
    assignment.IsValidInBox tromino region small := by
  constructor
  · intro offset in_small symmetry selected cell cell_mem
    exact valid.1 offset (LeanWang.inBox_mono radius_le in_small)
      symmetry selected cell cell_mem
  · intro cell in_small cell_mem
    exact valid.2 cell (LeanWang.inBox_mono radius_le in_small) cell_mem

/-- Global local validity is equivalent to validity in every finite centered
box. -/
theorem isLocallyValid_iff_forall_isValidInBox (tromino : Tromino)
    (region : Set Cell) (assignment : TrominoAssignment) :
    assignment.IsLocallyValid tromino region ↔
      ∀ radius : Nat, assignment.IsValidInBox tromino region radius := by
  constructor
  · intro valid radius
    constructor
    · intro offset _ symmetry selected cell cell_mem
      exact valid.1 offset symmetry selected cell cell_mem
    · intro cell _ cell_mem
      exact valid.2 cell cell_mem
  · intro valid
    constructor
    · intro offset symmetry selected cell cell_mem
      let radius := max offset.1.natAbs offset.2.natAbs
      have offset_in : LeanWang.InBox radius offset :=
        LeanWang.inBox_of_natAbs_le (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      exact (valid radius).1 offset offset_in symmetry selected cell cell_mem
    · intro cell cell_mem
      let radius := max cell.1.natAbs cell.2.natAbs
      have cell_in : LeanWang.InBox radius cell :=
        LeanWang.inBox_of_natAbs_le (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      exact (valid radius).2 cell cell_in cell_mem

/-- A global tiling assignment supplies a valid assignment in every finite
box. -/
theorem exists_isValidInBox_of_exists_isTiling (tromino : Tromino)
    (region : Set Cell)
    (tiling : ∃ assignment : TrominoAssignment, assignment.IsTiling tromino region) :
    ∀ radius : Nat,
      ∃ assignment : TrominoAssignment,
        assignment.IsValidInBox tromino region radius := by
  obtain ⟨assignment, assignment_tiling⟩ := tiling
  have locally_valid :=
    (isLocallyValid_iff_isTiling tromino region assignment).mpr assignment_tiling
  intro radius
  exact ⟨assignment,
    (isLocallyValid_iff_forall_isValidInBox tromino region assignment).mp
      locally_valid radius⟩

end TrominoAssignment
end LeanTrominoes
