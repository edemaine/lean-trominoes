/-
Copyright (c) 2026 lean-trominoes contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Erik Demaine, Stefan Langerman, GPT 5.6
-/
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

local instance stateTopologicalSpace : TopologicalSpace (Option SquareSymmetry) := ⊥
local instance stateDiscreteTopology : DiscreteTopology (Option SquareSymmetry) :=
  discreteTopology_bot _
local instance stateCompactSpace : CompactSpace (Option SquareSymmetry) :=
  Finite.compactSpace

/-- The finite vector of assignment states inspected to decide whether a cell
has exactly one covering placement. -/
abbrev CandidateStateVector (tromino : Tromino) (cell : Cell) :=
  (placement : ↑(coveringPlacements tromino cell)) → Option SquareSymmetry

/-- Restrict a global assignment to the offsets of placements that can cover
one cell. -/
def candidateObservation (tromino : Tromino) (cell : Cell)
    (assignment : TrominoAssignment) : CandidateStateVector tromino cell :=
  fun placement => assignment placement.val.offset

theorem continuous_candidateObservation (tromino : Tromino) (cell : Cell) :
    Continuous (candidateObservation tromino cell) := by
  apply continuous_pi
  intro placement
  exact continuous_apply placement.val.offset

/-- Number of active candidates, computed from a finite state vector. -/
def activeCandidateCount (tromino : Tromino) (cell : Cell)
    (states : CandidateStateVector tromino cell) : Nat :=
  ((coveringPlacements tromino cell).attach.filter fun placement =>
    states placement = some placement.val.symmetry).card

theorem activeCandidateCount_observation (tromino : Tromino) (cell : Cell)
    (assignment : TrominoAssignment) :
    activeCandidateCount tromino cell
        (candidateObservation tromino cell assignment) =
      ((coveringPlacements tromino cell).filter fun placement =>
        assignment placement.offset = some placement.symmetry).card := by
  have attached := Finset.filter_attach
    (fun placement : Placement Unit =>
      assignment placement.offset = some placement.symmetry)
    (coveringPlacements tromino cell)
  have same_card := congrArg Finset.card attached
  simpa only [activeCandidateCount, candidateObservation, Finset.card_map,
    Finset.card_attach] using same_card

/-- Having exactly one active candidate at a fixed cell is a closed cylinder
condition on global assignments. -/
theorem isClosed_uniqueCoverAt (tromino : Tromino) (cell : Cell) :
    IsClosed { assignment : TrominoAssignment |
      ((coveringPlacements tromino cell).filter fun placement =>
        assignment placement.offset = some placement.symmetry).card = 1 } := by
  have states_closed : IsClosed { states : CandidateStateVector tromino cell |
      activeCandidateCount tromino cell states = 1 } :=
    isClosed_discrete _
  have preimage_closed :=
    states_closed.preimage (continuous_candidateObservation tromino cell)
  convert preimage_closed using 1
  ext assignment
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [activeCandidateCount_observation]

/-- Local tiling constraints whose tile offsets and covered target cells are
drawn from the centered box of radius `radius`. -/
def IsValidInBox (tromino : Tromino) (region : Set Cell) (radius : Nat)
    (assignment : TrominoAssignment) : Prop :=
  (∀ offset, LeanWang.InBox radius offset →
      ∀ symmetry, ∀ cell ∈ (Placement.mk () symmetry offset).cells
            (fun _ : Unit => tromino.cells),
          assignment offset = some symmetry → cell ∈ region) ∧
    ∀ cell, LeanWang.InBox radius cell → cell ∈ region →
      ((coveringPlacements tromino cell).filter fun placement =>
        assignment placement.offset = some placement.symmetry).card = 1

/-- The closed cylinder of global assignments satisfying the constraints in a
centered finite box. -/
def BoxCylinder (tromino : Tromino) (region : Set Cell) (radius : Nat) :
    Set TrominoAssignment :=
  { assignment | assignment.IsValidInBox tromino region radius }

theorem isClosed_boxCylinder (tromino : Tromino) (region : Set Cell)
    (radius : Nat) : IsClosed (BoxCylinder tromino region radius) := by
  unfold BoxCylinder IsValidInBox
  rw [Set.setOf_and]
  apply IsClosed.inter
  · convert (isClosed_iInter fun offset =>
      isClosed_iInter fun (_ : LeanWang.InBox radius offset) =>
        isClosed_iInter fun symmetry =>
          isClosed_iInter fun cell =>
            isClosed_iInter fun
                (_ : cell ∈ (Placement.mk () symmetry offset).cells
                  (fun _ : Unit => tromino.cells)) => by
              have state_closed : IsClosed
                  { state : Option SquareSymmetry |
                    state = some symmetry → cell ∈ region } :=
                isClosed_discrete _
              exact state_closed.preimage (continuous_apply offset)) using 1
    ext assignment
    simp
  · convert (isClosed_iInter fun cell =>
      isClosed_iInter fun (_ : LeanWang.InBox radius cell) =>
        isClosed_iInter fun (_ : cell ∈ region) =>
          isClosed_uniqueCoverAt tromino cell) using 1
    ext assignment
    simp

/-- Box validity is monotone under restricting to a smaller centered box. -/
theorem isValidInBox_mono (tromino : Tromino) (region : Set Cell)
    {small large : Nat} (radius_le : small ≤ large)
    {assignment : TrominoAssignment}
    (valid : assignment.IsValidInBox tromino region large) :
    assignment.IsValidInBox tromino region small := by
  constructor
  · intro offset in_small symmetry cell cell_mem selected
    exact valid.1 offset (LeanWang.inBox_mono radius_le in_small)
      symmetry cell cell_mem selected
  · intro cell in_small cell_mem
    exact valid.2 cell (LeanWang.inBox_mono radius_le in_small) cell_mem

theorem boxCylinder_succ_subset (tromino : Tromino) (region : Set Cell)
    (radius : Nat) :
    BoxCylinder tromino region (radius + 1) ⊆
      BoxCylinder tromino region radius := by
  intro assignment valid
  exact isValidInBox_mono tromino region (Nat.le_succ radius) valid

/-- Global local validity is equivalent to validity in every finite centered
box. -/
theorem isLocallyValid_iff_forall_isValidInBox (tromino : Tromino)
    (region : Set Cell) (assignment : TrominoAssignment) :
    assignment.IsLocallyValid tromino region ↔
      ∀ radius : Nat, assignment.IsValidInBox tromino region radius := by
  constructor
  · intro valid radius
    constructor
    · intro offset _ symmetry cell cell_mem selected
      exact valid.1 offset symmetry selected cell cell_mem
    · intro cell _ cell_mem
      exact valid.2 cell cell_mem
  · intro valid
    constructor
    · intro offset symmetry selected cell cell_mem
      let radius := max offset.1.natAbs offset.2.natAbs
      have offset_in : LeanWang.InBox radius offset :=
        LeanWang.inBox_of_natAbs_le (Nat.le_max_left _ _) (Nat.le_max_right _ _)
      exact (valid radius).1 offset offset_in symmetry cell cell_mem selected
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

/-- If every finite centered box has some satisfying assignment, compactness
produces one assignment satisfying all local constraints globally. -/
theorem exists_isLocallyValid_of_forall_exists_isValidInBox (tromino : Tromino)
    (region : Set Cell)
    (finite : ∀ radius : Nat,
      ∃ assignment : TrominoAssignment,
        assignment.IsValidInBox tromino region radius) :
    ∃ assignment : TrominoAssignment,
      assignment.IsLocallyValid tromino region := by
  have cylinders_nonempty : ∀ radius : Nat,
      (BoxCylinder tromino region radius).Nonempty := finite
  have cylinders_closed : ∀ radius : Nat,
      IsClosed (BoxCylinder tromino region radius) :=
    isClosed_boxCylinder tromino region
  have cylinder_zero_compact : IsCompact (BoxCylinder tromino region 0) :=
    (cylinders_closed 0).isCompact
  obtain ⟨assignment, assignment_mem⟩ :=
    IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed
      (BoxCylinder tromino region)
      (boxCylinder_succ_subset tromino region)
      cylinders_nonempty cylinder_zero_compact cylinders_closed
  refine ⟨assignment,
    (isLocallyValid_iff_forall_isValidInBox tromino region assignment).mpr ?_⟩
  intro radius
  have assignment_mem_all :
      ∀ index : Nat, assignment ∈ BoxCylinder tromino region index := by
    simpa using assignment_mem
  exact assignment_mem_all radius

/-- Tromino tileability is equivalent to satisfiability of every finite-box
constraint system. -/
theorem tileable_iff_forall_exists_isValidInBox (tromino : Tromino)
    (region : Set Cell) :
    tromino.Tileable region ↔
      ∀ radius : Nat,
        ∃ assignment : TrominoAssignment,
          assignment.IsValidInBox tromino region radius := by
  constructor
  · intro tileable
    apply exists_isValidInBox_of_exists_isTiling tromino region
    exact (exists_assignment_iff_tileable tromino region).mpr tileable
  · intro finite
    obtain ⟨assignment, locally_valid⟩ :=
      exists_isLocallyValid_of_forall_exists_isValidInBox tromino region finite
    apply (exists_assignment_iff_tileable tromino region).mp
    exact ⟨assignment,
      (isLocallyValid_iff_isTiling tromino region assignment).mp locally_valid⟩

end TrominoAssignment
end LeanTrominoes
